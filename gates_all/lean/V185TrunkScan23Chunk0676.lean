import V185TrunkScan23Chunk0675

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3997425 : List Nat := [1, 2, 2, 2, 2, 3, 1, 5, 5]
def baseStart_3997425 : Nat := 118140960795 + 3997425 * 2 ^ 59
def prefixEnd_3997425 : Nat := 4983230072969 + 3 ^ 40 * 3997425 * 2
def baseEnd_3997425 : Nat := 228066711699903087778187

theorem tailTrace_3997425 : CollatzResearch.WordTrace tailWord_3997425 prefixEnd_3997425 228066711699903087778187 := by
  unfold tailWord_3997425
  simp only [CollatzResearch.WordTrace]
  refine ⟨145798067543019405682121729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97198711695346270454747819 145798067543019405682121729)
  ·
    refine ⟨109348550657264554261591297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145798067543019405682121729 109348550657264554261591297)
    ·
      refine ⟨82011412992948415696193473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109348550657264554261591297 82011412992948415696193473)
      ·
        refine ⟨61508559744711311772145105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82011412992948415696193473 61508559744711311772145105)
        ·
          refine ⟨46131419808533483829108829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61508559744711311772145105 46131419808533483829108829)
          ·
            refine ⟨17299282428200056435915811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46131419808533483829108829 17299282428200056435915811)
            ·
              refine ⟨25948923642300084653873717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299282428200056435915811 25948923642300084653873717)
              ·
                refine ⟨2432711591465632936300661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25948923642300084653873717 2432711591465632936300661)
                ·
                  refine ⟨228066711699903087778187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2432711591465632936300661 228066711699903087778187)
                  ·
                    rfl

theorem cell23_3997425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 5].length) (baseStart_3997425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997425 prefixEnd_3997425 := by exact prefixLift 3997425
  have htrace : WordTrace (prefixWord ++ tailWord_3997425) baseStart_3997425 baseEnd_3997425 := by
    simpa [prefixWord, tailWord_3997425, baseEnd_3997425] using wordTrace_append hprefix tailTrace_3997425
  have hstable : (prefixWord ++ tailWord_3997425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997425).length < 2 ^ (prefixWord ++ tailWord_3997425).sum := by decide
  have hdescent : baseEnd_3997425 < baseStart_3997425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997442 : List Nat := [3, 4, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3997442 : Nat := 118140960795 + 3997442 * 2 ^ 59
def prefixEnd_3997442 : Nat := 4983230072969 + 3 ^ 40 * 3997442 * 2
def baseEnd_3997442 : Nat := 228067681607806024832345

theorem tailTrace_3997442 : CollatzResearch.WordTrace tailWord_3997442 prefixEnd_3997442 228067681607806024832345 := by
  unfold tailWord_3997442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36449671895989454396372645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97199125055971878390327053 36449671895989454396372645)
  ·
    refine ⟨6834313480498022699319871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36449671895989454396372645 6834313480498022699319871)
    ·
      refine ⟨10251470220747034048979807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6834313480498022699319871 10251470220747034048979807)
      ·
        refine ⟨15377205331120551073469711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10251470220747034048979807 15377205331120551073469711)
        ·
          refine ⟨23065807996680826610204567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15377205331120551073469711 23065807996680826610204567)
          ·
            refine ⟨34598711995021239915306851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23065807996680826610204567 34598711995021239915306851)
            ·
              refine ⟨51898067992531859872960277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34598711995021239915306851 51898067992531859872960277)
              ·
                refine ⟨2432721937149930931545013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51898067992531859872960277 2432721937149930931545013)
                ·
                  refine ⟨228067681607806024832345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2432721937149930931545013 228067681607806024832345)
                  ·
                    rfl

theorem cell23_3997442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3997442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997442 prefixEnd_3997442 := by exact prefixLift 3997442
  have htrace : WordTrace (prefixWord ++ tailWord_3997442) baseStart_3997442 baseEnd_3997442 := by
    simpa [prefixWord, tailWord_3997442, baseEnd_3997442] using wordTrace_append hprefix tailTrace_3997442
  have hstable : (prefixWord ++ tailWord_3997442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997442).length < 2 ^ (prefixWord ++ tailWord_3997442).sum := by decide
  have hdescent : baseEnd_3997442 < baseStart_3997442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997448 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3997448 : Nat := 118140960795 + 3997448 * 2 ^ 59
def prefixEnd_3997448 : Nat := 4983230072969 + 3 ^ 40 * 3997448 * 2
def baseEnd_3997448 : Nat := 2052612215354181200016077

theorem tailTrace_3997448 : CollatzResearch.WordTrace tailWord_3997448 prefixEnd_3997448 2052612215354181200016077 := by
  unfold tailWord_3997448
  simp only [CollatzResearch.WordTrace]
  refine ⟨72899453210968040305104499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97199270947957387073472665 72899453210968040305104499)
  ·
    refine ⟨109349179816452060457656749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72899453210968040305104499 109349179816452060457656749)
    ·
      refine ⟨41005942431169522671621281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109349179816452060457656749 41005942431169522671621281)
      ·
        refine ⟨30754456823377142003715961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41005942431169522671621281 30754456823377142003715961)
        ·
          refine ⟨23065842617532856502786971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30754456823377142003715961 23065842617532856502786971)
          ·
            refine ⟨34598763926299284754180457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23065842617532856502786971 34598763926299284754180457)
            ·
              refine ⟨25949072944724463565635343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34598763926299284754180457 25949072944724463565635343)
              ·
                refine ⟨38923609417086695348453015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25949072944724463565635343 38923609417086695348453015)
                ·
                  refine ⟨58385414125630043022679523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38923609417086695348453015 58385414125630043022679523)
                  ·
                    refine ⟨87578121188445064534019285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58385414125630043022679523 87578121188445064534019285)
                    ·
                      refine ⟨2052612215354181200016077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87578121188445064534019285 2052612215354181200016077)
                      ·
                        rfl

theorem cell23_3997448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3997448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997448 prefixEnd_3997448 := by exact prefixLift 3997448
  have htrace : WordTrace (prefixWord ++ tailWord_3997448) baseStart_3997448 baseEnd_3997448 := by
    simpa [prefixWord, tailWord_3997448, baseEnd_3997448] using wordTrace_append hprefix tailTrace_3997448
  have hstable : (prefixWord ++ tailWord_3997448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997448).length < 2 ^ (prefixWord ++ tailWord_3997448).sum := by decide
  have hdescent : baseEnd_3997448 < baseStart_3997448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997468 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_3997468 : Nat := 118140960795 + 3997468 * 2 ^ 59
def prefixEnd_3997468 : Nat := 4983230072969 + 3 ^ 40 * 3997468 * 2
def baseEnd_3997468 : Nat := 684207494989090373921995

theorem tailTrace_3997468 : CollatzResearch.WordTrace tailWord_3997468 prefixEnd_3997468 684207494989090373921995 := by
  unfold tailWord_3997468
  simp only [CollatzResearch.WordTrace]
  refine ⟨72899817940931812012968529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97199757254575749350624705 72899817940931812012968529)
  ·
    refine ⟨54674863455698859009726397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72899817940931812012968529 54674863455698859009726397)
    ·
      refine ⟨20503073795887072128647399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54674863455698859009726397 20503073795887072128647399)
      ·
        refine ⟨30754610693830608192971099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20503073795887072128647399 30754610693830608192971099)
        ·
          refine ⟨46131916040745912289456649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30754610693830608192971099 46131916040745912289456649)
          ·
            refine ⟨34598937030559434217092487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46131916040745912289456649 34598937030559434217092487)
            ·
              refine ⟨51898405545839151325638731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34598937030559434217092487 51898405545839151325638731)
              ·
                refine ⟨77847608318758726988458097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51898405545839151325638731 77847608318758726988458097)
                ·
                  refine ⟨58385706239069045241343573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77847608318758726988458097 58385706239069045241343573)
                  ·
                    refine ⟨684207494989090373921995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58385706239069045241343573 684207494989090373921995)
                    ·
                      rfl

theorem cell23_3997468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_3997468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997468 prefixEnd_3997468 := by exact prefixLift 3997468
  have htrace : WordTrace (prefixWord ++ tailWord_3997468) baseStart_3997468 baseEnd_3997468 := by
    simpa [prefixWord, tailWord_3997468, baseEnd_3997468] using wordTrace_append hprefix tailTrace_3997468
  have hstable : (prefixWord ++ tailWord_3997468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997468).length < 2 ^ (prefixWord ++ tailWord_3997468).sum := by decide
  have hdescent : baseEnd_3997468 < baseStart_3997468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997475 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 1, 6, 2]
def baseStart_3997475 : Nat := 118140960795 + 3997475 * 2 ^ 59
def prefixEnd_3997475 : Nat := 4983230072969 + 3 ^ 40 * 3997475 * 2
def baseEnd_3997475 : Nat := 2052626079331852594378453

theorem tailTrace_3997475 : CollatzResearch.WordTrace tailWord_3997475 prefixEnd_3997475 2052626079331852594378453 := by
  unfold tailWord_3997475
  simp only [CollatzResearch.WordTrace]
  refine ⟨145799891192838264221441879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97199927461892176147627919 145799891192838264221441879)
  ·
    refine ⟨218699836789257396332162819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145799891192838264221441879 218699836789257396332162819)
    ·
      refine ⟨328049755183886094498244229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218699836789257396332162819 328049755183886094498244229)
      ·
        refine ⟨61509329096978642718420793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328049755183886094498244229 61509329096978642718420793)
        ·
          refine ⟨46131996822733982038815595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61509329096978642718420793 46131996822733982038815595)
          ·
            refine ⟨69197995234100973058223393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46131996822733982038815595 69197995234100973058223393)
            ·
              refine ⟨51898496425575729793667545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69197995234100973058223393 51898496425575729793667545)
              ·
                refine ⟨38923872319181797345250659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51898496425575729793667545 38923872319181797345250659)
                ·
                  refine ⟨58385808478772696017875989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38923872319181797345250659 58385808478772696017875989)
                  ·
                    refine ⟨2736834772442470125837937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58385808478772696017875989 2736834772442470125837937)
                    ·
                      refine ⟨2052626079331852594378453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736834772442470125837937 2052626079331852594378453)
                      ·
                        rfl

theorem cell23_3997475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_3997475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997475 prefixEnd_3997475 := by exact prefixLift 3997475
  have htrace : WordTrace (prefixWord ++ tailWord_3997475) baseStart_3997475 baseEnd_3997475 := by
    simpa [prefixWord, tailWord_3997475, baseEnd_3997475] using wordTrace_append hprefix tailTrace_3997475
  have hstable : (prefixWord ++ tailWord_3997475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997475).length < 2 ^ (prefixWord ++ tailWord_3997475).sum := by decide
  have hdescent : baseEnd_3997475 < baseStart_3997475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997492 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3997492 : Nat := 118140960795 + 3997492 * 2 ^ 59
def prefixEnd_3997492 : Nat := 4983230072969 + 3 ^ 40 * 3997492 * 2
def baseEnd_3997492 : Nat := 2052634808502979027865875

theorem tailTrace_3997492 : CollatzResearch.WordTrace tailWord_3997492 prefixEnd_3997492 2052634808502979027865875 := by
  unfold tailWord_3997492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72900255616888338062405365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97200340822517784083207153 72900255616888338062405365)
  ·
    refine ⟨6834398964083281693350503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72900255616888338062405365 6834398964083281693350503)
    ·
      refine ⟨10251598446124922540025755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6834398964083281693350503 10251598446124922540025755)
      ·
        refine ⟨15377397669187383810038633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10251598446124922540025755 15377397669187383810038633)
        ·
          refine ⟨11533048251890537857528975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15377397669187383810038633 11533048251890537857528975)
          ·
            refine ⟨17299572377835806786293463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11533048251890537857528975 17299572377835806786293463)
            ·
              refine ⟨25949358566753710179440195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299572377835806786293463 25949358566753710179440195)
              ·
                refine ⟨38924037850130565269160293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25949358566753710179440195 38924037850130565269160293)
                ·
                  refine ⟨7298257096899480987967555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38924037850130565269160293 7298257096899480987967555)
                  ·
                    refine ⟨10947385645349221481951333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298257096899480987967555 10947385645349221481951333)
                    ·
                      refine ⟨2052634808502979027865875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10947385645349221481951333 2052634808502979027865875)
                      ·
                        rfl

theorem cell23_3997492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3997492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997492 prefixEnd_3997492 := by exact prefixLift 3997492
  have htrace : WordTrace (prefixWord ++ tailWord_3997492) baseStart_3997492 baseEnd_3997492 := by
    simpa [prefixWord, tailWord_3997492, baseEnd_3997492] using wordTrace_append hprefix tailTrace_3997492
  have hstable : (prefixWord ++ tailWord_3997492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997492).length < 2 ^ (prefixWord ++ tailWord_3997492).sum := by decide
  have hdescent : baseEnd_3997492 < baseStart_3997492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997545 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 1, 5]
def baseStart_3997545 : Nat := 118140960795 + 3997545 * 2 ^ 59
def prefixEnd_3997545 : Nat := 4983230072969 + 3 ^ 40 * 3997545 * 2
def baseEnd_3997545 : Nat := 684220674325889106834377

theorem tailTrace_3997545 : CollatzResearch.WordTrace tailWord_3997545 prefixEnd_3997545 684220674325889106834377 := by
  unfold tailWord_3997545
  simp only [CollatzResearch.WordTrace]
  refine ⟨145802444302584666176490089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97201629535056444117660059 145802444302584666176490089)
  ·
    refine ⟨109351833226938499632367567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145802444302584666176490089 109351833226938499632367567)
    ·
      refine ⟨164027749840407749448551351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109351833226938499632367567 164027749840407749448551351)
      ·
        refine ⟨246041624760611624172827027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164027749840407749448551351 246041624760611624172827027)
        ·
          refine ⟨369062437140917436259240541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246041624760611624172827027 369062437140917436259240541)
          ·
            refine ⟨138398413927844038597215203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369062437140917436259240541 138398413927844038597215203)
            ·
              refine ⟨207597620891766057895822805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138398413927844038597215203 207597620891766057895822805)
              ·
                refine ⟨4865569239650766981933347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207597620891766057895822805 4865569239650766981933347)
                ·
                  refine ⟨7298353859476150472900021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865569239650766981933347 7298353859476150472900021)
                  ·
                    refine ⟨684220674325889106834377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7298353859476150472900021 684220674325889106834377)
                    ·
                      rfl

theorem cell23_3997545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_3997545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997545 prefixEnd_3997545 := by exact prefixLift 3997545
  have htrace : WordTrace (prefixWord ++ tailWord_3997545) baseStart_3997545 baseEnd_3997545 := by
    simpa [prefixWord, tailWord_3997545, baseEnd_3997545] using wordTrace_append hprefix tailTrace_3997545
  have hstable : (prefixWord ++ tailWord_3997545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997545).length < 2 ^ (prefixWord ++ tailWord_3997545).sum := by decide
  have hdescent : baseEnd_3997545 < baseStart_3997545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997586 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3997586 : Nat := 118140960795 + 3997586 * 2 ^ 59
def prefixEnd_3997586 : Nat := 4983230072969 + 3 ^ 40 * 3997586 * 2
def baseEnd_3997586 : Nat := 2052683075684501660090443

theorem tailTrace_3997586 : CollatzResearch.WordTrace tailWord_3997586 prefixEnd_3997586 2052683075684501660090443 := by
  unfold tailWord_3997586
  simp only [CollatzResearch.WordTrace]
  refine ⟨36450984923859032544683153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97202626463624086785821741 36450984923859032544683153)
  ·
    refine ⟨27338238692894274408512365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36450984923859032544683153 27338238692894274408512365)
    ·
      refine ⟨10251839509835352903192137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27338238692894274408512365 10251839509835352903192137)
      ·
        refine ⟨7688879632376514677394103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10251839509835352903192137 7688879632376514677394103)
        ·
          refine ⟨11533319448564772016091155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688879632376514677394103 11533319448564772016091155)
          ·
            refine ⟨17299979172847158024136733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11533319448564772016091155 17299979172847158024136733)
            ·
              refine ⟨6487492189817684259051275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17299979172847158024136733 6487492189817684259051275)
              ·
                refine ⟨9731238284726526388576913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487492189817684259051275 9731238284726526388576913)
                ·
                  refine ⟨7298428713544894791432685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9731238284726526388576913 7298428713544894791432685)
                  ·
                    refine ⟨2736910767579335546787257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7298428713544894791432685 2736910767579335546787257)
                    ·
                      refine ⟨2052683075684501660090443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736910767579335546787257 2052683075684501660090443)
                      ·
                        rfl

theorem cell23_3997586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3997586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997586 prefixEnd_3997586 := by exact prefixLift 3997586
  have htrace : WordTrace (prefixWord ++ tailWord_3997586) baseStart_3997586 baseEnd_3997586 := by
    simpa [prefixWord, tailWord_3997586, baseEnd_3997586] using wordTrace_append hprefix tailTrace_3997586
  have hstable : (prefixWord ++ tailWord_3997586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997586).length < 2 ^ (prefixWord ++ tailWord_3997586).sum := by decide
  have hdescent : baseEnd_3997586 < baseStart_3997586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997596 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_3997596 : Nat := 118140960795 + 3997596 * 2 ^ 59
def prefixEnd_3997596 : Nat := 4983230072969 + 3 ^ 40 * 3997596 * 2
def baseEnd_3997596 : Nat := 684229403497015540321799

theorem tailTrace_3997596 : CollatzResearch.WordTrace tailWord_3997596 prefixEnd_3997596 684229403497015540321799 := by
  unfold tailWord_3997596
  simp only [CollatzResearch.WordTrace]
  refine ⟨72902152212699950943298321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97202869616933267924397761 72902152212699950943298321)
  ·
    refine ⟨54676614159524963207473741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72902152212699950943298321 54676614159524963207473741)
    ·
      refine ⟨20503730309821861202802653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54676614159524963207473741 20503730309821861202802653)
      ·
        refine ⟨7688898866183197951050995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20503730309821861202802653 7688898866183197951050995)
        ·
          refine ⟨11533348299274796926576493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688898866183197951050995 11533348299274796926576493)
          ·
            refine ⟨4325005612228048847466185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11533348299274796926576493 4325005612228048847466185)
            ·
              refine ⟨3243754209171036635599639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325005612228048847466185 3243754209171036635599639)
              ·
                refine ⟨4865631313756554953399459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243754209171036635599639 4865631313756554953399459)
                ·
                  refine ⟨7298446970634832430099189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865631313756554953399459 7298446970634832430099189)
                  ·
                    refine ⟨684229403497015540321799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7298446970634832430099189 684229403497015540321799)
                    ·
                      rfl

theorem cell23_3997596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_3997596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997596 prefixEnd_3997596 := by exact prefixLift 3997596
  have htrace : WordTrace (prefixWord ++ tailWord_3997596) baseStart_3997596 baseEnd_3997596 := by
    simpa [prefixWord, tailWord_3997596, baseEnd_3997596] using wordTrace_append hprefix tailTrace_3997596
  have hstable : (prefixWord ++ tailWord_3997596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997596).length < 2 ^ (prefixWord ++ tailWord_3997596).sum := by decide
  have hdescent : baseEnd_3997596 < baseStart_3997596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997599 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 4]
def baseStart_3997599 : Nat := 118140960795 + 3997599 * 2 ^ 59
def prefixEnd_3997599 : Nat := 4983230072969 + 3 ^ 40 * 3997599 * 2
def baseEnd_3997599 : Nat := 2052689750933010109227883

theorem tailTrace_3997599 : CollatzResearch.WordTrace tailWord_3997599 prefixEnd_3997599 2052689750933010109227883 := by
  unfold tailWord_3997599
  simp only [CollatzResearch.WordTrace]
  refine ⟨145804413844389033398955851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97202942562926022265970567 145804413844389033398955851)
  ·
    refine ⟨218706620766583550098433777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145804413844389033398955851 218706620766583550098433777)
    ·
      refine ⟨164029965574937662573825333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218706620766583550098433777 164029965574937662573825333)
      ·
        refine ⟨15377809272650405866296125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164029965574937662573825333 15377809272650405866296125)
        ·
          refine ⟨5766678477243902199861047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15377809272650405866296125 5766678477243902199861047)
          ·
            refine ⟨8650017715865853299791571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766678477243902199861047 8650017715865853299791571)
            ·
              refine ⟨12975026573798779949687357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650017715865853299791571 12975026573798779949687357)
              ·
                refine ⟨4865634965174542481132759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12975026573798779949687357 4865634965174542481132759)
                ·
                  refine ⟨7298452447761813721699139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865634965174542481132759 7298452447761813721699139)
                  ·
                    refine ⟨10947678671642720582548709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7298452447761813721699139 10947678671642720582548709)
                    ·
                      refine ⟨2052689750933010109227883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10947678671642720582548709 2052689750933010109227883)
                      ·
                        rfl

theorem cell23_3997599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_3997599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997599 prefixEnd_3997599 := by exact prefixLift 3997599
  have htrace : WordTrace (prefixWord ++ tailWord_3997599) baseStart_3997599 baseEnd_3997599 := by
    simpa [prefixWord, tailWord_3997599, baseEnd_3997599] using wordTrace_append hprefix tailTrace_3997599
  have hstable : (prefixWord ++ tailWord_3997599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997599).length < 2 ^ (prefixWord ++ tailWord_3997599).sum := by decide
  have hdescent : baseEnd_3997599 < baseStart_3997599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997629 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_3997629 : Nat := 118140960795 + 3997629 * 2 ^ 59
def prefixEnd_3997629 : Nat := 4983230072969 + 3 ^ 40 * 3997629 * 2
def baseEnd_3997629 : Nat := 2052705155352644991852745

theorem tailTrace_3997629 : CollatzResearch.WordTrace tailWord_3997629 prefixEnd_3997629 2052705155352644991852745 := by
  unfold tailWord_3997629
  simp only [CollatzResearch.WordTrace]
  refine ⟨145805508034280348522547941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97203672022853565681698627 145805508034280348522547941)
  ·
    refine ⟨27338532756427565347977739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145805508034280348522547941 27338532756427565347977739)
    ·
      refine ⟨41007799134641348021966609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27338532756427565347977739 41007799134641348021966609)
      ·
        refine ⟨30755849350981011016474957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41007799134641348021966609 30755849350981011016474957)
        ·
          refine ⟨11533443506617879131178109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30755849350981011016474957 11533443506617879131178109)
          ·
            refine ⟨4325041314981704674191791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11533443506617879131178109 4325041314981704674191791)
            ·
              refine ⟨6487561972472557011287687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4325041314981704674191791 6487561972472557011287687)
              ·
                refine ⟨9731342958708835516931531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487561972472557011287687 9731342958708835516931531)
                ·
                  refine ⟨14597014438063253275397297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9731342958708835516931531 14597014438063253275397297)
                  ·
                    refine ⟨10947760828547439956547973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14597014438063253275397297 10947760828547439956547973)
                    ·
                      refine ⟨2052705155352644991852745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10947760828547439956547973 2052705155352644991852745)
                      ·
                        rfl

theorem cell23_3997629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_3997629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997629 prefixEnd_3997629 := by exact prefixLift 3997629
  have htrace : WordTrace (prefixWord ++ tailWord_3997629) baseStart_3997629 baseEnd_3997629 := by
    simpa [prefixWord, tailWord_3997629, baseEnd_3997629] using wordTrace_append hprefix tailTrace_3997629
  have hstable : (prefixWord ++ tailWord_3997629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997629).length < 2 ^ (prefixWord ++ tailWord_3997629).sum := by decide
  have hdescent : baseEnd_3997629 < baseStart_3997629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997665 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3997665 : Nat := 118140960795 + 3997665 * 2 ^ 59
def prefixEnd_3997665 : Nat := 4983230072969 + 3 ^ 40 * 3997665 * 2
def baseEnd_3997665 : Nat := 684241213552068950334193

theorem tailTrace_3997665 : CollatzResearch.WordTrace tailWord_3997665 prefixEnd_3997665 684241213552068950334193 := by
  unfold tailWord_3997665
  simp only [CollatzResearch.WordTrace]
  refine ⟨145806821062149926670858449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97204547374766617780572299 145806821062149926670858449)
  ·
    refine ⟨109355115796612445003143837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145806821062149926670858449 109355115796612445003143837)
    ·
      refine ⟨41008168423729666876178939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109355115796612445003143837 41008168423729666876178939)
      ·
        refine ⟨61512252635594500314268409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41008168423729666876178939 61512252635594500314268409)
        ·
          refine ⟨46134189476695875235701307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61512252635594500314268409 46134189476695875235701307)
          ·
            refine ⟨69201284215043812853551961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46134189476695875235701307 69201284215043812853551961)
            ·
              refine ⟨51900963161282859640163971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69201284215043812853551961 51900963161282859640163971)
              ·
                refine ⟨77851444741924289460245957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51900963161282859640163971 77851444741924289460245957)
                ·
                  refine ⟨14597145889110804273796117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77851444741924289460245957 14597145889110804273796117)
                  ·
                    refine ⟨684241213552068950334193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14597145889110804273796117 684241213552068950334193)
                    ·
                      rfl

theorem cell23_3997665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3997665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997665 prefixEnd_3997665 := by exact prefixLift 3997665
  have htrace : WordTrace (prefixWord ++ tailWord_3997665) baseStart_3997665 baseEnd_3997665 := by
    simpa [prefixWord, tailWord_3997665, baseEnd_3997665] using wordTrace_append hprefix tailTrace_3997665
  have hstable : (prefixWord ++ tailWord_3997665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997665).length < 2 ^ (prefixWord ++ tailWord_3997665).sum := by decide
  have hdescent : baseEnd_3997665 < baseStart_3997665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997695 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 7]
def baseStart_3997695 : Nat := 118140960795 + 3997695 * 2 ^ 59
def prefixEnd_3997695 : Nat := 4983230072969 + 3 ^ 40 * 3997695 * 2
def baseEnd_3997695 : Nat := 228082116119537970403049

theorem tailTrace_3997695 : CollatzResearch.WordTrace tailWord_3997695 prefixEnd_3997695 228082116119537970403049 := by
  unfold tailWord_3997695
  simp only [CollatzResearch.WordTrace]
  refine ⟨145807915252041241794450539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97205276834694161196300359 145807915252041241794450539)
  ·
    refine ⟨218711872878061862691675809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145807915252041241794450539 218711872878061862691675809)
    ·
      refine ⟨164033904658546397018756857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218711872878061862691675809 164033904658546397018756857)
      ·
        refine ⟨123025428493909797764067643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164033904658546397018756857 123025428493909797764067643)
        ·
          refine ⟨184538142740864696646101465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123025428493909797764067643 184538142740864696646101465)
          ·
            refine ⟨138403607055648522484576099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184538142740864696646101465 138403607055648522484576099)
            ·
              refine ⟨207605410583472783726864149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138403607055648522484576099 207605410583472783726864149)
              ·
                refine ⟨9731503621100286737196757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207605410583472783726864149 9731503621100286737196757)
                ·
                  refine ⟨228082116119537970403049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9731503621100286737196757 228082116119537970403049)
                  ·
                    rfl

theorem cell23_3997695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 7].length) (baseStart_3997695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997695 prefixEnd_3997695 := by exact prefixLift 3997695
  have htrace : WordTrace (prefixWord ++ tailWord_3997695) baseStart_3997695 baseEnd_3997695 := by
    simpa [prefixWord, tailWord_3997695, baseEnd_3997695] using wordTrace_append hprefix tailTrace_3997695
  have hstable : (prefixWord ++ tailWord_3997695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997695).length < 2 ^ (prefixWord ++ tailWord_3997695).sum := by decide
  have hdescent : baseEnd_3997695 < baseStart_3997695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997706 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_3997706 : Nat := 118140960795 + 3997706 * 2 ^ 59
def prefixEnd_3997706 : Nat := 4983230072969 + 3 ^ 40 * 3997706 * 2
def baseEnd_3997706 : Nat := 2052744693363041190589891

theorem tailTrace_3997706 : CollatzResearch.WordTrace tailWord_3997706 prefixEnd_3997706 2052744693363041190589891 := by
  unfold tailWord_3997706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36452079113750347668275243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97205544303334260448733981 36452079113750347668275243)
  ·
    refine ⟨54678118670625521502412865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36452079113750347668275243 54678118670625521502412865)
    ·
      refine ⟨41008589002969141126809649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54678118670625521502412865 41008589002969141126809649)
      ·
        refine ⟨30756441752226855845107237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41008589002969141126809649 30756441752226855845107237)
        ·
          refine ⟨5766832828542535470957607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30756441752226855845107237 5766832828542535470957607)
          ·
            refine ⟨8650249242813803206436411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766832828542535470957607 8650249242813803206436411)
            ·
              refine ⟨12975373864220704809654617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650249242813803206436411 12975373864220704809654617)
              ·
                refine ⟨9731530398165528607240963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12975373864220704809654617 9731530398165528607240963)
                ·
                  refine ⟨14597295597248292910861445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9731530398165528607240963 14597295597248292910861445)
                  ·
                    refine ⟨2736992924484054920786521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14597295597248292910861445 2736992924484054920786521)
                    ·
                      refine ⟨2052744693363041190589891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736992924484054920786521 2052744693363041190589891)
                      ·
                        rfl

theorem cell23_3997706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_3997706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997706 prefixEnd_3997706 := by exact prefixLift 3997706
  have htrace : WordTrace (prefixWord ++ tailWord_3997706) baseStart_3997706 baseEnd_3997706 := by
    simpa [prefixWord, tailWord_3997706, baseEnd_3997706] using wordTrace_append hprefix tailTrace_3997706
  have hstable : (prefixWord ++ tailWord_3997706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997706).length < 2 ^ (prefixWord ++ tailWord_3997706).sum := by decide
  have hdescent : baseEnd_3997706 < baseStart_3997706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997736 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3997736 : Nat := 118140960795 + 3997736 * 2 ^ 59
def prefixEnd_3997736 : Nat := 4983230072969 + 3 ^ 40 * 3997736 * 2
def baseEnd_3997736 : Nat := 2052760097782676073214753

theorem tailTrace_3997736 : CollatzResearch.WordTrace tailWord_3997736 prefixEnd_3997736 2052760097782676073214753 := by
  unfold tailWord_3997736
  simp only [CollatzResearch.WordTrace]
  refine ⟨72904705322446352898346531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97206273763261803864462041 72904705322446352898346531)
  ·
    refine ⟨109357057983669529347519797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72904705322446352898346531 109357057983669529347519797)
    ·
      refine ⟨10252224185969018376329981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109357057983669529347519797 10252224185969018376329981)
      ·
        refine ⟨3844584069738381891123743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10252224185969018376329981 3844584069738381891123743)
        ·
          refine ⟨5766876104607572836685615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844584069738381891123743 5766876104607572836685615)
          ·
            refine ⟨8650314156911359255028423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766876104607572836685615 8650314156911359255028423)
            ·
              refine ⟨12975471235367038882542635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650314156911359255028423 12975471235367038882542635)
              ·
                refine ⟨19463206853050558323813953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12975471235367038882542635 19463206853050558323813953)
                ·
                  refine ⟨14597405139787918742860465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19463206853050558323813953 14597405139787918742860465)
                  ·
                    refine ⟨10948053854840939057145349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14597405139787918742860465 10948053854840939057145349)
                    ·
                      refine ⟨2052760097782676073214753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10948053854840939057145349 2052760097782676073214753)
                      ·
                        rfl

theorem cell23_3997736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3997736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997736 prefixEnd_3997736 := by exact prefixLift 3997736
  have htrace : WordTrace (prefixWord ++ tailWord_3997736) baseStart_3997736 baseEnd_3997736 := by
    simpa [prefixWord, tailWord_3997736, baseEnd_3997736] using wordTrace_append hprefix tailTrace_3997736
  have hstable : (prefixWord ++ tailWord_3997736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997736).length < 2 ^ (prefixWord ++ tailWord_3997736).sum := by decide
  have hdescent : baseEnd_3997736 < baseStart_3997736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997755 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 2, 8]
def baseStart_3997755 : Nat := 118140960795 + 3997755 * 2 ^ 59
def prefixEnd_3997755 : Nat := 4983230072969 + 3 ^ 40 * 3997755 * 2
def baseEnd_3997755 : Nat := 684256617971703832959055

theorem tailTrace_3997755 : CollatzResearch.WordTrace tailWord_3997755 prefixEnd_3997755 684256617971703832959055 := by
  unfold tailWord_3997755
  simp only [CollatzResearch.WordTrace]
  refine ⟨145810103631823872041634719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97206735754549248027756479 145810103631823872041634719)
  ·
    refine ⟨218715155447735808062452079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145810103631823872041634719 218715155447735808062452079)
    ·
      refine ⟨328072733171603712093678119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218715155447735808062452079 328072733171603712093678119)
      ·
        refine ⟨492109099757405568140517179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328072733171603712093678119 492109099757405568140517179)
        ·
          refine ⟨738163649636108352210775769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492109099757405568140517179 738163649636108352210775769)
          ·
            refine ⟨553622737227081264158081827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738163649636108352210775769 553622737227081264158081827)
            ·
              refine ⟨830434105840621896237122741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553622737227081264158081827 830434105840621896237122741)
              ·
                refine ⟨77853197422558302772230257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830434105840621896237122741 77853197422558302772230257)
                ·
                  refine ⟨58389898066918727079172693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77853197422558302772230257 58389898066918727079172693)
                  ·
                    refine ⟨684256617971703832959055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58389898066918727079172693 684256617971703832959055)
                    ·
                      rfl

theorem cell23_3997755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_3997755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997755 prefixEnd_3997755 := by exact prefixLift 3997755
  have htrace : WordTrace (prefixWord ++ tailWord_3997755) baseStart_3997755 baseEnd_3997755 := by
    simpa [prefixWord, tailWord_3997755, baseEnd_3997755] using wordTrace_append hprefix tailTrace_3997755
  have hstable : (prefixWord ++ tailWord_3997755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997755).length < 2 ^ (prefixWord ++ tailWord_3997755).sum := by decide
  have hdescent : baseEnd_3997755 < baseStart_3997755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997879 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 1, 6]
def baseStart_3997879 : Nat := 118140960795 + 3997879 * 2 ^ 59
def prefixEnd_3997879 : Nat := 4983230072969 + 3 ^ 40 * 3997879 * 2
def baseEnd_3997879 : Nat := 684277841838756337908865

theorem tailTrace_3997879 : CollatzResearch.WordTrace tailWord_3997879 prefixEnd_3997879 684277841838756337908865 := by
  unfold tailWord_3997879
  simp only [CollatzResearch.WordTrace]
  refine ⟨145814626283374641219148691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97209750855583094146099127 145814626283374641219148691)
  ·
    refine ⟨218721939425061961828723037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145814626283374641219148691 218721939425061961828723037)
    ·
      refine ⟨82020727284398235685771139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218721939425061961828723037 82020727284398235685771139)
      ·
        refine ⟨123031090926597353528656709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82020727284398235685771139 123031090926597353528656709)
        ·
          refine ⟨23068329548737003786623133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123031090926597353528656709 23068329548737003786623133)
          ·
            refine ⟨8650623580776376419983675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23068329548737003786623133 8650623580776376419983675)
            ·
              refine ⟨12975935371164564629975513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650623580776376419983675 12975935371164564629975513)
              ·
                refine ⟨9731951528373423472481635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12975935371164564629975513 9731951528373423472481635)
                ·
                  refine ⟨14597927292560135208722453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9731951528373423472481635 14597927292560135208722453)
                  ·
                    refine ⟨684277841838756337908865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14597927292560135208722453 684277841838756337908865)
                    ·
                      rfl

theorem cell23_3997879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_3997879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997879 prefixEnd_3997879 := by exact prefixLift 3997879
  have htrace : WordTrace (prefixWord ++ tailWord_3997879) baseStart_3997879 baseEnd_3997879 := by
    simpa [prefixWord, tailWord_3997879, baseEnd_3997879] using wordTrace_append hprefix tailTrace_3997879
  have hstable : (prefixWord ++ tailWord_3997879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997879).length < 2 ^ (prefixWord ++ tailWord_3997879).sum := by decide
  have hdescent : baseEnd_3997879 < baseStart_3997879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997906 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3997906 : Nat := 118140960795 + 3997906 * 2 ^ 59
def prefixEnd_3997906 : Nat := 4983230072969 + 3 ^ 40 * 3997906 * 2
def baseEnd_3997906 : Nat := 2052847389493940408088971

theorem tailTrace_3997906 : CollatzResearch.WordTrace tailWord_3997906 prefixEnd_3997906 2052847389493940408088971 := by
  unfold tailWord_3997906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36453902763569206207595393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97210407369517883220254381 36453902763569206207595393)
  ·
    refine ⟨27340427072676904655696545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36453902763569206207595393 27340427072676904655696545)
    ·
      refine ⟨20505320304507678491772409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27340427072676904655696545 20505320304507678491772409)
      ·
        refine ⟨15378990228380758868829307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20505320304507678491772409 15378990228380758868829307)
        ·
          refine ⟨23068485342571138303243961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15378990228380758868829307 23068485342571138303243961)
          ·
            refine ⟨17301364006928353727432971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23068485342571138303243961 17301364006928353727432971)
            ·
              refine ⟨25952046010392530591149457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17301364006928353727432971 25952046010392530591149457)
              ·
                refine ⟨19464034507794397943362093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25952046010392530591149457 19464034507794397943362093)
                ·
                  refine ⟨7299012940422899228760785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19464034507794397943362093 7299012940422899228760785)
                  ·
                    refine ⟨5474259705317174421570589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7299012940422899228760785 5474259705317174421570589)
                    ·
                      refine ⟨2052847389493940408088971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5474259705317174421570589 2052847389493940408088971)
                      ·
                        rfl

theorem cell23_3997906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3997906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997906 prefixEnd_3997906 := by exact prefixLift 3997906
  have htrace : WordTrace (prefixWord ++ tailWord_3997906) baseStart_3997906 baseEnd_3997906 := by
    simpa [prefixWord, tailWord_3997906, baseEnd_3997906] using wordTrace_append hprefix tailTrace_3997906
  have hstable : (prefixWord ++ tailWord_3997906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997906).length < 2 ^ (prefixWord ++ tailWord_3997906).sum := by decide
  have hdescent : baseEnd_3997906 < baseStart_3997906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997969 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 2, 6]
def baseStart_3997969 : Nat := 118140960795 + 3997969 * 2 ^ 59
def prefixEnd_3997969 : Nat := 4983230072969 + 3 ^ 40 * 3997969 * 2
def baseEnd_3997969 : Nat := 684293246258391220533727

theorem tailTrace_3997969 : CollatzResearch.WordTrace tailWord_3997969 prefixEnd_3997969 684293246258391220533727 := by
  unfold tailWord_3997969
  simp only [CollatzResearch.WordTrace]
  refine ⟨145817908853048586589924961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97211939235365724393283307 145817908853048586589924961)
  ·
    refine ⟨109363431639786439942443721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145817908853048586589924961 109363431639786439942443721)
    ·
      refine ⟨82022573729839829956832791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109363431639786439942443721 82022573729839829956832791)
      ·
        refine ⟨123033860594759744935249187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82022573729839829956832791 123033860594759744935249187)
        ·
          refine ⟨184550790892139617402873781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123033860594759744935249187 184550790892139617402873781)
          ·
            refine ⟨17301636646138089131519417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184550790892139617402873781 17301636646138089131519417)
            ·
              refine ⟨12976227484603566848639563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17301636646138089131519417 12976227484603566848639563)
              ·
                refine ⟨19464341226905350272959345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12976227484603566848639563 19464341226905350272959345)
                ·
                  refine ⟨14598255920179012704719509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19464341226905350272959345 14598255920179012704719509)
                  ·
                    refine ⟨684293246258391220533727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14598255920179012704719509 684293246258391220533727)
                    ·
                      rfl

theorem cell23_3997969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_3997969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997969 prefixEnd_3997969 := by exact prefixLift 3997969
  have htrace : WordTrace (prefixWord ++ tailWord_3997969) baseStart_3997969 baseEnd_3997969 := by
    simpa [prefixWord, tailWord_3997969, baseEnd_3997969] using wordTrace_append hprefix tailTrace_3997969
  have hstable : (prefixWord ++ tailWord_3997969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997969).length < 2 ^ (prefixWord ++ tailWord_3997969).sum := by decide
  have hdescent : baseEnd_3997969 < baseStart_3997969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997979 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 3]
def baseStart_3997979 : Nat := 118140960795 + 3997979 * 2 ^ 59
def prefixEnd_3997979 : Nat := 4983230072969 + 3 ^ 40 * 3997979 * 2
def baseEnd_3997979 : Nat := 2052884873581718622476135

theorem tailTrace_3997979 : CollatzResearch.WordTrace tailWord_3997979 prefixEnd_3997979 2052884873581718622476135 := by
  unfold tailWord_3997979
  simp only [CollatzResearch.WordTrace]
  refine ⟨145818273583012358297788991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97212182388674905531859327 145818273583012358297788991)
  ·
    refine ⟨218727410374518537446683487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145818273583012358297788991 218727410374518537446683487)
    ·
      refine ⟨328091115561777806170025231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218727410374518537446683487 328091115561777806170025231)
      ·
        refine ⟨492136673342666709255037847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328091115561777806170025231 492136673342666709255037847)
        ·
          refine ⟨738205010014000063882556771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492136673342666709255037847 738205010014000063882556771)
          ·
            refine ⟨1107307515021000095823835157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738205010014000063882556771 1107307515021000095823835157)
            ·
              refine ⟨51905039766609379491742273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1107307515021000095823835157 51905039766609379491742273)
              ·
                refine ⟨38928779824957034618806705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51905039766609379491742273 38928779824957034618806705)
                ·
                  refine ⟨29196584868717775964105029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38928779824957034618806705 29196584868717775964105029)
                  ·
                    refine ⟨5474359662884582993269693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29196584868717775964105029 5474359662884582993269693)
                    ·
                      refine ⟨2052884873581718622476135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5474359662884582993269693 2052884873581718622476135)
                      ·
                        rfl

theorem cell23_3997979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 3].length) (baseStart_3997979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997979 prefixEnd_3997979 := by exact prefixLift 3997979
  have htrace : WordTrace (prefixWord ++ tailWord_3997979) baseStart_3997979 baseEnd_3997979 := by
    simpa [prefixWord, tailWord_3997979, baseEnd_3997979] using wordTrace_append hprefix tailTrace_3997979
  have hstable : (prefixWord ++ tailWord_3997979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997979).length < 2 ^ (prefixWord ++ tailWord_3997979).sum := by decide
  have hdescent : baseEnd_3997979 < baseStart_3997979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998039 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3998039 : Nat := 118140960795 + 3998039 * 2 ^ 59
def prefixEnd_3998039 : Nat := 4983230072969 + 3 ^ 40 * 3998039 * 2
def baseEnd_3998039 : Nat := 2052915682420988387725859

theorem tailTrace_3998039 : CollatzResearch.WordTrace tailWord_3998039 prefixEnd_3998039 2052915682420988387725859 := by
  unfold tailWord_3998039
  simp only [CollatzResearch.WordTrace]
  refine ⟨145820461962794988544973171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97213641308529992363315447 145820461962794988544973171)
  ·
    refine ⟨218730692944192482817459757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145820461962794988544973171 218730692944192482817459757)
    ·
      refine ⟨82024009854072181056547409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218730692944192482817459757 82024009854072181056547409)
      ·
        refine ⟨61518007390554135792410557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82024009854072181056547409 61518007390554135792410557)
        ·
          refine ⟨23069252771457800922153959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61518007390554135792410557 23069252771457800922153959)
          ·
            refine ⟨34603879157186701383230939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23069252771457800922153959 34603879157186701383230939)
            ·
              refine ⟨51905818735780052074846409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34603879157186701383230939 51905818735780052074846409)
              ·
                refine ⟨38929364051835039056134807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51905818735780052074846409 38929364051835039056134807)
                ·
                  refine ⟨58394046077752558584202211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38929364051835039056134807 58394046077752558584202211)
                  ·
                    refine ⟨87591069116628837876303317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58394046077752558584202211 87591069116628837876303317)
                    ·
                      refine ⟨2052915682420988387725859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87591069116628837876303317 2052915682420988387725859)
                      ·
                        rfl

theorem cell23_3998039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3998039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998039 prefixEnd_3998039 := by exact prefixLift 3998039
  have htrace : WordTrace (prefixWord ++ tailWord_3998039) baseStart_3998039 baseEnd_3998039 := by
    simpa [prefixWord, tailWord_3998039, baseEnd_3998039] using wordTrace_append hprefix tailTrace_3998039
  have hstable : (prefixWord ++ tailWord_3998039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998039).length < 2 ^ (prefixWord ++ tailWord_3998039).sum := by decide
  have hdescent : baseEnd_3998039 < baseStart_3998039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998056 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3998056 : Nat := 118140960795 + 3998056 * 2 ^ 59
def prefixEnd_3998056 : Nat := 4983230072969 + 3 ^ 40 * 3998056 * 2
def baseEnd_3998056 : Nat := 2052924411592114821213281

theorem tailTrace_3998056 : CollatzResearch.WordTrace tailWord_3998056 prefixEnd_3998056 2052924411592114821213281 := by
  unfold tailWord_3998056
  simp only [CollatzResearch.WordTrace]
  refine ⟨72910541001866700224171011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97214054669155600298894681 72910541001866700224171011)
  ·
    refine ⟨109365811502800050336256517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72910541001866700224171011 109365811502800050336256517)
    ·
      refine ⟨20506089656775009438048097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109365811502800050336256517 20506089656775009438048097)
      ·
        refine ⟨15379567242581257078536073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20506089656775009438048097 15379567242581257078536073)
        ·
          refine ⟨11534675431935942808902055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15379567242581257078536073 11534675431935942808902055)
          ·
            refine ⟨17302013147903914213353083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534675431935942808902055 17302013147903914213353083)
            ·
              refine ⟨25953019721855871320029625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17302013147903914213353083 25953019721855871320029625)
              ·
                refine ⟨19464764791391903490022219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25953019721855871320029625 19464764791391903490022219)
                ·
                  refine ⟨29197147187087855235033329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19464764791391903490022219 29197147187087855235033329)
                  ·
                    refine ⟨21897860390315891426274997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29197147187087855235033329 21897860390315891426274997)
                    ·
                      refine ⟨2052924411592114821213281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21897860390315891426274997 2052924411592114821213281)
                      ·
                        rfl

theorem cell23_3998056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3998056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998056 prefixEnd_3998056 := by exact prefixLift 3998056
  have htrace : WordTrace (prefixWord ++ tailWord_3998056) baseStart_3998056 baseEnd_3998056 := by
    simpa [prefixWord, tailWord_3998056, baseEnd_3998056] using wordTrace_append hprefix tailTrace_3998056
  have hstable : (prefixWord ++ tailWord_3998056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998056).length < 2 ^ (prefixWord ++ tailWord_3998056).sum := by decide
  have hdescent : baseEnd_3998056 < baseStart_3998056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998079 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_3998079 : Nat := 118140960795 + 3998079 * 2 ^ 59
def prefixEnd_3998079 : Nat := 4983230072969 + 3 ^ 40 * 3998079 * 2
def baseEnd_3998079 : Nat := 2052936221647168231225675

theorem tailTrace_3998079 : CollatzResearch.WordTrace tailWord_3998079 prefixEnd_3998079 2052936221647168231225675 := by
  unfold tailWord_3998079
  simp only [CollatzResearch.WordTrace]
  refine ⟨145821920882650075376429291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97214613921766716917619527 145821920882650075376429291)
  ·
    refine ⟨218732881323975113064643937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145821920882650075376429291 218732881323975113064643937)
    ·
      refine ⟨164049660992981334798482953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218732881323975113064643937 164049660992981334798482953)
      ·
        refine ⟨123037245744736001098862215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164049660992981334798482953 123037245744736001098862215)
        ·
          refine ⟨184555868617104001648293323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123037245744736001098862215 184555868617104001648293323)
          ·
            refine ⟨276833802925656002472439985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184555868617104001648293323 276833802925656002472439985)
            ·
              refine ⟨207625352194242001854329989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276833802925656002472439985 207625352194242001854329989)
              ·
                refine ⟨38929753536420375347686873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207625352194242001854329989 38929753536420375347686873)
                ·
                  refine ⟨29197315152315281510765155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38929753536420375347686873 29197315152315281510765155)
                  ·
                    refine ⟨43795972728472922266147733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29197315152315281510765155 43795972728472922266147733)
                    ·
                      refine ⟨2052936221647168231225675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43795972728472922266147733 2052936221647168231225675)
                      ·
                        rfl

theorem cell23_3998079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_3998079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998079 prefixEnd_3998079 := by exact prefixLift 3998079
  have htrace : WordTrace (prefixWord ++ tailWord_3998079) baseStart_3998079 baseEnd_3998079 := by
    simpa [prefixWord, tailWord_3998079, baseEnd_3998079] using wordTrace_append hprefix tailTrace_3998079
  have hstable : (prefixWord ++ tailWord_3998079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998079).length < 2 ^ (prefixWord ++ tailWord_3998079).sum := by decide
  have hdescent : baseEnd_3998079 < baseStart_3998079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998103 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_3998103 : Nat := 118140960795 + 3998103 * 2 ^ 59
def prefixEnd_3998103 : Nat := 4983230072969 + 3 ^ 40 * 3998103 * 2
def baseEnd_3998103 : Nat := 2052948545182876137325565

theorem tailTrace_3998103 : CollatzResearch.WordTrace tailWord_3998103 prefixEnd_3998103 2052948545182876137325565 := by
  unfold tailWord_3998103
  simp only [CollatzResearch.WordTrace]
  refine ⟨145822796234563127475302963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97215197489708751650201975 145822796234563127475302963)
  ·
    refine ⟨218734194351844691212954445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145822796234563127475302963 218734194351844691212954445)
    ·
      refine ⟨82025322881941759204857917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218734194351844691212954445 82025322881941759204857917)
      ·
        refine ⟨30759496080728159701821719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82025322881941759204857917 30759496080728159701821719)
        ·
          refine ⟨46139244121092239552732579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30759496080728159701821719 46139244121092239552732579)
          ·
            refine ⟨69208866181638359329098869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46139244121092239552732579 69208866181638359329098869)
            ·
              refine ⟨6488331204528596187103019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69208866181638359329098869 6488331204528596187103019)
              ·
                refine ⟨9732496806792894280654529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488331204528596187103019 9732496806792894280654529)
                ·
                  refine ⟨7299372605094670710490897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9732496806792894280654529 7299372605094670710490897)
                  ·
                    refine ⟨5474529453821003032868173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7299372605094670710490897 5474529453821003032868173)
                    ·
                      refine ⟨2052948545182876137325565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5474529453821003032868173 2052948545182876137325565)
                      ·
                        rfl

theorem cell23_3998103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_3998103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998103 prefixEnd_3998103 := by exact prefixLift 3998103
  have htrace : WordTrace (prefixWord ++ tailWord_3998103) baseStart_3998103 baseEnd_3998103 := by
    simpa [prefixWord, tailWord_3998103, baseEnd_3998103] using wordTrace_append hprefix tailTrace_3998103
  have hstable : (prefixWord ++ tailWord_3998103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998103).length < 2 ^ (prefixWord ++ tailWord_3998103).sum := by decide
  have hdescent : baseEnd_3998103 < baseStart_3998103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998139 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10]
def baseStart_3998139 : Nat := 118140960795 + 3998139 * 2 ^ 59
def prefixEnd_3998139 : Nat := 4983230072969 + 3 ^ 40 * 3998139 * 2
def baseEnd_3998139 : Nat := 2052967030486437996475399

theorem tailTrace_3998139 : CollatzResearch.WordTrace tailWord_3998139 prefixEnd_3998139 2052967030486437996475399 := by
  unfold tailWord_3998139
  simp only [CollatzResearch.WordTrace]
  refine ⟨145824109262432705623613471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97216072841621803749075647 145824109262432705623613471)
  ·
    refine ⟨218736163893649058435420207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145824109262432705623613471 218736163893649058435420207)
    ·
      refine ⟨328104245840473587653130311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218736163893649058435420207 328104245840473587653130311)
      ·
        refine ⟨492156368760710381479695467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328104245840473587653130311 492156368760710381479695467)
        ·
          refine ⟨738234553141065572219543201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492156368760710381479695467 738234553141065572219543201)
          ·
            refine ⟨553675914855799179164657401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738234553141065572219543201 553675914855799179164657401)
            ·
              refine ⟨415256936141849384373493051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553675914855799179164657401 415256936141849384373493051)
              ·
                refine ⟨622885404212774076560239577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415256936141849384373493051 622885404212774076560239577)
                ·
                  refine ⟨467164053159580557420179683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622885404212774076560239577 467164053159580557420179683)
                  ·
                    refine ⟨700746079739370836130269525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467164053159580557420179683 700746079739370836130269525)
                    ·
                      refine ⟨2052967030486437996475399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 700746079739370836130269525 2052967030486437996475399)
                      ·
                        rfl

theorem cell23_3998139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_3998139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998139 prefixEnd_3998139 := by exact prefixLift 3998139
  have htrace : WordTrace (prefixWord ++ tailWord_3998139) baseStart_3998139 baseEnd_3998139 := by
    simpa [prefixWord, tailWord_3998139, baseEnd_3998139] using wordTrace_append hprefix tailTrace_3998139
  have hstable : (prefixWord ++ tailWord_3998139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998139).length < 2 ^ (prefixWord ++ tailWord_3998139).sum := by decide
  have hdescent : baseEnd_3998139 < baseStart_3998139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998140 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 6]
def baseStart_3998140 : Nat := 118140960795 + 3998140 * 2 ^ 59
def prefixEnd_3998140 : Nat := 4983230072969 + 3 ^ 40 * 3998140 * 2
def baseEnd_3998140 : Nat := 228107504885232499173655

theorem tailTrace_3998140 : CollatzResearch.WordTrace tailWord_3998140 prefixEnd_3998140 228107504885232499173655 := by
  unfold tailWord_3998140
  simp only [CollatzResearch.WordTrace]
  refine ⟨72912072867714541397199937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97216097156952721862933249 72912072867714541397199937)
  ·
    refine ⟨54684054650785906047899953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72912072867714541397199937 54684054650785906047899953)
    ·
      refine ⟨41013040988089429535924965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54684054650785906047899953 41013040988089429535924965)
      ·
        refine ⟨7689945185266768037985931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41013040988089429535924965 7689945185266768037985931)
        ·
          refine ⟨11534917777900152056978897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689945185266768037985931 11534917777900152056978897)
          ·
            refine ⟨8651188333425114042734173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11534917777900152056978897 8651188333425114042734173)
            ·
              refine ⟨3244195625034417766025315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8651188333425114042734173 3244195625034417766025315)
              ·
                refine ⟨4866293437551626649037973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244195625034417766025315 4866293437551626649037973)
                ·
                  refine ⟨228107504885232499173655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4866293437551626649037973 228107504885232499173655)
                  ·
                    rfl

theorem cell23_3998140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_3998140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998140 prefixEnd_3998140 := by exact prefixLift 3998140
  have htrace : WordTrace (prefixWord ++ tailWord_3998140) baseStart_3998140 baseEnd_3998140 := by
    simpa [prefixWord, tailWord_3998140, baseEnd_3998140] using wordTrace_append hprefix tailTrace_3998140
  have hstable : (prefixWord ++ tailWord_3998140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998140).length < 2 ^ (prefixWord ++ tailWord_3998140).sum := by decide
  have hdescent : baseEnd_3998140 < baseStart_3998140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998183 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 4, 4]
def baseStart_3998183 : Nat := 118140960795 + 3998183 * 2 ^ 59
def prefixEnd_3998183 : Nat := 4983230072969 + 3 ^ 40 * 3998183 * 2
def baseEnd_3998183 : Nat := 684329874545078608108399

theorem tailTrace_3998183 : CollatzResearch.WordTrace tailWord_3998183 prefixEnd_3998183 684329874545078608108399 := by
  unfold tailWord_3998183
  simp only [CollatzResearch.WordTrace]
  refine ⟨145825714074273301138215203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97217142716182200758810135 145825714074273301138215203)
  ·
    refine ⟨218738571111409951707322805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145825714074273301138215203 218738571111409951707322805)
    ·
      refine ⟨20506741041694682972561513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218738571111409951707322805 20506741041694682972561513)
      ·
        refine ⟨15380055781271012229421135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20506741041694682972561513 15380055781271012229421135)
        ·
          refine ⟨23070083671906518344131703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15380055781271012229421135 23070083671906518344131703)
          ·
            refine ⟨34605125507859777516197555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23070083671906518344131703 34605125507859777516197555)
            ·
              refine ⟨51907688261789666274296333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34605125507859777516197555 51907688261789666274296333)
              ·
                refine ⟨19465383098171124852861125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51907688261789666274296333 19465383098171124852861125)
                ·
                  refine ⟨3649759330907085909911461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19465383098171124852861125 3649759330907085909911461)
                  ·
                    refine ⟨684329874545078608108399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3649759330907085909911461 684329874545078608108399)
                    ·
                      rfl

theorem cell23_3998183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_3998183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998183 prefixEnd_3998183 := by exact prefixLift 3998183
  have htrace : WordTrace (prefixWord ++ tailWord_3998183) baseStart_3998183 baseEnd_3998183 := by
    simpa [prefixWord, tailWord_3998183, baseEnd_3998183] using wordTrace_append hprefix tailTrace_3998183
  have hstable : (prefixWord ++ tailWord_3998183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998183).length < 2 ^ (prefixWord ++ tailWord_3998183).sum := by decide
  have hdescent : baseEnd_3998183 < baseStart_3998183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998184 : List Nat := [2, 1, 4, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_3998184 : Nat := 118140960795 + 3998184 * 2 ^ 59
def prefixEnd_3998184 : Nat := 4983230072969 + 3 ^ 40 * 3998184 * 2
def baseEnd_3998184 : Nat := 2052990137115890320412693

theorem tailTrace_3998184 : CollatzResearch.WordTrace tailWord_3998184 prefixEnd_3998184 2052990137115890320412693 := by
  unfold tailWord_3998184
  simp only [CollatzResearch.WordTrace]
  refine ⟨72912875273634839154500803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97217167031513118872667737 72912875273634839154500803)
  ·
    refine ⟨109369312910452258731751205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72912875273634839154500803 109369312910452258731751205)
    ·
      refine ⟨20506746170709798512203351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109369312910452258731751205 20506746170709798512203351)
      ·
        refine ⟨30760119256064697768305027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506746170709798512203351 30760119256064697768305027)
        ·
          refine ⟨46140178884097046652457541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30760119256064697768305027 46140178884097046652457541)
          ·
            refine ⟨8651283540768196247335789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46140178884097046652457541 8651283540768196247335789)
            ·
              refine ⟨3244231327788073592750921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8651283540768196247335789 3244231327788073592750921)
              ·
                refine ⟨2433173495841055194563191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244231327788073592750921 2433173495841055194563191)
                ·
                  refine ⟨3649760243761582791844787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433173495841055194563191 3649760243761582791844787)
                  ·
                    refine ⟨5474640365642374187767181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3649760243761582791844787 5474640365642374187767181)
                    ·
                      refine ⟨2052990137115890320412693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5474640365642374187767181 2052990137115890320412693)
                      ·
                        rfl

theorem cell23_3998184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_3998184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998184 prefixEnd_3998184 := by exact prefixLift 3998184
  have htrace : WordTrace (prefixWord ++ tailWord_3998184) baseStart_3998184 baseEnd_3998184 := by
    simpa [prefixWord, tailWord_3998184, baseEnd_3998184] using wordTrace_append hprefix tailTrace_3998184
  have hstable : (prefixWord ++ tailWord_3998184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998184).length < 2 ^ (prefixWord ++ tailWord_3998184).sum := by decide
  have hdescent : baseEnd_3998184 < baseStart_3998184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998193 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_3998193 : Nat := 118140960795 + 3998193 * 2 ^ 59
def prefixEnd_3998193 : Nat := 4983230072969 + 3 ^ 40 * 3998193 * 2
def baseEnd_3998193 : Nat := 2052994758441780785200151

theorem tailTrace_3998193 : CollatzResearch.WordTrace tailWord_3998193 prefixEnd_3998193 2052994758441780785200151 := by
  unfold tailWord_3998193
  simp only [CollatzResearch.WordTrace]
  refine ⟨145826078804237072846079233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97217385869491381897386155 145826078804237072846079233)
  ·
    refine ⟨109369559103177804634559425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145826078804237072846079233 109369559103177804634559425)
    ·
      refine ⟨82027169327383353475919569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109369559103177804634559425 82027169327383353475919569)
      ·
        refine ⟨61520376995537515106939677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82027169327383353475919569 61520376995537515106939677)
        ·
          refine ⟨23070141373326568165102379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61520376995537515106939677 23070141373326568165102379)
          ·
            refine ⟨34605212059989852247653569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23070141373326568165102379 34605212059989852247653569)
            ·
              refine ⟨25953909044992389185740177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34605212059989852247653569 25953909044992389185740177)
              ·
                refine ⟨19465431783744291889305133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25953909044992389185740177 19465431783744291889305133)
                ·
                  refine ⟨7299536918904109458489425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19465431783744291889305133 7299536918904109458489425)
                  ·
                    refine ⟨5474652689178082093867069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7299536918904109458489425 5474652689178082093867069)
                    ·
                      refine ⟨2052994758441780785200151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5474652689178082093867069 2052994758441780785200151)
                      ·
                        rfl

theorem cell23_3998193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_3998193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998193 prefixEnd_3998193 := by exact prefixLift 3998193
  have htrace : WordTrace (prefixWord ++ tailWord_3998193) baseStart_3998193 baseEnd_3998193 := by
    simpa [prefixWord, tailWord_3998193, baseEnd_3998193] using wordTrace_append hprefix tailTrace_3998193
  have hstable : (prefixWord ++ tailWord_3998193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998193).length < 2 ^ (prefixWord ++ tailWord_3998193).sum := by decide
  have hdescent : baseEnd_3998193 < baseStart_3998193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998247 : List Nat := [1, 1, 7, 2, 1, 2, 1, 8]
def baseStart_3998247 : Nat := 118140960795 + 3998247 * 2 ^ 59
def prefixEnd_3998247 : Nat := 4983230072969 + 3 ^ 40 * 3998247 * 2
def baseEnd_3998247 : Nat := 76037869866560132367589

theorem tailTrace_3998247 : CollatzResearch.WordTrace tailWord_3998247 prefixEnd_3998247 76037869866560132367589 := by
  unfold tailWord_3998247
  simp only [CollatzResearch.WordTrace]
  refine ⟨145828048346041440068544995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97218698897360960045696663 145828048346041440068544995)
  ·
    refine ⟨218742072519062160102817493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145828048346041440068544995 218742072519062160102817493)
    ·
      refine ⟨5126767324665519377409785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 218742072519062160102817493 5126767324665519377409785)
      ·
        refine ⟨3845075493499139533057339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5126767324665519377409785 3845075493499139533057339)
        ·
          refine ⟨5767613240248709299586009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845075493499139533057339 5767613240248709299586009)
          ·
            refine ⟨4325709930186531974689507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5767613240248709299586009 4325709930186531974689507)
            ·
              refine ⟨6488564895279797962034261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4325709930186531974689507 6488564895279797962034261)
              ·
                refine ⟨76037869866560132367589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6488564895279797962034261 76037869866560132367589)
                ·
                  rfl

theorem cell23_3998247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 8].length) (baseStart_3998247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998247 prefixEnd_3998247 := by exact prefixLift 3998247
  have htrace : WordTrace (prefixWord ++ tailWord_3998247) baseStart_3998247 baseEnd_3998247 := by
    simpa [prefixWord, tailWord_3998247, baseEnd_3998247] using wordTrace_append hprefix tailTrace_3998247
  have hstable : (prefixWord ++ tailWord_3998247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998247).length < 2 ^ (prefixWord ++ tailWord_3998247).sum := by decide
  have hdescent : baseEnd_3998247 < baseStart_3998247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998256 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 1, 8]
def baseStart_3998256 : Nat := 118140960795 + 3998256 * 2 ^ 59
def prefixEnd_3998256 : Nat := 4983230072969 + 3 ^ 40 * 3998256 * 2
def baseEnd_3998256 : Nat := 684342369241004679570787

theorem tailTrace_3998256 : CollatzResearch.WordTrace tailWord_3998256 prefixEnd_3998256 684342369241004679570787 := by
  unfold tailWord_3998256
  simp only [CollatzResearch.WordTrace]
  refine ⟨72914188301504417302811311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97218917735339223070415081 72914188301504417302811311)
  ·
    refine ⟨109371282452256625954216967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72914188301504417302811311 109371282452256625954216967)
    ·
      refine ⟨164056923678384938931325451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109371282452256625954216967 164056923678384938931325451)
      ·
        refine ⟨246085385517577408396988177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164056923678384938931325451 246085385517577408396988177)
        ·
          refine ⟨184564039138183056297741133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246085385517577408396988177 184564039138183056297741133)
          ·
            refine ⟨69211514676818646111652925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184564039138183056297741133 69211514676818646111652925)
            ·
              refine ⟨25954318003806992291869847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69211514676818646111652925 25954318003806992291869847)
              ·
                refine ⟨38931477005710488437804771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25954318003806992291869847 38931477005710488437804771)
                ·
                  refine ⟨58397215508565732656707157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38931477005710488437804771 58397215508565732656707157)
                  ·
                    refine ⟨684342369241004679570787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58397215508565732656707157 684342369241004679570787)
                    ·
                      rfl

theorem cell23_3998256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_3998256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998256 prefixEnd_3998256 := by exact prefixLift 3998256
  have htrace : WordTrace (prefixWord ++ tailWord_3998256) baseStart_3998256 baseEnd_3998256 := by
    simpa [prefixWord, tailWord_3998256, baseEnd_3998256] using wordTrace_append hprefix tailTrace_3998256
  have hstable : (prefixWord ++ tailWord_3998256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998256).length < 2 ^ (prefixWord ++ tailWord_3998256).sum := by decide
  have hdescent : baseEnd_3998256 < baseStart_3998256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998293 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3998293 : Nat := 118140960795 + 3998293 * 2 ^ 59
def prefixEnd_3998293 : Nat := 4983230072969 + 3 ^ 40 * 3998293 * 2
def baseEnd_3998293 : Nat := 2053046106507230393949691

theorem tailTrace_3998293 : CollatzResearch.WordTrace tailWord_3998293 prefixEnd_3998293 2053046106507230393949691 := by
  unfold tailWord_3998293
  simp only [CollatzResearch.WordTrace]
  refine ⟨145829726103874789924719533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97219817402583193283146355 145829726103874789924719533)
  ·
    refine ⟨54686147288953046221769825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145829726103874789924719533 54686147288953046221769825)
    ·
      refine ⟨41014610466714784666327369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54686147288953046221769825 41014610466714784666327369)
      ·
        refine ⟨30760957850036088499745527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41014610466714784666327369 30760957850036088499745527)
        ·
          refine ⟨46141436775054132749618291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30760957850036088499745527 46141436775054132749618291)
          ·
            refine ⟨69212155162581199124427437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46141436775054132749618291 69212155162581199124427437)
            ·
              refine ⟨25954558185967949671660289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69212155162581199124427437 25954558185967949671660289)
              ·
                refine ⟨19465918639475962253745217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25954558185967949671660289 19465918639475962253745217)
                ·
                  refine ⟨14599438979606971690308913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19465918639475962253745217 14599438979606971690308913)
                  ·
                    refine ⟨10949579234705228767731685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14599438979606971690308913 10949579234705228767731685)
                    ·
                      refine ⟨2053046106507230393949691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10949579234705228767731685 2053046106507230393949691)
                      ·
                        rfl

theorem cell23_3998293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3998293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998293 prefixEnd_3998293 := by exact prefixLift 3998293
  have htrace : WordTrace (prefixWord ++ tailWord_3998293) baseStart_3998293 baseEnd_3998293 := by
    simpa [prefixWord, tailWord_3998293, baseEnd_3998293] using wordTrace_append hprefix tailTrace_3998293
  have hstable : (prefixWord ++ tailWord_3998293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998293).length < 2 ^ (prefixWord ++ tailWord_3998293).sum := by decide
  have hdescent : baseEnd_3998293 < baseStart_3998293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998343 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3998343 : Nat := 118140960795 + 3998343 * 2 ^ 59
def prefixEnd_3998343 : Nat := 4983230072969 + 3 ^ 40 * 3998343 * 2
def baseEnd_3998343 : Nat := 2053071780539955198324461

theorem tailTrace_3998343 : CollatzResearch.WordTrace tailWord_3998343 prefixEnd_3998343 2053071780539955198324461 := by
  unfold tailWord_3998343
  simp only [CollatzResearch.WordTrace]
  refine ⟨145831549753693648464039683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97221033169129098976026455 145831549753693648464039683)
  ·
    refine ⟨218747324630540472696059525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145831549753693648464039683 218747324630540472696059525)
    ·
      refine ⟨41015123368226338630511161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218747324630540472696059525 41015123368226338630511161)
      ·
        refine ⟨30761342526169753972883371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41015123368226338630511161 30761342526169753972883371)
        ·
          refine ⟨46142013789254630959325057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30761342526169753972883371 46142013789254630959325057)
          ·
            refine ⟨34606510341940973219493793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46142013789254630959325057 34606510341940973219493793)
            ·
              refine ⟨25954882756455729914620345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34606510341940973219493793 25954882756455729914620345)
              ·
                refine ⟨19466162067341797435965259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25954882756455729914620345 19466162067341797435965259)
                ·
                  refine ⟨29199243101012696153947889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19466162067341797435965259 29199243101012696153947889)
                  ·
                    refine ⟨21899432325759522115460917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29199243101012696153947889 21899432325759522115460917)
                    ·
                      refine ⟨2053071780539955198324461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21899432325759522115460917 2053071780539955198324461)
                      ·
                        rfl

theorem cell23_3998343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3998343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998343 prefixEnd_3998343 := by exact prefixLift 3998343
  have htrace : WordTrace (prefixWord ++ tailWord_3998343) baseStart_3998343 baseEnd_3998343 := by
    simpa [prefixWord, tailWord_3998343, baseEnd_3998343] using wordTrace_append hprefix tailTrace_3998343
  have hstable : (prefixWord ++ tailWord_3998343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998343).length < 2 ^ (prefixWord ++ tailWord_3998343).sum := by decide
  have hdescent : baseEnd_3998343 < baseStart_3998343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998350 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3998350 : Nat := 118140960795 + 3998350 * 2 ^ 59
def prefixEnd_3998350 : Nat := 4983230072969 + 3 ^ 40 * 3998350 * 2
def baseEnd_3998350 : Nat := 684358458301512223645643

theorem tailTrace_3998350 : CollatzResearch.WordTrace tailWord_3998350 prefixEnd_3998350 684358458301512223645643 := by
  unfold tailWord_3998350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18228975633083536082443063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97221203376445525773029669 18228975633083536082443063)
  ·
    refine ⟨27343463449625304123664595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18228975633083536082443063 27343463449625304123664595)
    ·
      refine ⟨41015195174437956185496893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27343463449625304123664595 41015195174437956185496893)
      ·
        refine ⟨15380698190414233569561335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41015195174437956185496893 15380698190414233569561335)
        ·
          refine ⟨23071047285621350354342003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15380698190414233569561335 23071047285621350354342003)
          ·
            refine ⟨34606570928432025531513005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23071047285621350354342003 34606570928432025531513005)
            ·
              refine ⟨12977464098162009574317377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34606570928432025531513005 12977464098162009574317377)
              ·
                refine ⟨9733098073621507180738033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12977464098162009574317377 9733098073621507180738033)
                ·
                  refine ⟨7299823555216130385553525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9733098073621507180738033 7299823555216130385553525)
                  ·
                    refine ⟨684358458301512223645643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7299823555216130385553525 684358458301512223645643)
                    ·
                      rfl

theorem cell23_3998350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3998350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998350 prefixEnd_3998350 := by exact prefixLift 3998350
  have htrace : WordTrace (prefixWord ++ tailWord_3998350) baseStart_3998350 baseEnd_3998350 := by
    simpa [prefixWord, tailWord_3998350, baseEnd_3998350] using wordTrace_append hprefix tailTrace_3998350
  have hstable : (prefixWord ++ tailWord_3998350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998350).length < 2 ^ (prefixWord ++ tailWord_3998350).sum := by decide
  have hdescent : baseEnd_3998350 < baseStart_3998350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998354 : List Nat := [3, 2, 3, 1, 2, 2, 3, 2, 5]
def baseStart_3998354 : Nat := 118140960795 + 3998354 * 2 ^ 59
def prefixEnd_3998354 : Nat := 4983230072969 + 3 ^ 40 * 3998354 * 2
def baseEnd_3998354 : Nat := 228119714314128295031879

theorem tailTrace_3998354 : CollatzResearch.WordTrace tailWord_3998354 prefixEnd_3998354 228119714314128295031879 := by
  unfold tailWord_3998354
  simp only [CollatzResearch.WordTrace]
  refine ⟨36457987739163449335672529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97221300637769198228460077 36457987739163449335672529)
  ·
    refine ⟨27343490804372587001754397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36457987739163449335672529 27343490804372587001754397)
    ·
      refine ⟨10253809051639720125657899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27343490804372587001754397 10253809051639720125657899)
      ·
        refine ⟨15380713577459580188486849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253809051639720125657899 15380713577459580188486849)
        ·
          refine ⟨11535535183094685141365137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15380713577459580188486849 11535535183094685141365137)
          ·
            refine ⟨8651651387321013856023853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11535535183094685141365137 8651651387321013856023853)
            ·
              refine ⟨3244369270245380196008945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8651651387321013856023853 3244369270245380196008945)
              ·
                refine ⟨2433276952684035147006709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244369270245380196008945 2433276952684035147006709)
                ·
                  refine ⟨228119714314128295031879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2433276952684035147006709 228119714314128295031879)
                  ·
                    rfl

theorem cell23_3998354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_3998354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998354 prefixEnd_3998354 := by exact prefixLift 3998354
  have htrace : WordTrace (prefixWord ++ tailWord_3998354) baseStart_3998354 baseEnd_3998354 := by
    simpa [prefixWord, tailWord_3998354, baseEnd_3998354] using wordTrace_append hprefix tailTrace_3998354
  have hstable : (prefixWord ++ tailWord_3998354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998354).length < 2 ^ (prefixWord ++ tailWord_3998354).sum := by decide
  have hdescent : baseEnd_3998354 < baseStart_3998354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998410 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 6]
def baseStart_3998410 : Nat := 118140960795 + 3998410 * 2 ^ 59
def prefixEnd_3998410 : Nat := 4983230072969 + 3 ^ 40 * 3998410 * 2
def baseEnd_3998410 : Nat := 228122909304867381798517

theorem tailTrace_3998410 : CollatzResearch.WordTrace tailWord_3998410 prefixEnd_3998410 228122909304867381798517 := by
  unfold tailWord_3998410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36458498361112729726682171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97222662296300612604485789 36458498361112729726682171)
  ·
    refine ⟨54687747541669094590023257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36458498361112729726682171 54687747541669094590023257)
    ·
      refine ⟨41015810656251820942517443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54687747541669094590023257 41015810656251820942517443)
      ·
        refine ⟨61523715984377731413776165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41015810656251820942517443 61523715984377731413776165)
        ·
          refine ⟨11535696747070824640083031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61523715984377731413776165 11535696747070824640083031)
          ·
            refine ⟨17303545120606236960124547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11535696747070824640083031 17303545120606236960124547)
            ·
              refine ⟨25955317680909355440186821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17303545120606236960124547 25955317680909355440186821)
              ·
                refine ⟨4866622065170504145035029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25955317680909355440186821 4866622065170504145035029)
                ·
                  refine ⟨228122909304867381798517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4866622065170504145035029 228122909304867381798517)
                  ·
                    rfl

theorem cell23_3998410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_3998410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998410 prefixEnd_3998410 := by exact prefixLift 3998410
  have htrace : WordTrace (prefixWord ++ tailWord_3998410) baseStart_3998410 baseEnd_3998410 := by
    simpa [prefixWord, tailWord_3998410, baseEnd_3998410] using wordTrace_append hprefix tailTrace_3998410
  have hstable : (prefixWord ++ tailWord_3998410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998410).length < 2 ^ (prefixWord ++ tailWord_3998410).sum := by decide
  have hdescent : baseEnd_3998410 < baseStart_3998410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998414 : List Nat := [4, 1, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_3998414 : Nat := 118140960795 + 3998414 * 2 ^ 59
def prefixEnd_3998414 : Nat := 4983230072969 + 3 ^ 40 * 3998414 * 2
def baseEnd_3998414 : Nat := 684369412555474806845545

theorem tailTrace_3998414 : CollatzResearch.WordTrace tailWord_3998414 prefixEnd_3998414 684369412555474806845545 := by
  unfold tailWord_3998414
  simp only [CollatzResearch.WordTrace]
  refine ⟨18229267417054553448734287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97222759557624285059916197 18229267417054553448734287)
  ·
    refine ⟨27343901125581830173101431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18229267417054553448734287 27343901125581830173101431)
    ·
      refine ⟨41015851688372745259652147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27343901125581830173101431 41015851688372745259652147)
      ·
        refine ⟨61523777532559117889478221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41015851688372745259652147 61523777532559117889478221)
        ·
          refine ⟨23071416574709669208554333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61523777532559117889478221 23071416574709669208554333)
          ·
            refine ⟨8651781215516125953207875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23071416574709669208554333 8651781215516125953207875)
            ·
              refine ⟨12977671823274188929811813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8651781215516125953207875 12977671823274188929811813)
              ·
                refine ⟨2433313466863910424339715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12977671823274188929811813 2433313466863910424339715)
                ·
                  refine ⟨3649970200295865636509573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433313466863910424339715 3649970200295865636509573)
                  ·
                    refine ⟨684369412555474806845545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3649970200295865636509573 684369412555474806845545)
                    ·
                      rfl

theorem cell23_3998414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_3998414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998414 prefixEnd_3998414 := by exact prefixLift 3998414
  have htrace : WordTrace (prefixWord ++ tailWord_3998414) baseStart_3998414 baseEnd_3998414 := by
    simpa [prefixWord, tailWord_3998414, baseEnd_3998414] using wordTrace_append hprefix tailTrace_3998414
  have hstable : (prefixWord ++ tailWord_3998414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998414).length < 2 ^ (prefixWord ++ tailWord_3998414).sum := by decide
  have hdescent : baseEnd_3998414 < baseStart_3998414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998437 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3998437 : Nat := 118140960795 + 3998437 * 2 ^ 59
def prefixEnd_3998437 : Nat := 4983230072969 + 3 ^ 40 * 3998437 * 2
def baseEnd_3998437 : Nat := 2053120047721477830549029

theorem tailTrace_3998437 : CollatzResearch.WordTrace tailWord_3998437 prefixEnd_3998437 2053120047721477830549029 := by
  unfold tailWord_3998437
  simp only [CollatzResearch.WordTrace]
  refine ⟨145834978215353102517961565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97223318810235401678641043 145834978215353102517961565)
  ·
    refine ⟨54688116830757413444235587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145834978215353102517961565 54688116830757413444235587)
    ·
      refine ⟨82032175246136120166353381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54688116830757413444235587 82032175246136120166353381)
      ·
        refine ⟨15381032858650522531191259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82032175246136120166353381 15381032858650522531191259)
        ·
          refine ⟨23071549287975783796786889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15381032858650522531191259 23071549287975783796786889)
          ·
            refine ⟨17303661965981837847590167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23071549287975783796786889 17303661965981837847590167)
            ·
              refine ⟨25955492948972756771385251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17303661965981837847590167 25955492948972756771385251)
              ·
                refine ⟨38933239423459135157077877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25955492948972756771385251 38933239423459135157077877)
                ·
                  refine ⟨3649991195949293920976051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38933239423459135157077877 3649991195949293920976051)
                  ·
                    refine ⟨5474986793923940881464077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3649991195949293920976051 5474986793923940881464077)
                    ·
                      refine ⟨2053120047721477830549029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5474986793923940881464077 2053120047721477830549029)
                      ·
                        rfl

theorem cell23_3998437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3998437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998437 prefixEnd_3998437 := by exact prefixLift 3998437
  have htrace : WordTrace (prefixWord ++ tailWord_3998437) baseStart_3998437 baseEnd_3998437 := by
    simpa [prefixWord, tailWord_3998437, baseEnd_3998437] using wordTrace_append hprefix tailTrace_3998437
  have hstable : (prefixWord ++ tailWord_3998437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998437).length < 2 ^ (prefixWord ++ tailWord_3998437).sum := by decide
  have hdescent : baseEnd_3998437 < baseStart_3998437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998447 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 1, 5, 2]
def baseStart_3998447 : Nat := 118140960795 + 3998447 * 2 ^ 59
def prefixEnd_3998447 : Nat := 4983230072969 + 3 ^ 40 * 3998447 * 2
def baseEnd_3998447 : Nat := 2053125182528022791423983

theorem tailTrace_3998447 : CollatzResearch.WordTrace tailWord_3998447 prefixEnd_3998447 2053125182528022791423983 := by
  unfold tailWord_3998447
  simp only [CollatzResearch.WordTrace]
  refine ⟨145835342945316874225825595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97223561963544582817217063 145835342945316874225825595)
  ·
    refine ⟨218753014417975311338738393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145835342945316874225825595 218753014417975311338738393)
    ·
      refine ⟨164064760813481483504053795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218753014417975311338738393 164064760813481483504053795)
      ·
        refine ⟨246097141220222225256080693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164064760813481483504053795 246097141220222225256080693)
        ·
          refine ⟨23071606989395833617757565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246097141220222225256080693 23071606989395833617757565)
          ·
            refine ⟨8651852621023437606659087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23071606989395833617757565 8651852621023437606659087)
            ·
              refine ⟨12977778931535156409988631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8651852621023437606659087 12977778931535156409988631)
              ·
                refine ⟨19466668397302734614982947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12977778931535156409988631 19466668397302734614982947)
                ·
                  refine ⟨29200002595954101922474421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19466668397302734614982947 29200002595954101922474421)
                  ·
                    refine ⟨2737500243370697055231977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29200002595954101922474421 2737500243370697055231977)
                    ·
                      refine ⟨2053125182528022791423983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2737500243370697055231977 2053125182528022791423983)
                      ·
                        rfl

theorem cell23_3998447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5, 2].length) (baseStart_3998447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998447 prefixEnd_3998447 := by exact prefixLift 3998447
  have htrace : WordTrace (prefixWord ++ tailWord_3998447) baseStart_3998447 baseEnd_3998447 := by
    simpa [prefixWord, tailWord_3998447, baseEnd_3998447] using wordTrace_append hprefix tailTrace_3998447
  have hstable : (prefixWord ++ tailWord_3998447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998447).length < 2 ^ (prefixWord ++ tailWord_3998447).sum := by decide
  have hdescent : baseEnd_3998447 < baseStart_3998447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998471 : List Nat := [1, 1, 4, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3998471 : Nat := 118140960795 + 3998471 * 2 ^ 59
def prefixEnd_3998471 : Nat := 4983230072969 + 3 ^ 40 * 3998471 * 2
def baseEnd_3998471 : Nat := 2053137506063730697523873

theorem tailTrace_3998471 : CollatzResearch.WordTrace tailWord_3998471 prefixEnd_3998471 2053137506063730697523873 := by
  unfold tailWord_3998471
  simp only [CollatzResearch.WordTrace]
  refine ⟨145836218297229926324699267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97224145531486617549799511 145836218297229926324699267)
  ·
    refine ⟨218754327445844889487048901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145836218297229926324699267 218754327445844889487048901)
    ·
      refine ⟨41016436396095916778821669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218754327445844889487048901 41016436396095916778821669)
      ·
        refine ⟨7690581824267984396029063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41016436396095916778821669 7690581824267984396029063)
        ·
          refine ⟨11535872736401976594043595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690581824267984396029063 11535872736401976594043595)
          ·
            refine ⟨17303809104602964891065393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11535872736401976594043595 17303809104602964891065393)
            ·
              refine ⟨12977856828452223668299045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17303809104602964891065393 12977856828452223668299045)
              ·
                refine ⟨2433348155334791937806071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12977856828452223668299045 2433348155334791937806071)
                ·
                  refine ⟨3650022233002187906709107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433348155334791937806071 3650022233002187906709107)
                  ·
                    refine ⟨5475033349503281860063661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3650022233002187906709107 5475033349503281860063661)
                    ·
                      refine ⟨2053137506063730697523873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5475033349503281860063661 2053137506063730697523873)
                      ·
                        rfl

theorem cell23_3998471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3998471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998471 prefixEnd_3998471 := by exact prefixLift 3998471
  have htrace : WordTrace (prefixWord ++ tailWord_3998471) baseStart_3998471 baseEnd_3998471 := by
    simpa [prefixWord, tailWord_3998471, baseEnd_3998471] using wordTrace_append hprefix tailTrace_3998471
  have hstable : (prefixWord ++ tailWord_3998471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998471).length < 2 ^ (prefixWord ++ tailWord_3998471).sum := by decide
  have hdescent : baseEnd_3998471 < baseStart_3998471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998483 : List Nat := [1, 1, 1, 2, 1, 3, 4, 10]
def baseStart_3998483 : Nat := 118140960795 + 3998483 * 2 ^ 59
def prefixEnd_3998483 : Nat := 4983230072969 + 3 ^ 40 * 3998483 * 2
def baseEnd_3998483 : Nat := 76042358067836468539771

theorem tailTrace_3998483 : CollatzResearch.WordTrace tailWord_3998483 prefixEnd_3998483 76042358067836468539771 := by
  unfold tailWord_3998483
  simp only [CollatzResearch.WordTrace]
  refine ⟨145836655973186452374136103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97224437315457634916090735 145836655973186452374136103)
  ·
    refine ⟨218754983959779678561204155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145836655973186452374136103 218754983959779678561204155)
    ·
      refine ⟨328132475939669517841806233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218754983959779678561204155 328132475939669517841806233)
      ·
        refine ⟨246099356954752138381354675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328132475939669517841806233 246099356954752138381354675)
        ·
          refine ⟨369149035432128207572032013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246099356954752138381354675 369149035432128207572032013)
          ·
            refine ⟨138430888287048077839512005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369149035432128207572032013 138430888287048077839512005)
            ·
              refine ⟨25955791553821514594908501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138430888287048077839512005 25955791553821514594908501)
              ·
                refine ⟨76042358067836468539771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25955791553821514594908501 76042358067836468539771)
                ·
                  rfl

theorem cell23_3998483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 10].length) (baseStart_3998483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998483 prefixEnd_3998483 := by exact prefixLift 3998483
  have htrace : WordTrace (prefixWord ++ tailWord_3998483) baseStart_3998483 baseEnd_3998483 := by
    simpa [prefixWord, tailWord_3998483, baseEnd_3998483] using wordTrace_append hprefix tailTrace_3998483
  have hstable : (prefixWord ++ tailWord_3998483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998483).length < 2 ^ (prefixWord ++ tailWord_3998483).sum := by decide
  have hdescent : baseEnd_3998483 < baseStart_3998483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998490 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3998490 : Nat := 118140960795 + 3998490 * 2 ^ 59
def prefixEnd_3998490 : Nat := 4983230072969 + 3 ^ 40 * 3998490 * 2
def baseEnd_3998490 : Nat := 2053147262196166123186285

theorem tailTrace_3998490 : CollatzResearch.WordTrace tailWord_3998490 prefixEnd_3998490 2053147262196166123186285 := by
  unfold tailWord_3998490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36459227821040273142410231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97224607522774061713093949 36459227821040273142410231)
  ·
    refine ⟨54688841731560409713615347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36459227821040273142410231 54688841731560409713615347)
    ·
      refine ⟨82033262597340614570423021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54688841731560409713615347 82033262597340614570423021)
      ·
        refine ⟨30762473474002730463908633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82033262597340614570423021 30762473474002730463908633)
        ·
          refine ⟨23071855105502047847931475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30762473474002730463908633 23071855105502047847931475)
          ·
            refine ⟨34607782658253071771897213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23071855105502047847931475 34607782658253071771897213)
            ·
              refine ⟨12977918496844901914461455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34607782658253071771897213 12977918496844901914461455)
              ·
                refine ⟨19466877745267352871692183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12977918496844901914461455 19466877745267352871692183)
                ·
                  refine ⟨29200316617901029307538275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19466877745267352871692183 29200316617901029307538275)
                  ·
                    refine ⟨43800474926851543961307413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29200316617901029307538275 43800474926851543961307413)
                    ·
                      refine ⟨2053147262196166123186285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43800474926851543961307413 2053147262196166123186285)
                      ·
                        rfl

theorem cell23_3998490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3998490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998490 prefixEnd_3998490 := by exact prefixLift 3998490
  have htrace : WordTrace (prefixWord ++ tailWord_3998490) baseStart_3998490 baseEnd_3998490 := by
    simpa [prefixWord, tailWord_3998490, baseEnd_3998490] using wordTrace_append hprefix tailTrace_3998490
  have hstable : (prefixWord ++ tailWord_3998490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998490).length < 2 ^ (prefixWord ++ tailWord_3998490).sum := by decide
  have hdescent : baseEnd_3998490 < baseStart_3998490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998548 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_3998548 : Nat := 118140960795 + 3998548 * 2 ^ 59
def prefixEnd_3998548 : Nat := 4983230072969 + 3 ^ 40 * 3998548 * 2
def baseEnd_3998548 : Nat := 2053177044074126896261019

theorem tailTrace_3998548 : CollatzResearch.WordTrace tailWord_3998548 prefixEnd_3998548 2053177044074126896261019 := by
  unfold tailWord_3998548
  simp only [CollatzResearch.WordTrace]
  refine ⟨72919513358975484237626149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97226017811967312316834865 72919513358975484237626149)
  ·
    refine ⟨13672408754807903294554903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72919513358975484237626149 13672408754807903294554903)
    ·
      refine ⟨20508613132211854941832355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13672408754807903294554903 20508613132211854941832355)
      ·
        refine ⟨30762919698317782412748533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20508613132211854941832355 30762919698317782412748533)
        ·
          refine ⟨2884023721717292101195175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30762919698317782412748533 2884023721717292101195175)
          ·
            refine ⟨4326035582575938151792763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884023721717292101195175 4326035582575938151792763)
            ·
              refine ⟨6489053373863907227689145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326035582575938151792763 6489053373863907227689145)
              ·
                refine ⟨4866790030397930420766859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6489053373863907227689145 4866790030397930420766859)
                ·
                  refine ⟨7300185045596895631150289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4866790030397930420766859 7300185045596895631150289)
                  ·
                    refine ⟨5475138784197671723362717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7300185045596895631150289 5475138784197671723362717)
                    ·
                      refine ⟨2053177044074126896261019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5475138784197671723362717 2053177044074126896261019)
                      ·
                        rfl

theorem cell23_3998548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_3998548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998548 prefixEnd_3998548 := by exact prefixLift 3998548
  have htrace : WordTrace (prefixWord ++ tailWord_3998548) baseStart_3998548 baseEnd_3998548 := by
    simpa [prefixWord, tailWord_3998548, baseEnd_3998548] using wordTrace_append hprefix tailTrace_3998548
  have hstable : (prefixWord ++ tailWord_3998548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998548).length < 2 ^ (prefixWord ++ tailWord_3998548).sum := by decide
  have hdescent : baseEnd_3998548 < baseStart_3998548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998554 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2]
def baseStart_3998554 : Nat := 118140960795 + 3998554 * 2 ^ 59
def prefixEnd_3998554 : Nat := 4983230072969 + 3 ^ 40 * 3998554 * 2
def baseEnd_3998554 : Nat := 2053180124958053872785991

theorem tailTrace_3998554 : CollatzResearch.WordTrace tailWord_3998554 prefixEnd_3998554 2053180124958053872785991 := by
  unfold tailWord_3998554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36459811388982307874992679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97226163703952820999980477 36459811388982307874992679)
  ·
    refine ⟨54689717083473461812489019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36459811388982307874992679 54689717083473461812489019)
    ·
      refine ⟨82034575625210192718733529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54689717083473461812489019 82034575625210192718733529)
      ·
        refine ⟨61525931718907644539050147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82034575625210192718733529 61525931718907644539050147)
        ·
          refine ⟨92288897578361466808575221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61525931718907644539050147 92288897578361466808575221)
          ·
            refine ⟨8652084147971387513303927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92288897578361466808575221 8652084147971387513303927)
            ·
              refine ⟨12978126221957081269955891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652084147971387513303927 12978126221957081269955891)
              ·
                refine ⟨19467189332935621904933837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978126221957081269955891 19467189332935621904933837)
                ·
                  refine ⟨7300195999850858214350189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19467189332935621904933837 7300195999850858214350189)
                  ·
                    refine ⟨2737573499944071830381321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7300195999850858214350189 2737573499944071830381321)
                    ·
                      refine ⟨2053180124958053872785991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2737573499944071830381321 2053180124958053872785991)
                      ·
                        rfl

theorem cell23_3998554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_3998554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998554 prefixEnd_3998554 := by exact prefixLift 3998554
  have htrace : WordTrace (prefixWord ++ tailWord_3998554) baseStart_3998554 baseEnd_3998554 := by
    simpa [prefixWord, tailWord_3998554, baseEnd_3998554] using wordTrace_append hprefix tailTrace_3998554
  have hstable : (prefixWord ++ tailWord_3998554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998554).length < 2 ^ (prefixWord ++ tailWord_3998554).sum := by decide
  have hdescent : baseEnd_3998554 < baseStart_3998554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998597 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_3998597 : Nat := 118140960795 + 3998597 * 2 ^ 59
def prefixEnd_3998597 : Nat := 4983230072969 + 3 ^ 40 * 3998597 * 2
def baseEnd_3998597 : Nat := 2053202204626197204548293

theorem tailTrace_3998597 : CollatzResearch.WordTrace tailWord_3998597 prefixEnd_3998597 2053202204626197204548293 := by
  unfold tailWord_3998597
  simp only [CollatzResearch.WordTrace]
  refine ⟨145840813894773449843786045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97227209263182299895857363 145840813894773449843786045)
  ·
    refine ⟨54690305210540043691419767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145840813894773449843786045 54690305210540043691419767)
    ·
      refine ⟨82035457815810065537129651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54690305210540043691419767 82035457815810065537129651)
      ·
        refine ⟨123053186723715098305694477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82035457815810065537129651 123053186723715098305694477)
        ·
          refine ⟨46144945021393161864635429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123053186723715098305694477 46144945021393161864635429)
          ·
            refine ⟨8652177191511217849619143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46144945021393161864635429 8652177191511217849619143)
            ·
              refine ⟨12978265787266826774428715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652177191511217849619143 12978265787266826774428715)
              ·
                refine ⟨19467398680900240161643073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978265787266826774428715 19467398680900240161643073)
                ·
                  refine ⟨14600549010675180121232305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19467398680900240161643073 14600549010675180121232305)
                  ·
                    refine ⟨10950411758006385090924229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14600549010675180121232305 10950411758006385090924229)
                    ·
                      refine ⟨2053202204626197204548293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10950411758006385090924229 2053202204626197204548293)
                      ·
                        rfl

theorem cell23_3998597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_3998597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998597 prefixEnd_3998597 := by exact prefixLift 3998597
  have htrace : WordTrace (prefixWord ++ tailWord_3998597) baseStart_3998597 baseEnd_3998597 := by
    simpa [prefixWord, tailWord_3998597, baseEnd_3998597] using wordTrace_append hprefix tailTrace_3998597
  have hstable : (prefixWord ++ tailWord_3998597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998597).length < 2 ^ (prefixWord ++ tailWord_3998597).sum := by decide
  have hdescent : baseEnd_3998597 < baseStart_3998597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998601 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 2, 2, 2]
def baseStart_3998601 : Nat := 118140960795 + 3998601 * 2 ^ 59
def prefixEnd_3998601 : Nat := 4983230072969 + 3 ^ 40 * 3998601 * 2
def baseEnd_3998601 : Nat := 2053204258548815188898275

theorem tailTrace_3998601 : CollatzResearch.WordTrace tailWord_3998601 prefixEnd_3998601 2053204258548815188898275 := by
  unfold tailWord_3998601
  simp only [CollatzResearch.WordTrace]
  refine ⟨145840959786758958526931657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97227306524505972351287771 145840959786758958526931657)
  ·
    refine ⟨109380719840069218895198743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145840959786758958526931657 109380719840069218895198743)
    ·
      refine ⟨164071079760103828342798115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109380719840069218895198743 164071079760103828342798115)
      ·
        refine ⟨246106619640155742514197173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164071079760103828342798115 246106619640155742514197173)
        ·
          refine ⟨23072495591264600860705985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246106619640155742514197173 23072495591264600860705985)
          ·
            refine ⟨17304371693448450645529489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23072495591264600860705985 17304371693448450645529489)
            ·
              refine ⟨12978278770086337984147117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17304371693448450645529489 12978278770086337984147117)
              ·
                refine ⟨4866854538782376744055169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12978278770086337984147117 4866854538782376744055169)
                ·
                  refine ⟨3650140904086782558041377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4866854538782376744055169 3650140904086782558041377)
                  ·
                    refine ⟨2737605678065086918531033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3650140904086782558041377 2737605678065086918531033)
                    ·
                      refine ⟨2053204258548815188898275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2737605678065086918531033 2053204258548815188898275)
                      ·
                        rfl

theorem cell23_3998601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 2, 2].length) (baseStart_3998601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998601 prefixEnd_3998601 := by exact prefixLift 3998601
  have htrace : WordTrace (prefixWord ++ tailWord_3998601) baseStart_3998601 baseEnd_3998601 := by
    simpa [prefixWord, tailWord_3998601, baseEnd_3998601] using wordTrace_append hprefix tailTrace_3998601
  have hstable : (prefixWord ++ tailWord_3998601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998601).length < 2 ^ (prefixWord ++ tailWord_3998601).sum := by decide
  have hdescent : baseEnd_3998601 < baseStart_3998601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998674 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3998674 : Nat := 118140960795 + 3998674 * 2 ^ 59
def prefixEnd_3998674 : Nat := 4983230072969 + 3 ^ 40 * 3998674 * 2
def baseEnd_3998674 : Nat := 2053241742636593403285439

theorem tailTrace_3998674 : CollatzResearch.WordTrace tailWord_3998674 prefixEnd_3998674 2053241742636593403285439 := by
  unfold tailWord_3998674
  simp only [CollatzResearch.WordTrace]
  refine ⟨36460905578873622998584769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97229081543662994662892717 36460905578873622998584769)
  ·
    refine ⟨27345679184155217248938577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36460905578873622998584769 27345679184155217248938577)
    ·
      refine ⟨20509259388116412936703933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27345679184155217248938577 20509259388116412936703933)
      ·
        refine ⟨7690972270543654851263975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20509259388116412936703933 7690972270543654851263975)
        ·
          refine ⟨11536458405815482276895963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690972270543654851263975 11536458405815482276895963)
          ·
            refine ⟨17304687608723223415343945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536458405815482276895963 17304687608723223415343945)
            ·
              refine ⟨12978515706542417561507959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17304687608723223415343945 12978515706542417561507959)
              ·
                refine ⟨19467773559813626342261939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978515706542417561507959 19467773559813626342261939)
                ·
                  refine ⟨29201660339720439513392909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19467773559813626342261939 29201660339720439513392909)
                  ·
                    refine ⟨10950622627395164817522341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29201660339720439513392909 10950622627395164817522341)
                    ·
                      refine ⟨2053241742636593403285439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10950622627395164817522341 2053241742636593403285439)
                      ·
                        rfl

theorem cell23_3998674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3998674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998674 prefixEnd_3998674 := by exact prefixLift 3998674
  have htrace : WordTrace (prefixWord ++ tailWord_3998674) baseStart_3998674 baseEnd_3998674 := by
    simpa [prefixWord, tailWord_3998674, baseEnd_3998674] using wordTrace_append hprefix tailTrace_3998674
  have hstable : (prefixWord ++ tailWord_3998674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998674).length < 2 ^ (prefixWord ++ tailWord_3998674).sum := by decide
  have hdescent : baseEnd_3998674 < baseStart_3998674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998751 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 2, 3, 2]
def baseStart_3998751 : Nat := 118140960795 + 3998751 * 2 ^ 59
def prefixEnd_3998751 : Nat := 4983230072969 + 3 ^ 40 * 3998751 * 2
def baseEnd_3998751 : Nat := 2053281280646989602022585

theorem tailTrace_3998751 : CollatzResearch.WordTrace tailWord_3998751 prefixEnd_3998751 2053281280646989602022585 := by
  unfold tailWord_3998751
  simp only [CollatzResearch.WordTrace]
  refine ⟨145846430736215534144892107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97230953824143689429928071 145846430736215534144892107)
  ·
    refine ⟨218769646104323301217338161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145846430736215534144892107 218769646104323301217338161)
    ·
      refine ⟨164077234578242475913003621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218769646104323301217338161 164077234578242475913003621)
      ·
        refine ⟨30764481483420464233688179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164077234578242475913003621 30764481483420464233688179)
        ·
          refine ⟨46146722225130696350532269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30764481483420464233688179 46146722225130696350532269)
          ·
            refine ⟨17305020834424011131449601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46146722225130696350532269 17305020834424011131449601)
            ·
              refine ⟨12978765625818008348587201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17305020834424011131449601 12978765625818008348587201)
              ·
                refine ⟨9734074219363506261440401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12978765625818008348587201 9734074219363506261440401)
                ·
                  refine ⟨7300555664522629696080301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9734074219363506261440401 7300555664522629696080301)
                  ·
                    refine ⟨2737708374195986136030113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7300555664522629696080301 2737708374195986136030113)
                    ·
                      refine ⟨2053281280646989602022585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2737708374195986136030113 2053281280646989602022585)
                      ·
                        rfl

theorem cell23_3998751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_3998751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998751 prefixEnd_3998751 := by exact prefixLift 3998751
  have htrace : WordTrace (prefixWord ++ tailWord_3998751) baseStart_3998751 baseEnd_3998751 := by
    simpa [prefixWord, tailWord_3998751, baseEnd_3998751] using wordTrace_append hprefix tailTrace_3998751
  have hstable : (prefixWord ++ tailWord_3998751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998751).length < 2 ^ (prefixWord ++ tailWord_3998751).sum := by decide
  have hdescent : baseEnd_3998751 < baseStart_3998751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998752 : List Nat := [2, 1, 1, 7, 1, 2, 2, 2, 1, 4]
def baseStart_3998752 : Nat := 118140960795 + 3998752 * 2 ^ 59
def prefixEnd_3998752 : Nat := 4983230072969 + 3 ^ 40 * 3998752 * 2
def baseEnd_3998752 : Nat := 684427264709214699370027

theorem tailTrace_3998752 : CollatzResearch.WordTrace tailWord_3998752 prefixEnd_3998752 684427264709214699370027 := by
  unfold tailWord_3998752
  simp only [CollatzResearch.WordTrace]
  refine ⟨72923233604605955657839255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97230978139474607543785673 72923233604605955657839255)
  ·
    refine ⟨109384850406908933486758883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72923233604605955657839255 109384850406908933486758883)
    ·
      refine ⟨164077275610363400230138325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109384850406908933486758883 164077275610363400230138325)
      ·
        refine ⟨3845561147117892192893867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 164077275610363400230138325 3845561147117892192893867)
        ·
          refine ⟨5768341720676838289340801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845561147117892192893867 5768341720676838289340801)
          ·
            refine ⟨4326256290507628717005601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5768341720676838289340801 4326256290507628717005601)
            ·
              refine ⟨3244692217880721537754201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4326256290507628717005601 3244692217880721537754201)
              ·
                refine ⟨2433519163410541153315651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244692217880721537754201 2433519163410541153315651)
                ·
                  refine ⟨3650278745115811729973477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433519163410541153315651 3650278745115811729973477)
                  ·
                    refine ⟨684427264709214699370027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3650278745115811729973477 684427264709214699370027)
                    ·
                      rfl

theorem cell23_3998752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 4].length) (baseStart_3998752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998752 prefixEnd_3998752 := by exact prefixLift 3998752
  have htrace : WordTrace (prefixWord ++ tailWord_3998752) baseStart_3998752 baseEnd_3998752 := by
    simpa [prefixWord, tailWord_3998752, baseEnd_3998752] using wordTrace_append hprefix tailTrace_3998752
  have hstable : (prefixWord ++ tailWord_3998752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998752).length < 2 ^ (prefixWord ++ tailWord_3998752).sum := by decide
  have hdescent : baseEnd_3998752 < baseStart_3998752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998757 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_3998757 : Nat := 118140960795 + 3998757 * 2 ^ 59
def prefixEnd_3998757 : Nat := 4983230072969 + 3 ^ 40 * 3998757 * 2
def baseEnd_3998757 : Nat := 684428120510305526182519

theorem tailTrace_3998757 : CollatzResearch.WordTrace tailWord_3998757 prefixEnd_3998757 684428120510305526182519 := by
  unfold tailWord_3998757
  simp only [CollatzResearch.WordTrace]
  refine ⟨145846649574193797169610525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97231099716129198113073683 145846649574193797169610525)
  ·
    refine ⟨54692493590322673938603947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145846649574193797169610525 54692493590322673938603947)
    ·
      refine ⟨82038740385484010907905921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54692493590322673938603947 82038740385484010907905921)
      ·
        refine ⟨61529055289113008180929441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82038740385484010907905921 61529055289113008180929441)
        ·
          refine ⟨46146791466834756135697081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61529055289113008180929441 46146791466834756135697081)
          ·
            refine ⟨34610093600126067101772811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46146791466834756135697081 34610093600126067101772811)
            ·
              refine ⟨51915140400189100652659217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34610093600126067101772811 51915140400189100652659217)
              ·
                refine ⟨38936355300141825489494413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51915140400189100652659217 38936355300141825489494413)
                ·
                  refine ⟨14601133237553184558560405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38936355300141825489494413 14601133237553184558560405)
                  ·
                    refine ⟨684428120510305526182519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14601133237553184558560405 684428120510305526182519)
                    ·
                      rfl

theorem cell23_3998757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_3998757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998757 prefixEnd_3998757 := by exact prefixLift 3998757
  have htrace : WordTrace (prefixWord ++ tailWord_3998757) baseStart_3998757 baseEnd_3998757 := by
    simpa [prefixWord, tailWord_3998757, baseEnd_3998757] using wordTrace_append hprefix tailTrace_3998757
  have hstable : (prefixWord ++ tailWord_3998757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998757).length < 2 ^ (prefixWord ++ tailWord_3998757).sum := by decide
  have hdescent : baseEnd_3998757 < baseStart_3998757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998784 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3]
def baseStart_3998784 : Nat := 118140960795 + 3998784 * 2 ^ 59
def prefixEnd_3998784 : Nat := 4983230072969 + 3 ^ 40 * 3998784 * 2
def baseEnd_3998784 : Nat := 2053298225508587972909933

theorem tailTrace_3998784 : CollatzResearch.WordTrace tailWord_3998784 prefixEnd_3998784 2053298225508587972909933 := by
  unfold tailWord_3998784
  simp only [CollatzResearch.WordTrace]
  refine ⟨72923817172547990390421703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97231756230063987187228937 72923817172547990390421703)
  ·
    refine ⟨109385725758821985585632555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72923817172547990390421703 109385725758821985585632555)
    ·
      refine ⟨164078588638232978378448833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109385725758821985585632555 164078588638232978378448833)
      ·
        refine ⟨123058941478674733783836625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164078588638232978378448833 123058941478674733783836625)
        ·
          refine ⟨92294206109006050337877469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123058941478674733783836625 92294206109006050337877469)
          ·
            refine ⟨34610327290877268876704051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92294206109006050337877469 34610327290877268876704051)
            ·
              refine ⟨51915490936315903315056077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34610327290877268876704051 51915490936315903315056077)
              ·
                refine ⟨19468309101118463743146029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51915490936315903315056077 19468309101118463743146029)
                ·
                  refine ⟨7300615912919423903679761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19468309101118463743146029 7300615912919423903679761)
                  ·
                    refine ⟨5475461934689567927759821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7300615912919423903679761 5475461934689567927759821)
                    ·
                      refine ⟨2053298225508587972909933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5475461934689567927759821 2053298225508587972909933)
                      ·
                        rfl

theorem cell23_3998784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_3998784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998784 prefixEnd_3998784 := by exact prefixLift 3998784
  have htrace : WordTrace (prefixWord ++ tailWord_3998784) baseStart_3998784 baseEnd_3998784 := by
    simpa [prefixWord, tailWord_3998784, baseEnd_3998784] using wordTrace_append hprefix tailTrace_3998784
  have hstable : (prefixWord ++ tailWord_3998784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998784).length < 2 ^ (prefixWord ++ tailWord_3998784).sum := by decide
  have hdescent : baseEnd_3998784 < baseStart_3998784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998785 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_3998785 : Nat := 118140960795 + 3998785 * 2 ^ 59
def prefixEnd_3998785 : Nat := 4983230072969 + 3 ^ 40 * 3998785 * 2
def baseEnd_3998785 : Nat := 2053298738989242468997429

theorem tailTrace_3998785 : CollatzResearch.WordTrace tailWord_3998785 prefixEnd_3998785 2053298738989242468997429 := by
  unfold tailWord_3998785
  simp only [CollatzResearch.WordTrace]
  refine ⟨145847670818092357951629809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97231780545394905301086539 145847670818092357951629809)
  ·
    refine ⟨109385753113569268463722357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145847670818092357951629809 109385753113569268463722357)
    ·
      refine ⟨10254914354397118918473971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109385753113569268463722357 10254914354397118918473971)
      ·
        refine ⟨15382371531595678377710957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10254914354397118918473971 15382371531595678377710957)
        ·
          refine ⟨5768389324348379391641609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15382371531595678377710957 5768389324348379391641609)
          ·
            refine ⟨4326291993261284543731207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5768389324348379391641609 4326291993261284543731207)
            ·
              refine ⟨6489437989891926815596811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326291993261284543731207 6489437989891926815596811)
              ·
                refine ⟨9734156984837890223395217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6489437989891926815596811 9734156984837890223395217)
                ·
                  refine ⟨7300617738628417667546413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9734156984837890223395217 7300617738628417667546413)
                  ·
                    refine ⟨2737731651985656625329905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7300617738628417667546413 2737731651985656625329905)
                    ·
                      refine ⟨2053298738989242468997429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2737731651985656625329905 2053298738989242468997429)
                      ·
                        rfl

theorem cell23_3998785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_3998785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998785 prefixEnd_3998785 := by exact prefixLift 3998785
  have htrace : WordTrace (prefixWord ++ tailWord_3998785) baseStart_3998785 baseEnd_3998785 := by
    simpa [prefixWord, tailWord_3998785, baseEnd_3998785] using wordTrace_append hprefix tailTrace_3998785
  have hstable : (prefixWord ++ tailWord_3998785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998785).length < 2 ^ (prefixWord ++ tailWord_3998785).sum := by decide
  have hdescent : baseEnd_3998785 < baseStart_3998785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998794 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_3998794 : Nat := 118140960795 + 3998794 * 2 ^ 59
def prefixEnd_3998794 : Nat := 4983230072969 + 3 ^ 40 * 3998794 * 2
def baseEnd_3998794 : Nat := 2053303360315132933784887

theorem tailTrace_3998794 : CollatzResearch.WordTrace tailWord_3998794 prefixEnd_3998794 2053303360315132933784887 := by
  unfold tailWord_3998794
  simp only [CollatzResearch.WordTrace]
  refine ⟨36461999768764938122176859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97231999383373168325804957 36461999768764938122176859)
  ·
    refine ⟨54692999653147407183265289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36461999768764938122176859 54692999653147407183265289)
    ·
      refine ⟨41019749739860555387448967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54692999653147407183265289 41019749739860555387448967)
      ·
        refine ⟨61529624609790833081173451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41019749739860555387448967 61529624609790833081173451)
        ·
          refine ⟨92294436914686249621760177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61529624609790833081173451 92294436914686249621760177)
          ·
            refine ⟨69220827686014687216320133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92294436914686249621760177 69220827686014687216320133)
            ·
              refine ⟨12978905191127753853060025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69220827686014687216320133 12978905191127753853060025)
              ·
                refine ⟨9734178893345815389795019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12978905191127753853060025 9734178893345815389795019)
                ·
                  refine ⟨14601268340018723084692529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9734178893345815389795019 14601268340018723084692529)
                  ·
                    refine ⟨10950951255014042313519397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14601268340018723084692529 10950951255014042313519397)
                    ·
                      refine ⟨2053303360315132933784887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10950951255014042313519397 2053303360315132933784887)
                      ·
                        rfl

theorem cell23_3998794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_3998794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998794 prefixEnd_3998794 := by exact prefixLift 3998794
  have htrace : WordTrace (prefixWord ++ tailWord_3998794) baseStart_3998794 baseEnd_3998794 := by
    simpa [prefixWord, tailWord_3998794, baseEnd_3998794] using wordTrace_append hprefix tailTrace_3998794
  have hstable : (prefixWord ++ tailWord_3998794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998794).length < 2 ^ (prefixWord ++ tailWord_3998794).sum := by decide
  have hdescent : baseEnd_3998794 < baseStart_3998794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998807 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3998807 : Nat := 118140960795 + 3998807 * 2 ^ 59
def prefixEnd_3998807 : Nat := 4983230072969 + 3 ^ 40 * 3998807 * 2
def baseEnd_3998807 : Nat := 2053310035563641382922327

theorem tailTrace_3998807 : CollatzResearch.WordTrace tailWord_3998807 prefixEnd_3998807 2053310035563641382922327 := by
  unfold tailWord_3998807
  simp only [CollatzResearch.WordTrace]
  refine ⟨145848473224012655708930675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97232315482675103805953783 145848473224012655708930675)
  ·
    refine ⟨218772709836018983563396013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145848473224012655708930675 218772709836018983563396013)
    ·
      refine ⟨82039766188507118836273505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218772709836018983563396013 82039766188507118836273505)
      ·
        refine ⟨61529824641380339127205129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82039766188507118836273505 61529824641380339127205129)
        ·
          refine ⟨46147368481035254345403847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61529824641380339127205129 46147368481035254345403847)
          ·
            refine ⟨69221052721552881518105771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46147368481035254345403847 69221052721552881518105771)
            ·
              refine ⟨103831579082329322277158657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69221052721552881518105771 103831579082329322277158657)
              ·
                refine ⟨77873684311746991707868993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103831579082329322277158657 77873684311746991707868993)
                ·
                  refine ⟨58405263233810243780901745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77873684311746991707868993 58405263233810243780901745)
                  ·
                    refine ⟨43803947425357682835676309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58405263233810243780901745 43803947425357682835676309)
                    ·
                      refine ⟨2053310035563641382922327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43803947425357682835676309 2053310035563641382922327)
                      ·
                        rfl

theorem cell23_3998807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3998807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998807 prefixEnd_3998807 := by exact prefixLift 3998807
  have htrace : WordTrace (prefixWord ++ tailWord_3998807) baseStart_3998807 baseEnd_3998807 := by
    simpa [prefixWord, tailWord_3998807, baseEnd_3998807] using wordTrace_append hprefix tailTrace_3998807
  have hstable : (prefixWord ++ tailWord_3998807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998807).length < 2 ^ (prefixWord ++ tailWord_3998807).sum := by decide
  have hdescent : baseEnd_3998807 < baseStart_3998807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998817 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3998817 : Nat := 118140960795 + 3998817 * 2 ^ 59
def prefixEnd_3998817 : Nat := 4983230072969 + 3 ^ 40 * 3998817 * 2
def baseEnd_3998817 : Nat := 684438390123395447932427

theorem tailTrace_3998817 : CollatzResearch.WordTrace tailWord_3998817 prefixEnd_3998817 684438390123395447932427 := by
  unfold tailWord_3998817
  simp only [CollatzResearch.WordTrace]
  refine ⟨145848837953976427416794705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97232558635984284944529803 145848837953976427416794705)
  ·
    refine ⟨109386628465482320562596029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145848837953976427416794705 109386628465482320562596029)
    ·
      refine ⟨41019985674555870210973511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109386628465482320562596029 41019985674555870210973511)
      ·
        refine ⟨61529978511833805316460267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41019985674555870210973511 61529978511833805316460267)
        ·
          refine ⟨92294967767750707974690401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61529978511833805316460267 92294967767750707974690401)
          ·
            refine ⟨69221225825813030981017801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92294967767750707974690401 69221225825813030981017801)
            ·
              refine ⟨51915919369359773235763351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69221225825813030981017801 51915919369359773235763351)
              ·
                refine ⟨77873879054039659853645027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51915919369359773235763351 77873879054039659853645027)
                ·
                  refine ⟨116810818581059489780467541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77873879054039659853645027 116810818581059489780467541)
                  ·
                    refine ⟨684438390123395447932427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116810818581059489780467541 684438390123395447932427)
                    ·
                      rfl

theorem cell23_3998817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3998817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998817 prefixEnd_3998817 := by exact prefixLift 3998817
  have htrace : WordTrace (prefixWord ++ tailWord_3998817) baseStart_3998817 baseEnd_3998817 := by
    simpa [prefixWord, tailWord_3998817, baseEnd_3998817] using wordTrace_append hprefix tailTrace_3998817
  have hstable : (prefixWord ++ tailWord_3998817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998817).length < 2 ^ (prefixWord ++ tailWord_3998817).sum := by decide
  have hdescent : baseEnd_3998817 < baseStart_3998817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998827 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5]
def baseStart_3998827 : Nat := 118140960795 + 3998827 * 2 ^ 59
def prefixEnd_3998827 : Nat := 4983230072969 + 3 ^ 40 * 3998827 * 2
def baseEnd_3998827 : Nat := 2053320305176731304672235

theorem tailTrace_3998827 : CollatzResearch.WordTrace tailWord_3998827 prefixEnd_3998827 2053320305176731304672235 := by
  unfold tailWord_3998827
  simp only [CollatzResearch.WordTrace]
  refine ⟨145849202683940199124658735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97232801789293466083105823 145849202683940199124658735)
  ·
    refine ⟨218773804025910298686988103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145849202683940199124658735 218773804025910298686988103)
    ·
      refine ⟨328160706038865448030482155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218773804025910298686988103 328160706038865448030482155)
      ·
        refine ⟨492241059058298172045723233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328160706038865448030482155 492241059058298172045723233)
        ·
          refine ⟨369180794293723629034292425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492241059058298172045723233 369180794293723629034292425)
          ·
            refine ⟨276885595720292721775719319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369180794293723629034292425 276885595720292721775719319)
            ·
              refine ⟨415328393580439082663578979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276885595720292721775719319 415328393580439082663578979)
              ·
                refine ⟨622992590370658623995368469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415328393580439082663578979 622992590370658623995368469)
                ·
                  refine ⟨29202777673624622999782897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 622992590370658623995368469 29202777673624622999782897)
                  ·
                    refine ⟨21902083255218467249837173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29202777673624622999782897 21902083255218467249837173)
                    ·
                      refine ⟨2053320305176731304672235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21902083255218467249837173 2053320305176731304672235)
                      ·
                        rfl

theorem cell23_3998827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_3998827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998827 prefixEnd_3998827 := by exact prefixLift 3998827
  have htrace : WordTrace (prefixWord ++ tailWord_3998827) baseStart_3998827 baseEnd_3998827 := by
    simpa [prefixWord, tailWord_3998827, baseEnd_3998827] using wordTrace_append hprefix tailTrace_3998827
  have hstable : (prefixWord ++ tailWord_3998827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998827).length < 2 ^ (prefixWord ++ tailWord_3998827).sum := by decide
  have hdescent : baseEnd_3998827 < baseStart_3998827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998858 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_3998858 : Nat := 118140960795 + 3998858 * 2 ^ 59
def prefixEnd_3998858 : Nat := 4983230072969 + 3 ^ 40 * 3998858 * 2
def baseEnd_3998858 : Nat := 2053336223077020683384593

theorem tailTrace_3998858 : CollatzResearch.WordTrace tailWord_3998858 prefixEnd_3998858 2053336223077020683384593 := by
  unfold tailWord_3998858
  simp only [CollatzResearch.WordTrace]
  refine ⟨36462583336706972854759307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97233555564551927612691485 36462583336706972854759307)
  ·
    refine ⟨54693875005060459282138961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36462583336706972854759307 54693875005060459282138961)
    ·
      refine ⟨41020406253795344461604221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54693875005060459282138961 41020406253795344461604221)
      ·
        refine ⟨15382652345173254173101583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41020406253795344461604221 15382652345173254173101583)
        ·
          refine ⟨23073978517759881259652375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15382652345173254173101583 23073978517759881259652375)
          ·
            refine ⟨34610967776639821889478563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23073978517759881259652375 34610967776639821889478563)
            ·
              refine ⟨51916451664959732834217845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34610967776639821889478563 51916451664959732834217845)
              ·
                refine ⟨4867167343589974953207923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51916451664959732834217845 4867167343589974953207923)
                ·
                  refine ⟨7300751015384962429811885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867167343589974953207923 7300751015384962429811885)
                  ·
                    refine ⟨2737781630769360911179457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7300751015384962429811885 2737781630769360911179457)
                    ·
                      refine ⟨2053336223077020683384593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2737781630769360911179457 2053336223077020683384593)
                      ·
                        rfl

theorem cell23_3998858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_3998858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998858 prefixEnd_3998858 := by exact prefixLift 3998858
  have htrace : WordTrace (prefixWord ++ tailWord_3998858) baseStart_3998858 baseEnd_3998858 := by
    simpa [prefixWord, tailWord_3998858, baseEnd_3998858] using wordTrace_append hprefix tailTrace_3998858
  have hstable : (prefixWord ++ tailWord_3998858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998858).length < 2 ^ (prefixWord ++ tailWord_3998858).sum := by decide
  have hdescent : baseEnd_3998858 < baseStart_3998858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998904 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_3998904 : Nat := 118140960795 + 3998904 * 2 ^ 59
def prefixEnd_3998904 : Nat := 4983230072969 + 3 ^ 40 * 3998904 * 2
def baseEnd_3998904 : Nat := 2053359843187127503409381

theorem tailTrace_3998904 : CollatzResearch.WordTrace tailWord_3998904 prefixEnd_3998904 2053359843187127503409381 := by
  unfold tailWord_3998904
  simp only [CollatzResearch.WordTrace]
  refine ⟨72926005552330620637605883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97234674069774160850141177 72926005552330620637605883)
  ·
    refine ⟨109389008328495930956408825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72926005552330620637605883 109389008328495930956408825)
    ·
      refine ⟨82041756246371948217306619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109389008328495930956408825 82041756246371948217306619)
      ·
        refine ⟨123062634369557922325959929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82041756246371948217306619 123062634369557922325959929)
        ·
          refine ⟨92296975777168441744469947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123062634369557922325959929 92296975777168441744469947)
          ·
            refine ⟨138445463665752662616704921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92296975777168441744469947 138445463665752662616704921)
            ·
              refine ⟨103834097749314496962528691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138445463665752662616704921 103834097749314496962528691)
              ·
                refine ⟨155751146623971745443793037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103834097749314496962528691 155751146623971745443793037)
                ·
                  refine ⟨58406679983989404541422389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155751146623971745443793037 58406679983989404541422389)
                  ·
                    refine ⟨5475626248499006675758349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58406679983989404541422389 5475626248499006675758349)
                    ·
                      refine ⟨2053359843187127503409381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5475626248499006675758349 2053359843187127503409381)
                      ·
                        rfl

theorem cell23_3998904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_3998904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998904 prefixEnd_3998904 := by exact prefixLift 3998904
  have htrace : WordTrace (prefixWord ++ tailWord_3998904) baseStart_3998904 baseEnd_3998904 := by
    simpa [prefixWord, tailWord_3998904, baseEnd_3998904] using wordTrace_append hprefix tailTrace_3998904
  have hstable : (prefixWord ++ tailWord_3998904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998904).length < 2 ^ (prefixWord ++ tailWord_3998904).sum := by decide
  have hdescent : baseEnd_3998904 < baseStart_3998904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998961 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 3, 6, 2]
def baseStart_3998961 : Nat := 118140960795 + 3998961 * 2 ^ 59
def prefixEnd_3998961 : Nat := 4983230072969 + 3 ^ 40 * 3998961 * 2
def baseEnd_3998961 : Nat := 2053389111584433780396619

theorem tailTrace_3998961 : CollatzResearch.WordTrace tailWord_3998961 prefixEnd_3998961 2053389111584433780396619 := by
  unfold tailWord_3998961
  simp only [CollatzResearch.WordTrace]
  refine ⟨145854090065454740010036737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97236060043636493340024491 145854090065454740010036737)
  ·
    refine ⟨109390567549091055007527553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145854090065454740010036737 109390567549091055007527553)
    ·
      refine ⟨82042925661818291255645665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109390567549091055007527553 82042925661818291255645665)
      ·
        refine ⟨61532194246363718441734249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82042925661818291255645665 61532194246363718441734249)
        ·
          refine ⟨46149145684772788831300687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61532194246363718441734249 46149145684772788831300687)
          ·
            refine ⟨69223718527159183246951031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46149145684772788831300687 69223718527159183246951031)
            ·
              refine ⟨103835577790738774870426547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69223718527159183246951031 103835577790738774870426547)
              ·
                refine ⟨155753366686108162305639821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103835577790738774870426547 155753366686108162305639821)
                ·
                  refine ⟨58407512507290560864614933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155753366686108162305639821 58407512507290560864614933)
                  ·
                    refine ⟨2737852148779245040528825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58407512507290560864614933 2737852148779245040528825)
                    ·
                      refine ⟨2053389111584433780396619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2737852148779245040528825 2053389111584433780396619)
                      ·
                        rfl

theorem cell23_3998961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_3998961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998961 prefixEnd_3998961 := by exact prefixLift 3998961
  have htrace : WordTrace (prefixWord ++ tailWord_3998961) baseStart_3998961 baseEnd_3998961 := by
    simpa [prefixWord, tailWord_3998961, baseEnd_3998961] using wordTrace_append hprefix tailTrace_3998961
  have hstable : (prefixWord ++ tailWord_3998961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998961).length < 2 ^ (prefixWord ++ tailWord_3998961).sum := by decide
  have hdescent : baseEnd_3998961 < baseStart_3998961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998981 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_3998981 : Nat := 118140960795 + 3998981 * 2 ^ 59
def prefixEnd_3998981 : Nat := 4983230072969 + 3 ^ 40 * 3998981 * 2
def baseEnd_3998981 : Nat := 2053399381197523702146527

theorem tailTrace_3998981 : CollatzResearch.WordTrace tailWord_3998981 prefixEnd_3998981 2053399381197523702146527 := by
  unfold tailWord_3998981
  simp only [CollatzResearch.WordTrace]
  refine ⟨145854819525382283425764797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97236546350254855617176531 145854819525382283425764797)
  ·
    refine ⟨54695557322018356284661799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145854819525382283425764797 54695557322018356284661799)
    ·
      refine ⟨82043335983027534426992699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54695557322018356284661799 82043335983027534426992699)
      ·
        refine ⟨123065003974541301640489049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82043335983027534426992699 123065003974541301640489049)
        ·
          refine ⟨92298752980905976230366787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123065003974541301640489049 92298752980905976230366787)
          ·
            refine ⟨138448129471358964345550181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92298752980905976230366787 138448129471358964345550181)
            ·
              refine ⟨25959024275879805814790659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138448129471358964345550181 25959024275879805814790659)
              ·
                refine ⟨38938536413819708722185989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25959024275879805814790659 38938536413819708722185989)
                ·
                  refine ⟨7300975577591195385409873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38938536413819708722185989 7300975577591195385409873)
                  ·
                    refine ⟨5475731683193396539057405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7300975577591195385409873 5475731683193396539057405)
                    ·
                      refine ⟨2053399381197523702146527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5475731683193396539057405 2053399381197523702146527)
                      ·
                        rfl

theorem cell23_3998981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_3998981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998981 prefixEnd_3998981 := by exact prefixLift 3998981
  have htrace : WordTrace (prefixWord ++ tailWord_3998981) baseStart_3998981 baseEnd_3998981 := by
    simpa [prefixWord, tailWord_3998981, baseEnd_3998981] using wordTrace_append hprefix tailTrace_3998981
  have hstable : (prefixWord ++ tailWord_3998981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998981).length < 2 ^ (prefixWord ++ tailWord_3998981).sum := by decide
  have hdescent : baseEnd_3998981 < baseStart_3998981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3998988 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_3998988 : Nat := 118140960795 + 3998988 * 2 ^ 59
def prefixEnd_3998988 : Nat := 4983230072969 + 3 ^ 40 * 3998988 * 2
def baseEnd_3998988 : Nat := 684467658520701724919665

theorem tailTrace_3998988 : CollatzResearch.WordTrace tailWord_3998988 prefixEnd_3998988 684467658520701724919665 := by
  unfold tailWord_3998988
  simp only [CollatzResearch.WordTrace]
  refine ⟨72927537418178461810634809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97236716557571282414179745 72927537418178461810634809)
  ·
    refine ⟨54695653063633846357976107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72927537418178461810634809 54695653063633846357976107)
    ·
      refine ⟨82043479595450769536964161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54695653063633846357976107 82043479595450769536964161)
      ·
        refine ⟨61532609696588077152723121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82043479595450769536964161 61532609696588077152723121)
        ·
          refine ⟨46149457272441057864542341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61532609696588077152723121 46149457272441057864542341)
          ·
            refine ⟨8653023238582698349601689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46149457272441057864542341 8653023238582698349601689)
            ·
              refine ⟨6489767428937023762201267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653023238582698349601689 6489767428937023762201267)
              ·
                refine ⟨9734651143405535643301901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6489767428937023762201267 9734651143405535643301901)
                ·
                  refine ⟨3650494178777075866238213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9734651143405535643301901 3650494178777075866238213)
                  ·
                    refine ⟨684467658520701724919665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3650494178777075866238213 684467658520701724919665)
                    ·
                      rfl

theorem cell23_3998988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_3998988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3998988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3998988 prefixEnd_3998988 := by exact prefixLift 3998988
  have htrace : WordTrace (prefixWord ++ tailWord_3998988) baseStart_3998988 baseEnd_3998988 := by
    simpa [prefixWord, tailWord_3998988, baseEnd_3998988] using wordTrace_append hprefix tailTrace_3998988
  have hstable : (prefixWord ++ tailWord_3998988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3998988).length < 2 ^ (prefixWord ++ tailWord_3998988).sum := by decide
  have hdescent : baseEnd_3998988 < baseStart_3998988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3998988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999045 : List Nat := [1, 3, 1, 1, 1, 2, 1, 8, 1, 1, 3]
def baseStart_3999045 : Nat := 118140960795 + 3999045 * 2 ^ 59
def prefixEnd_3999045 : Nat := 4983230072969 + 3 ^ 40 * 3999045 * 2
def baseEnd_3999045 : Nat := 2053432243959411451746233

theorem tailTrace_3999045 : CollatzResearch.WordTrace tailWord_3999045 prefixEnd_3999045 2053432243959411451746233 := by
  unfold tailWord_3999045
  simp only [CollatzResearch.WordTrace]
  refine ⟨145857153797150422356094589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97238102531433614904063059 145857153797150422356094589)
  ·
    refine ⟨54696432673931408383535471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145857153797150422356094589 54696432673931408383535471)
    ·
      refine ⟨82044649010897112575303207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54696432673931408383535471 82044649010897112575303207)
      ·
        refine ⟨123066973516345668862954811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82044649010897112575303207 123066973516345668862954811)
        ·
          refine ⟨184600460274518503294432217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123066973516345668862954811 184600460274518503294432217)
          ·
            refine ⟨138450345205888877470824163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184600460274518503294432217 138450345205888877470824163)
            ·
              refine ⟨207675517808833316206236245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138450345205888877470824163 207675517808833316206236245)
              ·
                refine ⟨2433697474322265424291831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 207675517808833316206236245 2433697474322265424291831)
                ·
                  refine ⟨3650546211483398136437747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433697474322265424291831 3650546211483398136437747)
                  ·
                    refine ⟨5475819317225097204656621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3650546211483398136437747 5475819317225097204656621)
                    ·
                      refine ⟨2053432243959411451746233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5475819317225097204656621 2053432243959411451746233)
                      ·
                        rfl

theorem cell23_3999045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_3999045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999045 prefixEnd_3999045 := by exact prefixLift 3999045
  have htrace : WordTrace (prefixWord ++ tailWord_3999045) baseStart_3999045 baseEnd_3999045 := by
    simpa [prefixWord, tailWord_3999045, baseEnd_3999045] using wordTrace_append hprefix tailTrace_3999045
  have hstable : (prefixWord ++ tailWord_3999045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999045).length < 2 ^ (prefixWord ++ tailWord_3999045).sum := by decide
  have hdescent : baseEnd_3999045 < baseStart_3999045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999082 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_3999082 : Nat := 118140960795 + 3999082 * 2 ^ 59
def prefixEnd_3999082 : Nat := 4983230072969 + 3 ^ 40 * 3999082 * 2
def baseEnd_3999082 : Nat := 684483747581209268994521

theorem tailTrace_3999082 : CollatzResearch.WordTrace tailWord_3999082 prefixEnd_3999082 684483747581209268994521 := by
  unfold tailWord_3999082
  simp only [CollatzResearch.WordTrace]
  refine ⟨36464625824504094418797875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97239002198677585116794333 36464625824504094418797875)
  ·
    refine ⟨54696938736756141628196813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36464625824504094418797875 54696938736756141628196813)
    ·
      refine ⟨20511352026283553110573805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54696938736756141628196813 20511352026283553110573805)
      ·
        refine ⟨7691757009856332416465177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20511352026283553110573805 7691757009856332416465177)
        ·
          refine ⟨5768817757392249312348883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7691757009856332416465177 5768817757392249312348883)
          ·
            refine ⟨8653226636088373968523325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768817757392249312348883 8653226636088373968523325)
            ·
              refine ⟨3244959988533140238196247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8653226636088373968523325 3244959988533140238196247)
              ·
                refine ⟨4867439982799710357294371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244959988533140238196247 4867439982799710357294371)
                ·
                  refine ⟨7301159974199565535941557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867439982799710357294371 7301159974199565535941557)
                  ·
                    refine ⟨684483747581209268994521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7301159974199565535941557 684483747581209268994521)
                    ·
                      rfl

theorem cell23_3999082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_3999082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999082 prefixEnd_3999082 := by exact prefixLift 3999082
  have htrace : WordTrace (prefixWord ++ tailWord_3999082) baseStart_3999082 baseEnd_3999082 := by
    simpa [prefixWord, tailWord_3999082, baseEnd_3999082] using wordTrace_append hprefix tailTrace_3999082
  have hstable : (prefixWord ++ tailWord_3999082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999082).length < 2 ^ (prefixWord ++ tailWord_3999082).sum := by decide
  have hdescent : baseEnd_3999082 < baseStart_3999082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999108 : List Nat := [2, 3, 2, 1, 1, 5, 1, 8]
def baseStart_3999108 : Nat := 118140960795 + 3999108 * 2 ^ 59
def prefixEnd_3999108 : Nat := 4983230072969 + 3 ^ 40 * 3999108 * 2
def baseEnd_3999108 : Nat := 76054244194097952046609

theorem tailTrace_3999108 : CollatzResearch.WordTrace tailWord_3999108 prefixEnd_3999108 76054244194097952046609 := by
  unfold tailWord_3999108
  simp only [CollatzResearch.WordTrace]
  refine ⟨72929725797961092057818989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97239634397281456077091985 72929725797961092057818989)
  ·
    refine ⟨27348647174235409521682121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72929725797961092057818989 27348647174235409521682121)
    ·
      refine ⟨20511485380676557141261591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27348647174235409521682121 20511485380676557141261591)
      ·
        refine ⟨30767228071014835711892387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20511485380676557141261591 30767228071014835711892387)
        ·
          refine ⟨46150842106522253567838581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30767228071014835711892387 46150842106522253567838581)
          ·
            refine ⟨4326641447486461271984867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46150842106522253567838581 4326641447486461271984867)
            ·
              refine ⟨6489962171229691907977301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326641447486461271984867 6489962171229691907977301)
              ·
                refine ⟨76054244194097952046609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6489962171229691907977301 76054244194097952046609)
                ·
                  rfl

theorem cell23_3999108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 8].length) (baseStart_3999108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999108 prefixEnd_3999108 := by exact prefixLift 3999108
  have htrace : WordTrace (prefixWord ++ tailWord_3999108) baseStart_3999108 baseEnd_3999108 := by
    simpa [prefixWord, tailWord_3999108, baseEnd_3999108] using wordTrace_append hprefix tailTrace_3999108
  have hstable : (prefixWord ++ tailWord_3999108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999108).length < 2 ^ (prefixWord ++ tailWord_3999108).sum := by decide
  have hdescent : baseEnd_3999108 < baseStart_3999108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999141 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3999141 : Nat := 118140960795 + 3999141 * 2 ^ 59
def prefixEnd_3999141 : Nat := 4983230072969 + 3 ^ 40 * 3999141 * 2
def baseEnd_3999141 : Nat := 2053481538102243076145791

theorem tailTrace_3999141 : CollatzResearch.WordTrace tailWord_3999141 prefixEnd_3999141 2053481538102243076145791 := by
  unfold tailWord_3999141
  simp only [CollatzResearch.WordTrace]
  refine ⟨145860655204802630751589277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97240436803201753834392851 145860655204802630751589277)
  ·
    refine ⟨54697745701800986531845979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145860655204802630751589277 54697745701800986531845979)
    ·
      refine ⟨82046618552701479797768969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54697745701800986531845979 82046618552701479797768969)
      ·
        refine ⟨61534963914526109848326727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82046618552701479797768969 61534963914526109848326727)
        ·
          refine ⟨92302445871789164772490091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61534963914526109848326727 92302445871789164772490091)
          ·
            refine ⟨138453668807683747158735137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92302445871789164772490091 138453668807683747158735137)
            ·
              refine ⟨103840251605762810369051353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138453668807683747158735137 103840251605762810369051353)
              ·
                refine ⟨77880188704322107776788515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103840251605762810369051353 77880188704322107776788515)
                ·
                  refine ⟨116820283056483161665182773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77880188704322107776788515 116820283056483161665182773)
                  ·
                    refine ⟨10951901536545296406110885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116820283056483161665182773 10951901536545296406110885)
                    ·
                      refine ⟨2053481538102243076145791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10951901536545296406110885 2053481538102243076145791)
                      ·
                        rfl

theorem cell23_3999141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3999141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999141 prefixEnd_3999141 := by exact prefixLift 3999141
  have htrace : WordTrace (prefixWord ++ tailWord_3999141) baseStart_3999141 baseEnd_3999141 := by
    simpa [prefixWord, tailWord_3999141, baseEnd_3999141] using wordTrace_append hprefix tailTrace_3999141
  have hstable : (prefixWord ++ tailWord_3999141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999141).length < 2 ^ (prefixWord ++ tailWord_3999141).sum := by decide
  have hdescent : baseEnd_3999141 < baseStart_3999141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999211 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 3, 7]
def baseStart_3999211 : Nat := 118140960795 + 3999211 * 2 ^ 59
def prefixEnd_3999211 : Nat := 4983230072969 + 3 ^ 40 * 3999211 * 2
def baseEnd_3999211 : Nat := 684505827249352600756823

theorem tailTrace_3999211 : CollatzResearch.WordTrace tailWord_3999211 prefixEnd_3999211 684505827249352600756823 := by
  unfold tailWord_3999211
  simp only [CollatzResearch.WordTrace]
  refine ⟨145863208314549032706637487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97242138876366021804424991 145863208314549032706637487)
  ·
    refine ⟨218794812471823549059956231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145863208314549032706637487 218794812471823549059956231)
    ·
      refine ⟨328192218707735323589934347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218794812471823549059956231 328192218707735323589934347)
      ·
        refine ⟨492288328061602985384901521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328192218707735323589934347 492288328061602985384901521)
        ·
          refine ⟨369216246046202239038676141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492288328061602985384901521 369216246046202239038676141)
          ·
            refine ⟨138456092267325839639503553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369216246046202239038676141 138456092267325839639503553)
            ·
              refine ⟨103842069200494379729627665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138456092267325839639503553 103842069200494379729627665)
              ·
                refine ⟨77881551900370784797220749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103842069200494379729627665 77881551900370784797220749)
                ·
                  refine ⟨29205581962639044298957781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77881551900370784797220749 29205581962639044298957781)
                  ·
                    refine ⟨684505827249352600756823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29205581962639044298957781 684505827249352600756823)
                    ·
                      rfl

theorem cell23_3999211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_3999211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999211 prefixEnd_3999211 := by exact prefixLift 3999211
  have htrace : WordTrace (prefixWord ++ tailWord_3999211) baseStart_3999211 baseEnd_3999211 := by
    simpa [prefixWord, tailWord_3999211, baseEnd_3999211] using wordTrace_append hprefix tailTrace_3999211
  have hstable : (prefixWord ++ tailWord_3999211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999211).length < 2 ^ (prefixWord ++ tailWord_3999211).sum := by decide
  have hdescent : baseEnd_3999211 < baseStart_3999211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999265 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3999265 : Nat := 118140960795 + 3999265 * 2 ^ 59
def prefixEnd_3999265 : Nat := 4983230072969 + 3 ^ 40 * 3999265 * 2
def baseEnd_3999265 : Nat := 2053545209703400590995221

theorem tailTrace_3999265 : CollatzResearch.WordTrace tailWord_3999265 prefixEnd_3999265 2053545209703400590995221 := by
  unfold tailWord_3999265
  simp only [CollatzResearch.WordTrace]
  refine ⟨145865177856353399929103249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97243451904235599952735499 145865177856353399929103249)
  ·
    refine ⟨109398883392265049946827437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145865177856353399929103249 109398883392265049946827437)
    ·
      refine ⟨41024581272099393730060289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109398883392265049946827437 41024581272099393730060289)
      ·
        refine ⟨30768435954074545297545217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41024581272099393730060289 30768435954074545297545217)
        ·
          refine ⟨23076326965555908973158913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30768435954074545297545217 23076326965555908973158913)
          ·
            refine ⟨17307245224166931729869185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23076326965555908973158913 17307245224166931729869185)
            ·
              refine ⟨12980433918125198797401889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17307245224166931729869185 12980433918125198797401889)
              ·
                refine ⟨9735325438593899098051417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12980433918125198797401889 9735325438593899098051417)
                ·
                  refine ⟨7301494078945424323538563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9735325438593899098051417 7301494078945424323538563)
                  ·
                    refine ⟨10952241118418136485307845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7301494078945424323538563 10952241118418136485307845)
                    ·
                      refine ⟨2053545209703400590995221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10952241118418136485307845 2053545209703400590995221)
                      ·
                        rfl

theorem cell23_3999265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3999265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999265 prefixEnd_3999265 := by exact prefixLift 3999265
  have htrace : WordTrace (prefixWord ++ tailWord_3999265) baseStart_3999265 baseEnd_3999265 := by
    simpa [prefixWord, tailWord_3999265, baseEnd_3999265] using wordTrace_append hprefix tailTrace_3999265
  have hstable : (prefixWord ++ tailWord_3999265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999265).length < 2 ^ (prefixWord ++ tailWord_3999265).sum := by decide
  have hdescent : baseEnd_3999265 < baseStart_3999265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999292 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_3999292 : Nat := 118140960795 + 3999292 * 2 ^ 59
def prefixEnd_3999292 : Nat := 4983230072969 + 3 ^ 40 * 3999292 * 2
def baseEnd_3999292 : Nat := 684519691227023995119199

theorem tailTrace_3999292 : CollatzResearch.WordTrace tailWord_3999292 prefixEnd_3999292 684519691227023995119199 := by
  unfold tailWord_3999292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72933081313627791770168065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97244108418170389026890753 72933081313627791770168065)
  ·
    refine ⟨54699810985220843827626049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72933081313627791770168065 54699810985220843827626049)
    ·
      refine ⟨41024858238915632870719537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54699810985220843827626049 41024858238915632870719537)
      ·
        refine ⟨30768643679186724653039653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41024858238915632870719537 30768643679186724653039653)
        ·
          refine ⟨5769120689847510872444935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30768643679186724653039653 5769120689847510872444935)
          ·
            refine ⟨8653681034771266308667403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769120689847510872444935 8653681034771266308667403)
            ·
              refine ⟨12980521552156899463001105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8653681034771266308667403 12980521552156899463001105)
              ·
                refine ⟨9735391164117674597250829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12980521552156899463001105 9735391164117674597250829)
                ·
                  refine ⟨3650771686544127973969061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9735391164117674597250829 3650771686544127973969061)
                  ·
                    refine ⟨684519691227023995119199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3650771686544127973969061 684519691227023995119199)
                    ·
                      rfl

theorem cell23_3999292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_3999292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999292 prefixEnd_3999292 := by exact prefixLift 3999292
  have htrace : WordTrace (prefixWord ++ tailWord_3999292) baseStart_3999292 baseEnd_3999292 := by
    simpa [prefixWord, tailWord_3999292, baseEnd_3999292] using wordTrace_append hprefix tailTrace_3999292
  have hstable : (prefixWord ++ tailWord_3999292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999292).length < 2 ^ (prefixWord ++ tailWord_3999292).sum := by decide
  have hdescent : baseEnd_3999292 < baseStart_3999292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999332 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_3999332 : Nat := 118140960795 + 3999332 * 2 ^ 59
def prefixEnd_3999332 : Nat := 4983230072969 + 3 ^ 40 * 3999332 * 2
def baseEnd_3999332 : Nat := 2053579612907251828857413

theorem tailTrace_3999332 : CollatzResearch.WordTrace tailWord_3999332 prefixEnd_3999332 2053579612907251828857413 := by
  unfold tailWord_3999332
  simp only [CollatzResearch.WordTrace]
  refine ⟨72933810773555335185896125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97245081031407113581194833 72933810773555335185896125)
  ·
    refine ⟨27350179040083250694711047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72933810773555335185896125 27350179040083250694711047)
    ·
      refine ⟨41025268560124876042066571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27350179040083250694711047 41025268560124876042066571)
      ·
        refine ⟨61537902840187314063099857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41025268560124876042066571 61537902840187314063099857)
        ·
          refine ⟨46153427130140485547324893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61537902840187314063099857 46153427130140485547324893)
          ·
            refine ⟨17307535173802682080246835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46153427130140485547324893 17307535173802682080246835)
            ·
              refine ⟨25961302760704023120370253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17307535173802682080246835 25961302760704023120370253)
              ·
                refine ⟨9735488535264008670138845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25961302760704023120370253 9735488535264008670138845)
                ·
                  refine ⟨3650808200724003251302067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9735488535264008670138845 3650808200724003251302067)
                  ·
                    refine ⟨5476212301086004876953101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3650808200724003251302067 5476212301086004876953101)
                    ·
                      refine ⟨2053579612907251828857413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476212301086004876953101 2053579612907251828857413)
                      ·
                        rfl

theorem cell23_3999332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_3999332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999332 prefixEnd_3999332 := by exact prefixLift 3999332
  have htrace : WordTrace (prefixWord ++ tailWord_3999332) baseStart_3999332 baseEnd_3999332 := by
    simpa [prefixWord, tailWord_3999332, baseEnd_3999332] using wordTrace_append hprefix tailTrace_3999332
  have hstable : (prefixWord ++ tailWord_3999332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999332).length < 2 ^ (prefixWord ++ tailWord_3999332).sum := by decide
  have hdescent : baseEnd_3999332 < baseStart_3999332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999349 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3999349 : Nat := 118140960795 + 3999349 * 2 ^ 59
def prefixEnd_3999349 : Nat := 4983230072969 + 3 ^ 40 * 3999349 * 2
def baseEnd_3999349 : Nat := 2053588342078378262344835

theorem tailTrace_3999349 : CollatzResearch.WordTrace tailWord_3999349 prefixEnd_3999349 2053588342078378262344835 := by
  unfold tailWord_3999349
  simp only [CollatzResearch.WordTrace]
  refine ⟨145868241588049082275161101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97245494392032721516774067 145868241588049082275161101)
  ·
    refine ⟨54700590595518405853185413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145868241588049082275161101 54700590595518405853185413)
    ·
      refine ⟨10256360736659701097472265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54700590595518405853185413 10256360736659701097472265)
      ·
        refine ⟨7692270552494775823104199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10256360736659701097472265 7692270552494775823104199)
        ·
          refine ⟨11538405828742163734656299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7692270552494775823104199 11538405828742163734656299)
          ·
            refine ⟨17307608743113245601984449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11538405828742163734656299 17307608743113245601984449)
            ·
              refine ⟨12980706557334934201488337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17307608743113245601984449 12980706557334934201488337)
              ·
                refine ⟨9735529918001200651116253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12980706557334934201488337 9735529918001200651116253)
                ·
                  refine ⟨3650823719250450244168595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9735529918001200651116253 3650823719250450244168595)
                  ·
                    refine ⟨5476235578875675366252893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3650823719250450244168595 5476235578875675366252893)
                    ·
                      refine ⟨2053588342078378262344835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476235578875675366252893 2053588342078378262344835)
                      ·
                        rfl

theorem cell23_3999349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3999349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999349 prefixEnd_3999349 := by exact prefixLift 3999349
  have htrace : WordTrace (prefixWord ++ tailWord_3999349) baseStart_3999349 baseEnd_3999349 := by
    simpa [prefixWord, tailWord_3999349, baseEnd_3999349] using wordTrace_append hprefix tailTrace_3999349
  have hstable : (prefixWord ++ tailWord_3999349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999349).length < 2 ^ (prefixWord ++ tailWord_3999349).sum := by decide
  have hdescent : baseEnd_3999349 < baseStart_3999349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999355 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 2, 6, 2]
def baseStart_3999355 : Nat := 118140960795 + 3999355 * 2 ^ 59
def prefixEnd_3999355 : Nat := 4983230072969 + 3 ^ 40 * 3999355 * 2
def baseEnd_3999355 : Nat := 2053591422962305238869807

theorem tailTrace_3999355 : CollatzResearch.WordTrace tailWord_3999355 prefixEnd_3999355 2053591422962305238869807 := by
  unfold tailWord_3999355
  simp only [CollatzResearch.WordTrace]
  refine ⟨145868460426027345299879519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97245640284018230199919679 145868460426027345299879519)
  ·
    refine ⟨218802690639041017949819279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145868460426027345299879519 218802690639041017949819279)
    ·
      refine ⟨328204035958561526924728919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218802690639041017949819279 328204035958561526924728919)
      ·
        refine ⟨492306053937842290387093379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328204035958561526924728919 492306053937842290387093379)
        ·
          refine ⟨738459080906763435580640069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492306053937842290387093379 738459080906763435580640069)
          ·
            refine ⟨138461077670018144171370013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 738459080906763435580640069 138461077670018144171370013)
            ·
              refine ⟨51922904126256804064263755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138461077670018144171370013 51922904126256804064263755)
              ·
                refine ⟨77884356189385206096395633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51922904126256804064263755 77884356189385206096395633)
                ·
                  refine ⟨58413267142038904572296725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77884356189385206096395633 58413267142038904572296725)
                  ·
                    refine ⟨2738121897283073651826409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58413267142038904572296725 2738121897283073651826409)
                    ·
                      refine ⟨2053591422962305238869807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738121897283073651826409 2053591422962305238869807)
                      ·
                        rfl

theorem cell23_3999355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6, 2].length) (baseStart_3999355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999355 prefixEnd_3999355 := by exact prefixLift 3999355
  have htrace : WordTrace (prefixWord ++ tailWord_3999355) baseStart_3999355 baseEnd_3999355 := by
    simpa [prefixWord, tailWord_3999355, baseEnd_3999355] using wordTrace_append hprefix tailTrace_3999355
  have hstable : (prefixWord ++ tailWord_3999355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999355).length < 2 ^ (prefixWord ++ tailWord_3999355).sum := by decide
  have hdescent : baseEnd_3999355 < baseStart_3999355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999365 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_3999365 : Nat := 118140960795 + 3999365 * 2 ^ 59
def prefixEnd_3999365 : Nat := 4983230072969 + 3 ^ 40 * 3999365 * 2
def baseEnd_3999365 : Nat := 684532185922950066581587

theorem tailTrace_3999365 : CollatzResearch.WordTrace tailWord_3999365 prefixEnd_3999365 684532185922950066581587 := by
  unfold tailWord_3999365
  simp only [CollatzResearch.WordTrace]
  refine ⟨145868825155991117007743549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97245883437327411338495699 145868825155991117007743549)
  ·
    refine ⟨54700809433496668877903831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145868825155991117007743549 54700809433496668877903831)
    ·
      refine ⟨82051214150245003316855747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54700809433496668877903831 82051214150245003316855747)
      ·
        refine ⟨123076821225367504975283621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82051214150245003316855747 123076821225367504975283621)
        ·
          refine ⟨23076903979756407182865679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123076821225367504975283621 23076903979756407182865679)
          ·
            refine ⟨34615355969634610774298519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23076903979756407182865679 34615355969634610774298519)
            ·
              refine ⟨51923033954451916161447779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34615355969634610774298519 51923033954451916161447779)
              ·
                refine ⟨77884550931677874242171669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51923033954451916161447779 77884550931677874242171669)
                ·
                  refine ⟨3650838324922400355101797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77884550931677874242171669 3650838324922400355101797)
                  ·
                    refine ⟨684532185922950066581587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3650838324922400355101797 684532185922950066581587)
                    ·
                      rfl

theorem cell23_3999365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_3999365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999365 prefixEnd_3999365 := by exact prefixLift 3999365
  have htrace : WordTrace (prefixWord ++ tailWord_3999365) baseStart_3999365 baseEnd_3999365 := by
    simpa [prefixWord, tailWord_3999365, baseEnd_3999365] using wordTrace_append hprefix tailTrace_3999365
  have hstable : (prefixWord ++ tailWord_3999365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999365).length < 2 ^ (prefixWord ++ tailWord_3999365).sum := by decide
  have hdescent : baseEnd_3999365 < baseStart_3999365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999422 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_3999422 : Nat := 118140960795 + 3999422 * 2 ^ 59
def prefixEnd_3999422 : Nat := 4983230072969 + 3 ^ 40 * 3999422 * 2
def baseEnd_3999422 : Nat := 2053625826166156476731999

theorem tailTrace_3999422 : CollatzResearch.WordTrace tailWord_3999422 prefixEnd_3999422 2053625826166156476731999 := by
  unfold tailWord_3999422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18233863014598076967821065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97247269411189743828379013 18233863014598076967821065)
  ·
    refine ⟨13675397260948557725865799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18233863014598076967821065 13675397260948557725865799)
    ·
      refine ⟨20513095891422836588798699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13675397260948557725865799 20513095891422836588798699)
      ·
        refine ⟨30769643837134254883198049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20513095891422836588798699 30769643837134254883198049)
        ·
          refine ⟨23077232877850691162398537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30769643837134254883198049 23077232877850691162398537)
          ·
            refine ⟨17307924658388018371798903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23077232877850691162398537 17307924658388018371798903)
            ·
              refine ⟨25961886987582027557698355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17307924658388018371798903 25961886987582027557698355)
              ·
                refine ⟨38942830481373041336547533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25961886987582027557698355 38942830481373041336547533)
                ·
                  refine ⟨14603561430514890501205325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38942830481373041336547533 14603561430514890501205325)
                  ·
                    refine ⟨5476335536443083937951997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14603561430514890501205325 5476335536443083937951997)
                    ·
                      refine ⟨2053625826166156476731999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476335536443083937951997 2053625826166156476731999)
                      ·
                        rfl

theorem cell23_3999422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_3999422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999422 prefixEnd_3999422 := by exact prefixLift 3999422
  have htrace : WordTrace (prefixWord ++ tailWord_3999422) baseStart_3999422 baseEnd_3999422 := by
    simpa [prefixWord, tailWord_3999422, baseEnd_3999422] using wordTrace_append hprefix tailTrace_3999422
  have hstable : (prefixWord ++ tailWord_3999422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999422).length < 2 ^ (prefixWord ++ tailWord_3999422).sum := by decide
  have hdescent : baseEnd_3999422 < baseStart_3999422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999446 : List Nat := [5, 2, 1, 3, 1, 2, 1, 8]
def baseStart_3999446 : Nat := 118140960795 + 3999446 * 2 ^ 59
def prefixEnd_3999446 : Nat := 4983230072969 + 3 ^ 40 * 3999446 * 2
def baseEnd_3999446 : Nat := 76060672211180162327107

theorem tailTrace_3999446 : CollatzResearch.WordTrace tailWord_3999446 prefixEnd_3999446 76060672211180162327107 := by
  unfold tailWord_3999446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9116986216793604240090137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97247852979131778560961461 9116986216793604240090137)
  ·
    refine ⟨6837739662595203180067603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9116986216793604240090137 6837739662595203180067603)
    ·
      refine ⟨10256609493892804770101405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6837739662595203180067603 10256609493892804770101405)
      ·
        refine ⟨3846228560209801788788027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10256609493892804770101405 3846228560209801788788027)
        ·
          refine ⟨5769342840314702683182041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846228560209801788788027 5769342840314702683182041)
          ·
            refine ⟨4327007130236027012386531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5769342840314702683182041 4327007130236027012386531)
            ·
              refine ⟨6490510695354040518579797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327007130236027012386531 6490510695354040518579797)
              ·
                refine ⟨76060672211180162327107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6490510695354040518579797 76060672211180162327107)
                ·
                  rfl

theorem cell23_3999446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_3999446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999446 prefixEnd_3999446 := by exact prefixLift 3999446
  have htrace : WordTrace (prefixWord ++ tailWord_3999446) baseStart_3999446 baseEnd_3999446 := by
    simpa [prefixWord, tailWord_3999446, baseEnd_3999446] using wordTrace_append hprefix tailTrace_3999446
  have hstable : (prefixWord ++ tailWord_3999446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999446).length < 2 ^ (prefixWord ++ tailWord_3999446).sum := by decide
  have hdescent : baseEnd_3999446 < baseStart_3999446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999455 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 2, 6]
def baseStart_3999455 : Nat := 118140960795 + 3999455 * 2 ^ 59
def prefixEnd_3999455 : Nat := 4983230072969 + 3 ^ 40 * 3999455 * 2
def baseEnd_3999455 : Nat := 684547590342584949206449

theorem tailTrace_3999455 : CollatzResearch.WordTrace tailWord_3999455 prefixEnd_3999455 684547590342584949206449 := by
  unfold tailWord_3999455
  simp only [CollatzResearch.WordTrace]
  refine ⟨145872107725665062378519819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97248071817110041585679879 145872107725665062378519819)
  ·
    refine ⟨218808161588497593567779729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145872107725665062378519819 218808161588497593567779729)
    ·
      refine ⟨164106121191373195175834797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218808161588497593567779729 164106121191373195175834797)
      ·
        refine ⟨61539795446764948190938049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164106121191373195175834797 61539795446764948190938049)
        ·
          refine ⟨46154846585073711143203537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61539795446764948190938049 46154846585073711143203537)
          ·
            refine ⟨34616134938805283357402653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46154846585073711143203537 34616134938805283357402653)
            ·
              refine ⟨12981050602051981259025995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34616134938805283357402653 12981050602051981259025995)
              ·
                refine ⟨19471575903077971888538993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12981050602051981259025995 19471575903077971888538993)
                ·
                  refine ⟨14603681927308478916404245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19471575903077971888538993 14603681927308478916404245)
                  ·
                    refine ⟨684547590342584949206449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14603681927308478916404245 684547590342584949206449)
                    ·
                      rfl

theorem cell23_3999455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_3999455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999455 prefixEnd_3999455 := by exact prefixLift 3999455
  have htrace : WordTrace (prefixWord ++ tailWord_3999455) baseStart_3999455 baseEnd_3999455 := by
    simpa [prefixWord, tailWord_3999455, baseEnd_3999455] using wordTrace_append hprefix tailTrace_3999455
  have hstable : (prefixWord ++ tailWord_3999455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999455).length < 2 ^ (prefixWord ++ tailWord_3999455).sum := by decide
  have hdescent : baseEnd_3999455 < baseStart_3999455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999465 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 3]
def baseStart_3999465 : Nat := 118140960795 + 3999465 * 2 ^ 59
def prefixEnd_3999465 : Nat := 4983230072969 + 3 ^ 40 * 3999465 * 2
def baseEnd_3999465 : Nat := 2053647905834299808494301

theorem tailTrace_3999465 : CollatzResearch.WordTrace tailWord_3999465 prefixEnd_3999465 2053647905834299808494301 := by
  unfold tailWord_3999465
  simp only [CollatzResearch.WordTrace]
  refine ⟨145872472455628834086383849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97248314970419222724255899 145872472455628834086383849)
  ·
    refine ⟨109404354341721625564787887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145872472455628834086383849 109404354341721625564787887)
    ·
      refine ⟨164106531512582438347181831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109404354341721625564787887 164106531512582438347181831)
      ·
        refine ⟨246159797268873657520772747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164106531512582438347181831 246159797268873657520772747)
        ·
          refine ⟨369239695903310486281159121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246159797268873657520772747 369239695903310486281159121)
          ·
            refine ⟨276929771927482864710869341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369239695903310486281159121 276929771927482864710869341)
            ·
              refine ⟨103848664472806074266576003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276929771927482864710869341 103848664472806074266576003)
              ·
                refine ⟨155772996709209111399864005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103848664472806074266576003 155772996709209111399864005)
                ·
                  refine ⟨29207436882976708387474501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155772996709209111399864005 29207436882976708387474501)
                  ·
                    refine ⟨5476394415558132822651469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29207436882976708387474501 5476394415558132822651469)
                    ·
                      refine ⟨2053647905834299808494301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476394415558132822651469 2053647905834299808494301)
                      ·
                        rfl

theorem cell23_3999465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_3999465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999465 prefixEnd_3999465 := by exact prefixLift 3999465
  have htrace : WordTrace (prefixWord ++ tailWord_3999465) baseStart_3999465 baseEnd_3999465 := by
    simpa [prefixWord, tailWord_3999465, baseEnd_3999465] using wordTrace_append hprefix tailTrace_3999465
  have hstable : (prefixWord ++ tailWord_3999465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999465).length < 2 ^ (prefixWord ++ tailWord_3999465).sum := by decide
  have hdescent : baseEnd_3999465 < baseStart_3999465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999492 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3999492 : Nat := 118140960795 + 3999492 * 2 ^ 59
def prefixEnd_3999492 : Nat := 4983230072969 + 3 ^ 40 * 3999492 * 2
def baseEnd_3999492 : Nat := 2053661769811971202856677

theorem tailTrace_3999492 : CollatzResearch.WordTrace tailWord_3999492 prefixEnd_3999492 2053661769811971202856677 := by
  unfold tailWord_3999492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72936728613265508848808365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97248971484354011798411153 72936728613265508848808365)
  ·
    refine ⟨27351273229974565818303137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72936728613265508848808365 27351273229974565818303137)
    ·
      refine ⟨20513454922480924363727353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27351273229974565818303137 20513454922480924363727353)
      ·
        refine ⟨15385091191860693272795515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20513454922480924363727353 15385091191860693272795515)
        ·
          refine ⟨23077636787791039909193273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15385091191860693272795515 23077636787791039909193273)
          ·
            refine ⟨17308227590843279931894955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23077636787791039909193273 17308227590843279931894955)
            ·
              refine ⟨25962341386264919897842433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17308227590843279931894955 25962341386264919897842433)
              ·
                refine ⟨19471756039698689923381825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25962341386264919897842433 19471756039698689923381825)
                ·
                  refine ⟨14603817029774017442536369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19471756039698689923381825 14603817029774017442536369)
                  ·
                    refine ⟨10952862772330513081902277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14603817029774017442536369 10952862772330513081902277)
                    ·
                      refine ⟨2053661769811971202856677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10952862772330513081902277 2053661769811971202856677)
                      ·
                        rfl

theorem cell23_3999492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3999492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999492 prefixEnd_3999492 := by exact prefixLift 3999492
  have htrace : WordTrace (prefixWord ++ tailWord_3999492) baseStart_3999492 baseEnd_3999492 := by
    simpa [prefixWord, tailWord_3999492, baseEnd_3999492] using wordTrace_append hprefix tailTrace_3999492
  have hstable : (prefixWord ++ tailWord_3999492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999492).length < 2 ^ (prefixWord ++ tailWord_3999492).sum := by decide
  have hdescent : baseEnd_3999492 < baseStart_3999492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999512 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3999512 : Nat := 118140960795 + 3999512 * 2 ^ 59
def prefixEnd_3999512 : Nat := 4983230072969 + 3 ^ 40 * 3999512 * 2
def baseEnd_3999512 : Nat := 2053672039425061124606585

theorem tailTrace_3999512 : CollatzResearch.WordTrace tailWord_3999512 prefixEnd_3999512 2053672039425061124606585 := by
  unfold tailWord_3999512
  simp only [CollatzResearch.WordTrace]
  refine ⟨72937093343229280556672395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97249457790972374075563193 72937093343229280556672395)
  ·
    refine ⟨109405640014843920835008593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72937093343229280556672395 109405640014843920835008593)
    ·
      refine ⟨82054230011132940626256445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109405640014843920835008593 82054230011132940626256445)
      ·
        refine ⟨30770336254174852734846167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82054230011132940626256445 30770336254174852734846167)
        ·
          refine ⟨46155504381262279102269251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30770336254174852734846167 46155504381262279102269251)
          ·
            refine ⟨69233256571893418653403877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46155504381262279102269251 69233256571893418653403877)
            ·
              refine ⟨12981235607230015997513227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69233256571893418653403877 12981235607230015997513227)
              ·
                refine ⟨19471853410845023996269841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12981235607230015997513227 19471853410845023996269841)
                ·
                  refine ⟨14603890058133767997202381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19471853410845023996269841 14603890058133767997202381)
                  ·
                    refine ⟨5476458771800162998950893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14603890058133767997202381 5476458771800162998950893)
                    ·
                      refine ⟨2053672039425061124606585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476458771800162998950893 2053672039425061124606585)
                      ·
                        rfl

theorem cell23_3999512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3999512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999512 prefixEnd_3999512 := by exact prefixLift 3999512
  have htrace : WordTrace (prefixWord ++ tailWord_3999512) baseStart_3999512 baseEnd_3999512 := by
    simpa [prefixWord, tailWord_3999512, baseEnd_3999512] using wordTrace_append hprefix tailTrace_3999512
  have hstable : (prefixWord ++ tailWord_3999512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999512).length < 2 ^ (prefixWord ++ tailWord_3999512).sum := by decide
  have hdescent : baseEnd_3999512 < baseStart_3999512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999515 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 4, 5]
def baseStart_3999515 : Nat := 118140960795 + 3999515 * 2 ^ 59
def prefixEnd_3999515 : Nat := 4983230072969 + 3 ^ 40 * 3999515 * 2
def baseEnd_3999515 : Nat := 684557859955674870956357

theorem tailTrace_3999515 : CollatzResearch.WordTrace tailWord_3999515 prefixEnd_3999515 684557859955674870956357 := by
  unfold tailWord_3999515
  simp only [CollatzResearch.WordTrace]
  refine ⟨145874296105447692625703999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97249530736965128417135999 145874296105447692625703999)
  ·
    refine ⟨218811444158171538938555999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145874296105447692625703999 218811444158171538938555999)
    ·
      refine ⟨328217166237257308407833999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218811444158171538938555999 328217166237257308407833999)
      ·
        refine ⟨492325749355885962611750999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328217166237257308407833999 492325749355885962611750999)
        ·
          refine ⟨738488624033828943917626499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492325749355885962611750999 738488624033828943917626499)
          ·
            refine ⟨1107732936050743415876439749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738488624033828943917626499 1107732936050743415876439749)
            ·
              refine ⟨207699925509514390476832453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1107732936050743415876439749 207699925509514390476832453)
              ·
                refine ⟨38943736033033948214406085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207699925509514390476832453 38943736033033948214406085)
                ·
                  refine ⟨7301950506193865290201141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38943736033033948214406085 7301950506193865290201141)
                  ·
                    refine ⟨684557859955674870956357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7301950506193865290201141 684557859955674870956357)
                    ·
                      rfl

theorem cell23_3999515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 5].length) (baseStart_3999515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999515 prefixEnd_3999515 := by exact prefixLift 3999515
  have htrace : WordTrace (prefixWord ++ tailWord_3999515) baseStart_3999515 baseEnd_3999515 := by
    simpa [prefixWord, tailWord_3999515, baseEnd_3999515] using wordTrace_append hprefix tailTrace_3999515
  have hstable : (prefixWord ++ tailWord_3999515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999515).length < 2 ^ (prefixWord ++ tailWord_3999515).sum := by decide
  have hdescent : baseEnd_3999515 < baseStart_3999515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999549 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3999549 : Nat := 118140960795 + 3999549 * 2 ^ 59
def prefixEnd_3999549 : Nat := 4983230072969 + 3 ^ 40 * 3999549 * 2
def baseEnd_3999549 : Nat := 684563679403092493281305

theorem tailTrace_3999549 : CollatzResearch.WordTrace tailWord_3999549 prefixEnd_3999549 684563679403092493281305 := by
  unfold tailWord_3999549
  simp only [CollatzResearch.WordTrace]
  refine ⟨145875536187324516432441701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97250357458216344288294467 145875536187324516432441701)
  ·
    refine ⟨27351663035123346831082819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145875536187324516432441701 27351663035123346831082819)
    ·
      refine ⟨41027494552685020246624229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27351663035123346831082819 41027494552685020246624229)
      ·
        refine ⟨7692655228628441296242043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41027494552685020246624229 7692655228628441296242043)
        ·
          refine ⟨11538982842942661944363065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7692655228628441296242043 11538982842942661944363065)
          ·
            refine ⟨8654237132206996458272299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11538982842942661944363065 8654237132206996458272299)
            ·
              refine ⟨12981355698310494687408449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8654237132206996458272299 12981355698310494687408449)
              ·
                refine ⟨9736016773732871015556337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12981355698310494687408449 9736016773732871015556337)
                ·
                  refine ⟨7302012580299653261667253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736016773732871015556337 7302012580299653261667253)
                  ·
                    refine ⟨684563679403092493281305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7302012580299653261667253 684563679403092493281305)
                    ·
                      rfl

theorem cell23_3999549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3999549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999549 prefixEnd_3999549 := by exact prefixLift 3999549
  have htrace : WordTrace (prefixWord ++ tailWord_3999549) baseStart_3999549 baseEnd_3999549 := by
    simpa [prefixWord, tailWord_3999549, baseEnd_3999549] using wordTrace_append hprefix tailTrace_3999549
  have hstable : (prefixWord ++ tailWord_3999549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999549).length < 2 ^ (prefixWord ++ tailWord_3999549).sum := by decide
  have hdescent : baseEnd_3999549 < baseStart_3999549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999586 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3999586 : Nat := 118140960795 + 3999586 * 2 ^ 59
def prefixEnd_3999586 : Nat := 4983230072969 + 3 ^ 40 * 3999586 * 2
def baseEnd_3999586 : Nat := 2053710036993493835081245

theorem tailTrace_3999586 : CollatzResearch.WordTrace tailWord_3999586 prefixEnd_3999586 2053710036993493835081245 := by
  unfold tailWord_3999586
  simp only [CollatzResearch.WordTrace]
  refine ⟨36469221422047617937884653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97251257125460314501025741 36469221422047617937884653)
  ·
    refine ⟨13675958033267856726706745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36469221422047617937884653 13675958033267856726706745)
    ·
      refine ⟨10256968524950892545030059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13675958033267856726706745 10256968524950892545030059)
      ·
        refine ⟨15385452787426338817545089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10256968524950892545030059 15385452787426338817545089)
        ·
          refine ⟨11539089590569754113158817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15385452787426338817545089 11539089590569754113158817)
          ·
            refine ⟨8654317192927315584869113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11539089590569754113158817 8654317192927315584869113)
            ·
              refine ⟨6490737894695486688651835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8654317192927315584869113 6490737894695486688651835)
              ·
                refine ⟨9736106842043230032977753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490737894695486688651835 9736106842043230032977753)
                ·
                  refine ⟨7302080131532422524733315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736106842043230032977753 7302080131532422524733315)
                  ·
                    refine ⟨10953120197298633787099973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7302080131532422524733315 10953120197298633787099973)
                    ·
                      refine ⟨2053710036993493835081245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10953120197298633787099973 2053710036993493835081245)
                      ·
                        rfl

theorem cell23_3999586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3999586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999586 prefixEnd_3999586 := by exact prefixLift 3999586
  have htrace : WordTrace (prefixWord ++ tailWord_3999586) baseStart_3999586 baseEnd_3999586 := by
    simpa [prefixWord, tailWord_3999586, baseEnd_3999586] using wordTrace_append hprefix tailTrace_3999586
  have hstable : (prefixWord ++ tailWord_3999586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999586).length < 2 ^ (prefixWord ++ tailWord_3999586).sum := by decide
  have hdescent : baseEnd_3999586 < baseStart_3999586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999595 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8]
def baseStart_3999595 : Nat := 118140960795 + 3999595 * 2 ^ 59
def prefixEnd_3999595 : Nat := 4983230072969 + 3 ^ 40 * 3999595 * 2
def baseEnd_3999595 : Nat := 2053714658319384299868703

theorem tailTrace_3999595 : CollatzResearch.WordTrace tailWord_3999595 prefixEnd_3999595 2053714658319384299868703 := by
  unfold tailWord_3999595
  simp only [CollatzResearch.WordTrace]
  refine ⟨145877213945157866288616239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97251475963438577525744159 145877213945157866288616239)
  ·
    refine ⟨218815820917736799432924359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145877213945157866288616239 218815820917736799432924359)
    ·
      refine ⟨328223731376605199149386539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218815820917736799432924359 328223731376605199149386539)
      ·
        refine ⟨492335597064907798724079809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328223731376605199149386539 492335597064907798724079809)
        ·
          refine ⟨369251697798680849043059857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492335597064907798724079809 369251697798680849043059857)
          ·
            refine ⟨276938773349010636782294893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369251697798680849043059857 276938773349010636782294893)
            ·
              refine ⟨103852040005878988793360585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276938773349010636782294893 103852040005878988793360585)
              ·
                refine ⟨77889030004409241595020439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103852040005878988793360585 77889030004409241595020439)
                ·
                  refine ⟨116833545006613862392530659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77889030004409241595020439 116833545006613862392530659)
                  ·
                    refine ⟨175250317509920793588795989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116833545006613862392530659 175250317509920793588795989)
                    ·
                      refine ⟨2053714658319384299868703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 175250317509920793588795989 2053714658319384299868703)
                      ·
                        rfl

theorem cell23_3999595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_3999595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999595 prefixEnd_3999595 := by exact prefixLift 3999595
  have htrace : WordTrace (prefixWord ++ tailWord_3999595) baseStart_3999595 baseEnd_3999595 := by
    simpa [prefixWord, tailWord_3999595, baseEnd_3999595] using wordTrace_append hprefix tailTrace_3999595
  have hstable : (prefixWord ++ tailWord_3999595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999595).length < 2 ^ (prefixWord ++ tailWord_3999595).sum := by decide
  have hdescent : baseEnd_3999595 < baseStart_3999595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999636 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3999636 : Nat := 118140960795 + 3999636 * 2 ^ 59
def prefixEnd_3999636 : Nat := 4983230072969 + 3 ^ 40 * 3999636 * 2
def baseEnd_3999636 : Nat := 2053735711026218639456015

theorem tailTrace_3999636 : CollatzResearch.WordTrace tailWord_3999636 prefixEnd_3999636 2053735711026218639456015 := by
  unfold tailWord_3999636
  simp only [CollatzResearch.WordTrace]
  refine ⟨72939354669004665145429381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97252472892006220193905841 72939354669004665145429381)
  ·
    refine ⟨13676129000438374714768009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72939354669004665145429381 13676129000438374714768009)
    ·
      refine ⟨10257096750328781036076007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13676129000438374714768009 10257096750328781036076007)
      ·
        refine ⟨15385645125493171554114011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257096750328781036076007 15385645125493171554114011)
        ·
          refine ⟨23078467688239757331171017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15385645125493171554114011 23078467688239757331171017)
          ·
            refine ⟨17308850766179817998378263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23078467688239757331171017 17308850766179817998378263)
            ·
              refine ⟨25963276149269726997567395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17308850766179817998378263 25963276149269726997567395)
              ·
                refine ⟨38944914223904590496351093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25963276149269726997567395 38944914223904590496351093)
                ·
                  refine ⟨3651085708491055359032915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38944914223904590496351093 3651085708491055359032915)
                  ·
                    refine ⟨5476628562736583038549373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3651085708491055359032915 5476628562736583038549373)
                    ·
                      refine ⟨2053735711026218639456015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476628562736583038549373 2053735711026218639456015)
                      ·
                        rfl

theorem cell23_3999636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3999636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999636 prefixEnd_3999636 := by exact prefixLift 3999636
  have htrace : WordTrace (prefixWord ++ tailWord_3999636) baseStart_3999636 baseEnd_3999636 := by
    simpa [prefixWord, tailWord_3999636, baseEnd_3999636] using wordTrace_append hprefix tailTrace_3999636
  have hstable : (prefixWord ++ tailWord_3999636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999636).length < 2 ^ (prefixWord ++ tailWord_3999636).sum := by decide
  have hdescent : baseEnd_3999636 < baseStart_3999636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999640 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3999640 : Nat := 118140960795 + 3999640 * 2 ^ 59
def prefixEnd_3999640 : Nat := 4983230072969 + 3 ^ 40 * 3999640 * 2
def baseEnd_3999640 : Nat := 2053737764948836623805997

theorem tailTrace_3999640 : CollatzResearch.WordTrace tailWord_3999640 prefixEnd_3999640 2053737764948836623805997 := by
  unfold tailWord_3999640
  simp only [CollatzResearch.WordTrace]
  refine ⟨72939427614997419487002187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97252570153329892649336249 72939427614997419487002187)
  ·
    refine ⟨109409141422496129230503281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72939427614997419487002187 109409141422496129230503281)
    ·
      refine ⟨82056856066872096922877461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109409141422496129230503281 82056856066872096922877461)
      ·
        refine ⟨3846415128134629543259881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82056856066872096922877461 3846415128134629543259881)
        ·
          refine ⟨2884811346100972157444911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3846415128134629543259881 2884811346100972157444911)
          ·
            refine ⟨4327217019151458236167367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884811346100972157444911 4327217019151458236167367)
            ·
              refine ⟨6490825528727187354251051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327217019151458236167367 6490825528727187354251051)
              ·
                refine ⟨9736238293090781031376577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490825528727187354251051 9736238293090781031376577)
                ·
                  refine ⟨7302178719818085773532433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736238293090781031376577 7302178719818085773532433)
                  ·
                    refine ⟨5476634039863564330149325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7302178719818085773532433 5476634039863564330149325)
                    ·
                      refine ⟨2053737764948836623805997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476634039863564330149325 2053737764948836623805997)
                      ·
                        rfl

theorem cell23_3999640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3999640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999640 prefixEnd_3999640 := by exact prefixLift 3999640
  have htrace : WordTrace (prefixWord ++ tailWord_3999640) baseStart_3999640 baseEnd_3999640 := by
    simpa [prefixWord, tailWord_3999640, baseEnd_3999640] using wordTrace_append hprefix tailTrace_3999640
  have hstable : (prefixWord ++ tailWord_3999640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999640).length < 2 ^ (prefixWord ++ tailWord_3999640).sum := by decide
  have hdescent : baseEnd_3999640 < baseStart_3999640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999672 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_3999672 : Nat := 118140960795 + 3999672 * 2 ^ 59
def prefixEnd_3999672 : Nat := 4983230072969 + 3 ^ 40 * 3999672 * 2
def baseEnd_3999672 : Nat := 2053754196329780498605849

theorem tailTrace_3999672 : CollatzResearch.WordTrace tailWord_3999672 prefixEnd_3999672 2053754196329780498605849 := by
  unfold tailWord_3999672
  simp only [CollatzResearch.WordTrace]
  refine ⟨72940011182939454219584635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97253348243919272292779513 72940011182939454219584635)
  ·
    refine ⟨109410016774409181329376953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72940011182939454219584635 109410016774409181329376953)
    ·
      refine ⟨82057512580806885997032715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109410016774409181329376953 82057512580806885997032715)
      ·
        refine ⟨123086268871210328995549073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82057512580806885997032715 123086268871210328995549073)
        ·
          refine ⟨92314701653407746746661805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123086268871210328995549073 92314701653407746746661805)
          ·
            refine ⟨34618013120027905029998177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92314701653407746746661805 34618013120027905029998177)
            ·
              refine ⟨25963509840020928772498633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34618013120027905029998177 25963509840020928772498633)
              ·
                refine ⟨19472632380015696579373975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25963509840020928772498633 19472632380015696579373975)
                ·
                  refine ⟨29208948570023544869060963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19472632380015696579373975 29208948570023544869060963)
                  ·
                    refine ⟨43813422855035317303591445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29208948570023544869060963 43813422855035317303591445)
                    ·
                      refine ⟨2053754196329780498605849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43813422855035317303591445 2053754196329780498605849)
                      ·
                        rfl

theorem cell23_3999672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_3999672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999672 prefixEnd_3999672 := by exact prefixLift 3999672
  have htrace : WordTrace (prefixWord ++ tailWord_3999672) baseStart_3999672 baseEnd_3999672 := by
    simpa [prefixWord, tailWord_3999672, baseEnd_3999672] using wordTrace_append hprefix tailTrace_3999672
  have hstable : (prefixWord ++ tailWord_3999672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999672).length < 2 ^ (prefixWord ++ tailWord_3999672).sum := by decide
  have hdescent : baseEnd_3999672 < baseStart_3999672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999770 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2]
def baseStart_3999770 : Nat := 118140960795 + 3999770 * 2 ^ 59
def prefixEnd_3999770 : Nat := 4983230072969 + 3 ^ 40 * 3999770 * 2
def baseEnd_3999770 : Nat := 2053804517433921115180399

theorem tailTrace_3999770 : CollatzResearch.WordTrace tailWord_3999770 prefixEnd_3999770 2053804517433921115180399 := by
  unfold tailWord_3999770
  simp only [CollatzResearch.WordTrace]
  refine ⟨36470899179880967794059191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97255731146349247450824509 36470899179880967794059191)
  ·
    refine ⟨54706348769821451691088787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36470899179880967794059191 54706348769821451691088787)
    ·
      refine ⟨82059523154732177536633181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54706348769821451691088787 82059523154732177536633181)
      ·
        refine ⟨30772321183024566576237443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82059523154732177536633181 30772321183024566576237443)
        ·
          refine ⟨46158481774536849864356165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30772321183024566576237443 46158481774536849864356165)
          ·
            refine ⟨8654715332725659349566781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46158481774536849864356165 8654715332725659349566781)
            ·
              refine ⟨3245518249772122256087543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8654715332725659349566781 3245518249772122256087543)
              ·
                refine ⟨4868277374658183384131315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245518249772122256087543 4868277374658183384131315)
                ·
                  refine ⟨7302416061987275076196973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868277374658183384131315 7302416061987275076196973)
                  ·
                    refine ⟨2738406023245228153573865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7302416061987275076196973 2738406023245228153573865)
                    ·
                      refine ⟨2053804517433921115180399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738406023245228153573865 2053804517433921115180399)
                      ·
                        rfl

theorem cell23_3999770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_3999770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999770 prefixEnd_3999770 := by exact prefixLift 3999770
  have htrace : WordTrace (prefixWord ++ tailWord_3999770) baseStart_3999770 baseEnd_3999770 := by
    simpa [prefixWord, tailWord_3999770, baseEnd_3999770] using wordTrace_append hprefix tailTrace_3999770
  have hstable : (prefixWord ++ tailWord_3999770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999770).length < 2 ^ (prefixWord ++ tailWord_3999770).sum := by decide
  have hdescent : baseEnd_3999770 < baseStart_3999770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999779 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4]
def baseStart_3999779 : Nat := 118140960795 + 3999779 * 2 ^ 59
def prefixEnd_3999779 : Nat := 4983230072969 + 3 ^ 40 * 3999779 * 2
def baseEnd_3999779 : Nat := 2053809138759811579967857

theorem tailTrace_3999779 : CollatzResearch.WordTrace tailWord_3999779 prefixEnd_3999779 2053809138759811579967857 := by
  unfold tailWord_3999779
  simp only [CollatzResearch.WordTrace]
  refine ⟨145883924976491265713314391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97255949984327510475542927 145883924976491265713314391)
  ·
    refine ⟨218825887464736898569971587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145883924976491265713314391 218825887464736898569971587)
    ·
      refine ⟨328238831197105347854957381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218825887464736898569971587 328238831197105347854957381)
      ·
        refine ⟨61544780849457252722804509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328238831197105347854957381 61544780849457252722804509)
        ·
          refine ⟨23079292818546469771051691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61544780849457252722804509 23079292818546469771051691)
          ·
            refine ⟨34618939227819704656577537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23079292818546469771051691 34618939227819704656577537)
            ·
              refine ⟨25964204420864778492433153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34618939227819704656577537 25964204420864778492433153)
              ·
                refine ⟨19473153315648583869324865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25964204420864778492433153 19473153315648583869324865)
                ·
                  refine ⟨14604864986736437901993649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19473153315648583869324865 14604864986736437901993649)
                  ·
                    refine ⟨10953648740052328426495237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14604864986736437901993649 10953648740052328426495237)
                    ·
                      refine ⟨2053809138759811579967857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10953648740052328426495237 2053809138759811579967857)
                      ·
                        rfl

theorem cell23_3999779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_3999779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999779 prefixEnd_3999779 := by exact prefixLift 3999779
  have htrace : WordTrace (prefixWord ++ tailWord_3999779) baseStart_3999779 baseEnd_3999779 := by
    simpa [prefixWord, tailWord_3999779, baseEnd_3999779] using wordTrace_append hprefix tailTrace_3999779
  have hstable : (prefixWord ++ tailWord_3999779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999779).length < 2 ^ (prefixWord ++ tailWord_3999779).sum := by decide
  have hdescent : baseEnd_3999779 < baseStart_3999779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999786 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3999786 : Nat := 118140960795 + 3999786 * 2 ^ 59
def prefixEnd_3999786 : Nat := 4983230072969 + 3 ^ 40 * 3999786 * 2
def baseEnd_3999786 : Nat := 2053812733124393052580325

theorem tailTrace_3999786 : CollatzResearch.WordTrace tailWord_3999786 prefixEnd_3999786 2053812733124393052580325 := by
  unfold tailWord_3999786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36471045071866476477204803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97256120191643937272546141 36471045071866476477204803)
  ·
    refine ⟨54706567607799714715807205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36471045071866476477204803 54706567607799714715807205)
    ·
      refine ⟨10257481426462446509213851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54706567607799714715807205 10257481426462446509213851)
      ·
        refine ⟨15386222139693669763820777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257481426462446509213851 15386222139693669763820777)
        ·
          refine ⟨11539666604770252322865583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15386222139693669763820777 11539666604770252322865583)
          ·
            refine ⟨17309499907155378484298375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11539666604770252322865583 17309499907155378484298375)
            ·
              refine ⟨25964249860733067726447563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17309499907155378484298375 25964249860733067726447563)
              ·
                refine ⟨38946374791099601589671345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25964249860733067726447563 38946374791099601589671345)
                ·
                  refine ⟨29209781093324701192253509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38946374791099601589671345 29209781093324701192253509)
                  ·
                    refine ⟨5476833954998381473547533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29209781093324701192253509 5476833954998381473547533)
                    ·
                      refine ⟨2053812733124393052580325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476833954998381473547533 2053812733124393052580325)
                      ·
                        rfl

theorem cell23_3999786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3999786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999786 prefixEnd_3999786 := by exact prefixLift 3999786
  have htrace : WordTrace (prefixWord ++ tailWord_3999786) baseStart_3999786 baseEnd_3999786 := by
    simpa [prefixWord, tailWord_3999786, baseEnd_3999786] using wordTrace_append hprefix tailTrace_3999786
  have hstable : (prefixWord ++ tailWord_3999786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999786).length < 2 ^ (prefixWord ++ tailWord_3999786).sum := by decide
  have hdescent : baseEnd_3999786 < baseStart_3999786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999799 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_3999799 : Nat := 118140960795 + 3999799 * 2 ^ 59
def prefixEnd_3999799 : Nat := 4983230072969 + 3 ^ 40 * 3999799 * 2
def baseEnd_3999799 : Nat := 2053819408372901501717765

theorem tailTrace_3999799 : CollatzResearch.WordTrace tailWord_3999799 prefixEnd_3999799 2053819408372901501717765 := by
  unfold tailWord_3999799
  simp only [CollatzResearch.WordTrace]
  refine ⟨145884654436418809129042451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97256436290945872752694967 145884654436418809129042451)
  ·
    refine ⟨218826981654628213693563677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145884654436418809129042451 218826981654628213693563677)
    ·
      refine ⟨82060118120485580135086379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218826981654628213693563677 82060118120485580135086379)
      ·
        refine ⟨123090177180728370202629569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82060118120485580135086379 123090177180728370202629569)
        ·
          refine ⟨92317632885546277651972177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123090177180728370202629569 92317632885546277651972177)
          ·
            refine ⟨69238224664159708238979133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92317632885546277651972177 69238224664159708238979133)
            ·
              refine ⟨25964334249059890589617175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69238224664159708238979133 25964334249059890589617175)
              ·
                refine ⟨38946501373589835884425763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25964334249059890589617175 38946501373589835884425763)
                ·
                  refine ⟨58419752060384753826638645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38946501373589835884425763 58419752060384753826638645)
                  ·
                    refine ⟨5476851755661070671247373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58419752060384753826638645 5476851755661070671247373)
                    ·
                      refine ⟨2053819408372901501717765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476851755661070671247373 2053819408372901501717765)
                      ·
                        rfl

theorem cell23_3999799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_3999799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999799 prefixEnd_3999799 := by exact prefixLift 3999799
  have htrace : WordTrace (prefixWord ++ tailWord_3999799) baseStart_3999799 baseEnd_3999799 := by
    simpa [prefixWord, tailWord_3999799, baseEnd_3999799] using wordTrace_append hprefix tailTrace_3999799
  have hstable : (prefixWord ++ tailWord_3999799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999799).length < 2 ^ (prefixWord ++ tailWord_3999799).sum := by decide
  have hdescent : baseEnd_3999799 < baseStart_3999799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999876 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3999876 : Nat := 118140960795 + 3999876 * 2 ^ 59
def prefixEnd_3999876 : Nat := 4983230072969 + 3 ^ 40 * 3999876 * 2
def baseEnd_3999876 : Nat := 2053858946383297700454911

theorem tailTrace_3999876 : CollatzResearch.WordTrace tailWord_3999876 prefixEnd_3999876 2053858946383297700454911 := by
  unfold tailWord_3999876
  simp only [CollatzResearch.WordTrace]
  refine ⟨72943731428569925639797741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97258308571426567519730321 72943731428569925639797741)
  ·
    refine ⟨27353899285713722114924153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72943731428569925639797741 27353899285713722114924153)
    ·
      refine ⟨20515424464285291586193115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27353899285713722114924153 20515424464285291586193115)
      ·
        refine ⟨30773136696427937379289673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20515424464285291586193115 30773136696427937379289673)
        ·
          refine ⟨23079852522320953034467255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30773136696427937379289673 23079852522320953034467255)
          ·
            refine ⟨34619778783481429551700883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23079852522320953034467255 34619778783481429551700883)
            ·
              refine ⟨51929668175222144327551325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34619778783481429551700883 51929668175222144327551325)
              ·
                refine ⟨19473625565708304122831747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51929668175222144327551325 19473625565708304122831747)
                ·
                  refine ⟨29210438348562456184247621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19473625565708304122831747 29210438348562456184247621)
                  ·
                    refine ⟨5476957190355460534546429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29210438348562456184247621 5476957190355460534546429)
                    ·
                      refine ⟨2053858946383297700454911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5476957190355460534546429 2053858946383297700454911)
                      ·
                        rfl

theorem cell23_3999876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3999876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999876 prefixEnd_3999876 := by exact prefixLift 3999876
  have htrace : WordTrace (prefixWord ++ tailWord_3999876) baseStart_3999876 baseEnd_3999876 := by
    simpa [prefixWord, tailWord_3999876, baseEnd_3999876] using wordTrace_append hprefix tailTrace_3999876
  have hstable : (prefixWord ++ tailWord_3999876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999876).length < 2 ^ (prefixWord ++ tailWord_3999876).sum := by decide
  have hdescent : baseEnd_3999876 < baseStart_3999876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999879 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 8]
def baseStart_3999879 : Nat := 118140960795 + 3999879 * 2 ^ 59
def prefixEnd_3999879 : Nat := 4983230072969 + 3 ^ 40 * 3999879 * 2
def baseEnd_3999879 : Nat := 228206720758362354301933

theorem tailTrace_3999879 : CollatzResearch.WordTrace tailWord_3999879 prefixEnd_3999879 228206720758362354301933 := by
  unfold tailWord_3999879
  simp only [CollatzResearch.WordTrace]
  refine ⟨145887572276128982791954691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97258381517419321861303127 145887572276128982791954691)
  ·
    refine ⟨218831358414193474187932037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145887572276128982791954691 218831358414193474187932037)
    ·
      refine ⟨41030879702661276410237257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218831358414193474187932037 41030879702661276410237257)
      ·
        refine ⟨30773159776995957307677943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41030879702661276410237257 30773159776995957307677943)
        ·
          refine ⟨46159739665493935961516915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30773159776995957307677943 46159739665493935961516915)
          ·
            refine ⟨69239609498240903942275373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46159739665493935961516915 69239609498240903942275373)
            ·
              refine ⟨25964853561840338978353265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69239609498240903942275373 25964853561840338978353265)
              ·
                refine ⟨19473640171380254233764949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25964853561840338978353265 19473640171380254233764949)
                ·
                  refine ⟨228206720758362354301933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19473640171380254233764949 228206720758362354301933)
                  ·
                    rfl

theorem cell23_3999879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 8].length) (baseStart_3999879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999879 prefixEnd_3999879 := by exact prefixLift 3999879
  have htrace : WordTrace (prefixWord ++ tailWord_3999879) baseStart_3999879 baseEnd_3999879 := by
    simpa [prefixWord, tailWord_3999879, baseEnd_3999879] using wordTrace_append hprefix tailTrace_3999879
  have hstable : (prefixWord ++ tailWord_3999879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999879).length < 2 ^ (prefixWord ++ tailWord_3999879).sum := by decide
  have hdescent : baseEnd_3999879 < baseStart_3999879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999924 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3999924 : Nat := 118140960795 + 3999924 * 2 ^ 59
def prefixEnd_3999924 : Nat := 4983230072969 + 3 ^ 40 * 3999924 * 2
def baseEnd_3999924 : Nat := 2053883593454713512654691

theorem tailTrace_3999924 : CollatzResearch.WordTrace tailWord_3999924 prefixEnd_3999924 2053883593454713512654691 := by
  unfold tailWord_3999924
  simp only [CollatzResearch.WordTrace]
  refine ⟨72944606780482977738671413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97259475707310636984895217 72944606780482977738671413)
  ·
    refine ⟨6838556885670279163000445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72944606780482977738671413 6838556885670279163000445)
    ·
      refine ⟨2564458832126354686125167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6838556885670279163000445 2564458832126354686125167)
      ·
        refine ⟨3846688248189532029187751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564458832126354686125167 3846688248189532029187751)
        ·
          refine ⟨5770032372284298043781627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846688248189532029187751 5770032372284298043781627)
          ·
            refine ⟨8655048558426447065672441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5770032372284298043781627 8655048558426447065672441)
            ·
              refine ⟨6491286418819835299254331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655048558426447065672441 6491286418819835299254331)
              ·
                refine ⟨9736929628229752948881497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491286418819835299254331 9736929628229752948881497)
                ·
                  refine ⟨7302697221172314711661123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736929628229752948881497 7302697221172314711661123)
                  ·
                    refine ⟨10954045831758472067491685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7302697221172314711661123 10954045831758472067491685)
                    ·
                      refine ⟨2053883593454713512654691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10954045831758472067491685 2053883593454713512654691)
                      ·
                        rfl

theorem cell23_3999924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3999924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999924 prefixEnd_3999924 := by exact prefixLift 3999924
  have htrace : WordTrace (prefixWord ++ tailWord_3999924) baseStart_3999924 baseEnd_3999924 := by
    simpa [prefixWord, tailWord_3999924, baseEnd_3999924] using wordTrace_append hprefix tailTrace_3999924
  have hstable : (prefixWord ++ tailWord_3999924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999924).length < 2 ^ (prefixWord ++ tailWord_3999924).sum := by decide
  have hdescent : baseEnd_3999924 < baseStart_3999924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999950 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_3999950 : Nat := 118140960795 + 3999950 * 2 ^ 59
def prefixEnd_3999950 : Nat := 4983230072969 + 3 ^ 40 * 3999950 * 2
def baseEnd_3999950 : Nat := 2053896943951730410929571

theorem tailTrace_3999950 : CollatzResearch.WordTrace tailWord_3999950 prefixEnd_3999950 2053896943951730410929571 := by
  unfold tailWord_3999950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18236270232358970239723663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97260107905914507945192869 18236270232358970239723663)
  ·
    refine ⟨27354405348538455359585495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18236270232358970239723663 27354405348538455359585495)
    ·
      refine ⟨41031608022807683039378243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27354405348538455359585495 41031608022807683039378243)
      ·
        refine ⟨61547412034211524559067365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41031608022807683039378243 61547412034211524559067365)
        ·
          refine ⟨11540139756414660854825131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61547412034211524559067365 11540139756414660854825131)
          ·
            refine ⟨17310209634621991282237697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11540139756414660854825131 17310209634621991282237697)
            ·
              refine ⟨12982657225966493461678273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17310209634621991282237697 12982657225966493461678273)
              ·
                refine ⟨9736992919474870096258705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12982657225966493461678273 9736992919474870096258705)
                ·
                  refine ⟨7302744689606152572194029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736992919474870096258705 7302744689606152572194029)
                  ·
                    refine ⟨2738529258602307214572761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7302744689606152572194029 2738529258602307214572761)
                    ·
                      refine ⟨2053896943951730410929571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738529258602307214572761 2053896943951730410929571)
                      ·
                        rfl

theorem cell23_3999950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_3999950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999950 prefixEnd_3999950 := by exact prefixLift 3999950
  have htrace : WordTrace (prefixWord ++ tailWord_3999950) baseStart_3999950 baseEnd_3999950 := by
    simpa [prefixWord, tailWord_3999950, baseEnd_3999950] using wordTrace_append hprefix tailTrace_3999950
  have hstable : (prefixWord ++ tailWord_3999950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999950).length < 2 ^ (prefixWord ++ tailWord_3999950).sum := by decide
  have hdescent : baseEnd_3999950 < baseStart_3999950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999973 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_3999973 : Nat := 118140960795 + 3999973 * 2 ^ 59
def prefixEnd_3999973 : Nat := 4983230072969 + 3 ^ 40 * 3999973 * 2
def baseEnd_3999973 : Nat := 684636251335594606980655

theorem tailTrace_3999973 : CollatzResearch.WordTrace tailWord_3999973 prefixEnd_3999973 684636251335594606980655 := by
  unfold tailWord_3999973
  simp only [CollatzResearch.WordTrace]
  refine ⟨145891000737788436845876573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97260667158525624563917715 145891000737788436845876573)
  ·
    refine ⟨54709125276670663817203715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145891000737788436845876573 54709125276670663817203715)
    ·
      refine ⟨82063687915005995725805573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54709125276670663817203715 82063687915005995725805573)
      ·
        refine ⟨15386941484063624198588545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82063687915005995725805573 15386941484063624198588545)
        ·
          refine ⟨11540206113047718148941409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15386941484063624198588545 11540206113047718148941409)
          ·
            refine ⟨8655154584785788611706057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11540206113047718148941409 8655154584785788611706057)
            ·
              refine ⟨6491365938589341458779543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655154584785788611706057 6491365938589341458779543)
              ·
                refine ⟨9737048907884012188169315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491365938589341458779543 9737048907884012188169315)
                ·
                  refine ⟨14605573361826018282253973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9737048907884012188169315 14605573361826018282253973)
                  ·
                    refine ⟨684636251335594606980655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14605573361826018282253973 684636251335594606980655)
                    ·
                      rfl

theorem cell23_3999973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_3999973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999973 prefixEnd_3999973 := by exact prefixLift 3999973
  have htrace : WordTrace (prefixWord ++ tailWord_3999973) baseStart_3999973 baseEnd_3999973 := by
    simpa [prefixWord, tailWord_3999973, baseEnd_3999973] using wordTrace_append hprefix tailTrace_3999973
  have hstable : (prefixWord ++ tailWord_3999973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999973).length < 2 ^ (prefixWord ++ tailWord_3999973).sum := by decide
  have hdescent : baseEnd_3999973 < baseStart_3999973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999980 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 3, 2, 2]
def baseStart_3999980 : Nat := 118140960795 + 3999980 * 2 ^ 59
def prefixEnd_3999980 : Nat := 4983230072969 + 3 ^ 40 * 3999980 * 2
def baseEnd_3999980 : Nat := 2053912348371365293554433

theorem tailTrace_3999980 : CollatzResearch.WordTrace tailWord_3999980 prefixEnd_3999980 2053912348371365293554433 := by
  unfold tailWord_3999980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72945628024381538520690697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97260837365842051360920929 72945628024381538520690697)
  ·
    refine ⟨54709221018286153890518023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72945628024381538520690697 54709221018286153890518023)
    ·
      refine ⟨82063831527429230835777035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54709221018286153890518023 82063831527429230835777035)
      ·
        refine ⟨123095747291143846253665553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82063831527429230835777035 123095747291143846253665553)
        ·
          refine ⟨92321810468357884690249165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123095747291143846253665553 92321810468357884690249165)
          ·
            refine ⟨34620678925634206758843437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92321810468357884690249165 34620678925634206758843437)
            ·
              refine ⟨12982754597112827534566289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34620678925634206758843437 12982754597112827534566289)
              ·
                refine ⟨9737065947834620650924717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12982754597112827534566289 9737065947834620650924717)
                ·
                  refine ⟨3651399730437982744096769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9737065947834620650924717 3651399730437982744096769)
                  ·
                    refine ⟨2738549797828487058072577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3651399730437982744096769 2738549797828487058072577)
                    ·
                      refine ⟨2053912348371365293554433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738549797828487058072577 2053912348371365293554433)
                      ·
                        rfl

theorem cell23_3999980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_3999980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999980 prefixEnd_3999980 := by exact prefixLift 3999980
  have htrace : WordTrace (prefixWord ++ tailWord_3999980) baseStart_3999980 baseEnd_3999980 := by
    simpa [prefixWord, tailWord_3999980, baseEnd_3999980] using wordTrace_append hprefix tailTrace_3999980
  have hstable : (prefixWord ++ tailWord_3999980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999980).length < 2 ^ (prefixWord ++ tailWord_3999980).sum := by decide
  have hdescent : baseEnd_3999980 < baseStart_3999980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3999983 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 3]
def baseStart_3999983 : Nat := 118140960795 + 3999983 * 2 ^ 59
def prefixEnd_3999983 : Nat := 4983230072969 + 3 ^ 40 * 3999983 * 2
def baseEnd_3999983 : Nat := 2053913888813328781816919

theorem tailTrace_3999983 : CollatzResearch.WordTrace tailWord_3999983 prefixEnd_3999983 2053913888813328781816919 := by
  unfold tailWord_3999983
  simp only [CollatzResearch.WordTrace]
  refine ⟨145891365467752208553740603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97260910311834805702493735 145891365467752208553740603)
  ·
    refine ⟨218837048201628312830610905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145891365467752208553740603 218837048201628312830610905)
    ·
      refine ⟨164127786151221234622958179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218837048201628312830610905 164127786151221234622958179)
      ·
        refine ⟨246191679226831851934437269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164127786151221234622958179 246191679226831851934437269)
        ·
          refine ⟨11540234963757743059426747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246191679226831851934437269 11540234963757743059426747)
          ·
            refine ⟨17310352445636614589140121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11540234963757743059426747 17310352445636614589140121)
            ·
              refine ⟨12982764334227460941855091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17310352445636614589140121 12982764334227460941855091)
              ·
                refine ⟨19474146501341191412782637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12982764334227460941855091 19474146501341191412782637)
                ·
                  refine ⟨7302804938002946779793489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19474146501341191412782637 7302804938002946779793489)
                  ·
                    refine ⟨5477103703502210084845117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7302804938002946779793489 5477103703502210084845117)
                    ·
                      refine ⟨2053913888813328781816919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5477103703502210084845117 2053913888813328781816919)
                      ·
                        rfl

theorem cell23_3999983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_3999983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3999983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3999983 prefixEnd_3999983 := by exact prefixLift 3999983
  have htrace : WordTrace (prefixWord ++ tailWord_3999983) baseStart_3999983 baseEnd_3999983 := by
    simpa [prefixWord, tailWord_3999983, baseEnd_3999983] using wordTrace_append hprefix tailTrace_3999983
  have hstable : (prefixWord ++ tailWord_3999983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3999983).length < 2 ^ (prefixWord ++ tailWord_3999983).sum := by decide
  have hdescent : baseEnd_3999983 < baseStart_3999983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3999983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000000 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 1, 2, 3]
def baseStart_4000000 : Nat := 118140960795 + 4000000 * 2 ^ 59
def prefixEnd_4000000 : Nat := 4983230072969 + 3 ^ 40 * 4000000 * 2
def baseEnd_4000000 : Nat := 2053922617984455215304341

theorem tailTrace_4000000 : CollatzResearch.WordTrace tailWord_4000000 prefixEnd_4000000 2053922617984455215304341 := by
  unfold tailWord_4000000
  simp only [CollatzResearch.WordTrace]
  refine ⟨72945992754345310228554727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97261323672460413638072969 72945992754345310228554727)
  ·
    refine ⟨109418989131517965342832091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72945992754345310228554727 109418989131517965342832091)
    ·
      refine ⟨164128483697276948014248137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109418989131517965342832091 164128483697276948014248137)
      ·
        refine ⟨123096362772957711010686103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164128483697276948014248137 123096362772957711010686103)
        ·
          refine ⟨184644544159436566516029155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123096362772957711010686103 184644544159436566516029155)
          ·
            refine ⟨276966816239154849774043733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184644544159436566516029155 276966816239154849774043733)
            ·
              refine ⟨3245704877802595895789575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 276966816239154849774043733 3245704877802595895789575)
              ·
                refine ⟨4868557316703893843684363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245704877802595895789575 4868557316703893843684363)
                ·
                  refine ⟨7302835975055840765526545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868557316703893843684363 7302835975055840765526545)
                  ·
                    refine ⟨5477126981291880574144909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7302835975055840765526545 5477126981291880574144909)
                    ·
                      refine ⟨2053922617984455215304341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5477126981291880574144909 2053922617984455215304341)
                      ·
                        rfl

theorem cell23_4000000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_4000000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000000 prefixEnd_4000000 := by exact prefixLift 4000000
  have htrace : WordTrace (prefixWord ++ tailWord_4000000) baseStart_4000000 baseEnd_4000000 := by
    simpa [prefixWord, tailWord_4000000, baseEnd_4000000] using wordTrace_append hprefix tailTrace_4000000
  have hstable : (prefixWord ++ tailWord_4000000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000000).length < 2 ^ (prefixWord ++ tailWord_4000000).sum := by decide
  have hdescent : baseEnd_4000000 < baseStart_4000000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000056 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_4000056 : Nat := 118140960795 + 4000056 * 2 ^ 59
def prefixEnd_4000056 : Nat := 4983230072969 + 3 ^ 40 * 4000056 * 2
def baseEnd_4000056 : Nat := 2053951372901106996204083

theorem tailTrace_4000056 : CollatzResearch.WordTrace tailWord_4000056 prefixEnd_4000056 2053951372901106996204083 := by
  unfold tailWord_4000056
  simp only [CollatzResearch.WordTrace]
  refine ⟨72947013998243871010574011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97262685330991828014098681 72947013998243871010574011)
  ·
    refine ⟨109420520997365806515861017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72947013998243871010574011 109420520997365806515861017)
    ·
      refine ⟨82065390748024354886895763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109420520997365806515861017 82065390748024354886895763)
      ·
        refine ⟨123098086122036532330343645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82065390748024354886895763 123098086122036532330343645)
        ·
          refine ⟨46161782295763699623878867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123098086122036532330343645 46161782295763699623878867)
          ·
            refine ⟨69242673443645549435818301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46161782295763699623878867 69242673443645549435818301)
            ·
              refine ⟨25966002541367081038431863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69242673443645549435818301 25966002541367081038431863)
              ·
                refine ⟨38949003812050621557647795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25966002541367081038431863 38949003812050621557647795)
                ·
                  refine ⟨58423505718075932336471693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38949003812050621557647795 58423505718075932336471693)
                  ·
                    refine ⟨21908814644278474626176885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58423505718075932336471693 21908814644278474626176885)
                    ·
                      refine ⟨2053951372901106996204083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21908814644278474626176885 2053951372901106996204083)
                      ·
                        rfl

theorem cell23_4000056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_4000056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000056 prefixEnd_4000056 := by exact prefixLift 4000056
  have htrace : WordTrace (prefixWord ++ tailWord_4000056) baseStart_4000056 baseEnd_4000056 := by
    simpa [prefixWord, tailWord_4000056, baseEnd_4000056] using wordTrace_append hprefix tailTrace_4000056
  have hstable : (prefixWord ++ tailWord_4000056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000056).length < 2 ^ (prefixWord ++ tailWord_4000056).sum := by decide
  have hdescent : baseEnd_4000056 < baseStart_4000056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000057 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4000057 : Nat := 118140960795 + 4000057 * 2 ^ 59
def prefixEnd_4000057 : Nat := 4983230072969 + 3 ^ 40 * 4000057 * 2
def baseEnd_4000057 : Nat := 2053951886381761492291579

theorem tailTrace_4000057 : CollatzResearch.WordTrace tailWord_4000057 prefixEnd_4000057 2053951886381761492291579 := by
  unfold tailWord_4000057
  simp only [CollatzResearch.WordTrace]
  refine ⟨145894064469484119191934425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97262709646322746127956283 145894064469484119191934425)
  ·
    refine ⟨109420548352113089393950819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145894064469484119191934425 109420548352113089393950819)
    ·
      refine ⟨164130822528169634090926229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109420548352113089393950819 164130822528169634090926229)
      ·
        refine ⟨7693632306007951598012167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164130822528169634090926229 7693632306007951598012167)
        ·
          refine ⟨11540448459011927397018251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7693632306007951598012167 11540448459011927397018251)
          ·
            refine ⟨17310672688517891095527377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11540448459011927397018251 17310672688517891095527377)
            ·
              refine ⟨12983004516388418321645533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17310672688517891095527377 12983004516388418321645533)
              ·
                refine ⟨4868626693645656870617075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12983004516388418321645533 4868626693645656870617075)
                ·
                  refine ⟨7302940040468485305925613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868626693645656870617075 7302940040468485305925613)
                  ·
                    refine ⟨2738602515175681989722105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7302940040468485305925613 2738602515175681989722105)
                    ·
                      refine ⟨2053951886381761492291579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738602515175681989722105 2053951886381761492291579)
                      ·
                        rfl

theorem cell23_4000057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4000057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000057 prefixEnd_4000057 := by exact prefixLift 4000057
  have htrace : WordTrace (prefixWord ++ tailWord_4000057) baseStart_4000057 baseEnd_4000057 := by
    simpa [prefixWord, tailWord_4000057, baseEnd_4000057] using wordTrace_append hprefix tailTrace_4000057
  have hstable : (prefixWord ++ tailWord_4000057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000057).length < 2 ^ (prefixWord ++ tailWord_4000057).sum := by decide
  have hdescent : baseEnd_4000057 < baseStart_4000057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000087 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 2, 2, 2]
def baseStart_4000087 : Nat := 118140960795 + 4000087 * 2 ^ 59
def prefixEnd_4000087 : Nat := 4983230072969 + 3 ^ 40 * 4000087 * 2
def baseEnd_4000087 : Nat := 2053967290801396374916441

theorem tailTrace_4000087 : CollatzResearch.WordTrace tailWord_4000087 prefixEnd_4000087 2053967290801396374916441 := by
  unfold tailWord_4000087
  simp only [CollatzResearch.WordTrace]
  refine ⟨145895158659375434315526515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97263439106250289543684343 145895158659375434315526515)
  ·
    refine ⟨218842737989063151473289773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145895158659375434315526515 218842737989063151473289773)
    ·
      refine ⟨82066026745898681802483665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218842737989063151473289773 82066026745898681802483665)
      ·
        refine ⟨61549520059424011351862749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82066026745898681802483665 61549520059424011351862749)
        ·
          refine ⟨23081070022284004256948531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61549520059424011351862749 23081070022284004256948531)
          ·
            refine ⟨34621605033426006385422797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23081070022284004256948531 34621605033426006385422797)
            ·
              refine ⟨12983101887534752394533549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34621605033426006385422797 12983101887534752394533549)
              ·
                refine ⟨4868663207825532147950081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12983101887534752394533549 4868663207825532147950081)
                ·
                  refine ⟨3651497405869149110962561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4868663207825532147950081 3651497405869149110962561)
                  ·
                    refine ⟨2738623054401861833221921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3651497405869149110962561 2738623054401861833221921)
                    ·
                      refine ⟨2053967290801396374916441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738623054401861833221921 2053967290801396374916441)
                      ·
                        rfl

theorem cell23_4000087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_4000087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000087 prefixEnd_4000087 := by exact prefixLift 4000087
  have htrace : WordTrace (prefixWord ++ tailWord_4000087) baseStart_4000087 baseEnd_4000087 := by
    simpa [prefixWord, tailWord_4000087, baseEnd_4000087] using wordTrace_append hprefix tailTrace_4000087
  have hstable : (prefixWord ++ tailWord_4000087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000087).length < 2 ^ (prefixWord ++ tailWord_4000087).sum := by decide
  have hdescent : baseEnd_4000087 < baseStart_4000087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000123 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 2, 5]
def baseStart_4000123 : Nat := 118140960795 + 4000123 * 2 ^ 59
def prefixEnd_4000123 : Nat := 4983230072969 + 3 ^ 40 * 4000123 * 2
def baseEnd_4000123 : Nat := 684661925368319411355425

theorem tailTrace_4000123 : CollatzResearch.WordTrace tailWord_4000123 prefixEnd_4000123 684661925368319411355425 := by
  unfold tailWord_4000123
  simp only [CollatzResearch.WordTrace]
  refine ⟨145896471687245012463837023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97264314458163341642558015 145896471687245012463837023)
  ·
    refine ⟨218844707530867518695755535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145896471687245012463837023 218844707530867518695755535)
    ·
      refine ⟨328267061296301278043633303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218844707530867518695755535 328267061296301278043633303)
      ·
        refine ⟨492400591944451917065449955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328267061296301278043633303 492400591944451917065449955)
        ·
          refine ⟨738600887916677875598174933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492400591944451917065449955 738600887916677875598174933)
          ·
            refine ⟨17310958310547137709332225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 738600887916677875598174933 17310958310547137709332225)
            ·
              refine ⟨12983218732910353281999169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17310958310547137709332225 12983218732910353281999169)
              ·
                refine ⟨9737414049682764961499377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12983218732910353281999169 9737414049682764961499377)
                ·
                  refine ⟨7303060537262073721124533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9737414049682764961499377 7303060537262073721124533)
                  ·
                    refine ⟨684661925368319411355425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7303060537262073721124533 684661925368319411355425)
                    ·
                      rfl

theorem cell23_4000123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 5].length) (baseStart_4000123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000123 prefixEnd_4000123 := by exact prefixLift 4000123
  have htrace : WordTrace (prefixWord ++ tailWord_4000123) baseStart_4000123 baseEnd_4000123 := by
    simpa [prefixWord, tailWord_4000123, baseEnd_4000123] using wordTrace_append hprefix tailTrace_4000123
  have hstable : (prefixWord ++ tailWord_4000123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000123).length < 2 ^ (prefixWord ++ tailWord_4000123).sum := by decide
  have hdescent : baseEnd_4000123 < baseStart_4000123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000157 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_4000157 : Nat := 118140960795 + 4000157 * 2 ^ 59
def prefixEnd_4000157 : Nat := 4983230072969 + 3 ^ 40 * 4000157 * 2
def baseEnd_4000157 : Nat := 684667744815737033680373

theorem tailTrace_4000157 : CollatzResearch.WordTrace tailWord_4000157 prefixEnd_4000157 684667744815737033680373 := by
  unfold tailWord_4000157
  simp only [CollatzResearch.WordTrace]
  refine ⟨145897711769121836270574725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97265141179414557513716483 145897711769121836270574725)
  ·
    refine ⟨27355820956710344300732761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145897711769121836270574725 27355820956710344300732761)
    ·
      refine ⟨20516865717532758225549571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27355820956710344300732761 20516865717532758225549571)
      ·
        refine ⟨30775298576299137338324357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20516865717532758225549571 30775298576299137338324357)
        ·
          refine ⟨5770368483056088250935817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30775298576299137338324357 5770368483056088250935817)
          ·
            refine ⟨4327776362292066188201863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5770368483056088250935817 4327776362292066188201863)
            ·
              refine ⟨6491664543438099282302795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327776362292066188201863 6491664543438099282302795)
              ·
                refine ⟨9737496815157148923454193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491664543438099282302795 9737496815157148923454193)
                ·
                  refine ⟨7303122611367861692590645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9737496815157148923454193 7303122611367861692590645)
                  ·
                    refine ⟨684667744815737033680373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7303122611367861692590645 684667744815737033680373)
                    ·
                      rfl

theorem cell23_4000157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_4000157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000157 prefixEnd_4000157 := by exact prefixLift 4000157
  have htrace : WordTrace (prefixWord ++ tailWord_4000157) baseStart_4000157 baseEnd_4000157 := by
    simpa [prefixWord, tailWord_4000157, baseEnd_4000157] using wordTrace_append hprefix tailTrace_4000157
  have hstable : (prefixWord ++ tailWord_4000157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000157).length < 2 ^ (prefixWord ++ tailWord_4000157).sum := by decide
  have hdescent : baseEnd_4000157 < baseStart_4000157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000160 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4]
def baseStart_4000160 : Nat := 118140960795 + 4000160 * 2 ^ 59
def prefixEnd_4000160 : Nat := 4983230072969 + 3 ^ 40 * 4000160 * 2
def baseEnd_4000160 : Nat := 2054004774889174589303605

theorem tailTrace_4000160 : CollatzResearch.WordTrace tailWord_4000160 prefixEnd_4000160 2054004774889174589303605 := by
  unfold tailWord_4000160
  simp only [CollatzResearch.WordTrace]
  refine ⟨72948910594055483891466967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97265214125407311855289289 72948910594055483891466967)
  ·
    refine ⟨109423365891083225837200451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72948910594055483891466967 109423365891083225837200451)
    ·
      refine ⟨164135048836624838755800677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109423365891083225837200451 164135048836624838755800677)
      ·
        refine ⟨30775321656867157266712627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164135048836624838755800677 30775321656867157266712627)
        ·
          refine ⟨46162982485300735900068941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30775321656867157266712627 46162982485300735900068941)
          ·
            refine ⟨17311118431987775962525853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46162982485300735900068941 17311118431987775962525853)
            ·
              refine ⟨6491669411995415985947195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17311118431987775962525853 6491669411995415985947195)
              ·
                refine ⟨9737504117993123978920793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491669411995415985947195 9737504117993123978920793)
                ·
                  refine ⟨7303128088494842984190595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9737504117993123978920793 7303128088494842984190595)
                  ·
                    refine ⟨10954692132742264476285893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303128088494842984190595 10954692132742264476285893)
                    ·
                      refine ⟨2054004774889174589303605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10954692132742264476285893 2054004774889174589303605)
                      ·
                        rfl

theorem cell23_4000160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_4000160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000160 prefixEnd_4000160 := by exact prefixLift 4000160
  have htrace : WordTrace (prefixWord ++ tailWord_4000160) baseStart_4000160 baseEnd_4000160 := by
    simpa [prefixWord, tailWord_4000160, baseEnd_4000160] using wordTrace_append hprefix tailTrace_4000160
  have hstable : (prefixWord ++ tailWord_4000160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000160).length < 2 ^ (prefixWord ++ tailWord_4000160).sum := by decide
  have hdescent : baseEnd_4000160 < baseStart_4000160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000183 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 8]
def baseStart_4000183 : Nat := 118140960795 + 4000183 * 2 ^ 59
def prefixEnd_4000183 : Nat := 4983230072969 + 3 ^ 40 * 4000183 * 2
def baseEnd_4000183 : Nat := 228224064993803111035111

theorem tailTrace_4000183 : CollatzResearch.WordTrace tailWord_4000183 prefixEnd_4000183 228224064993803111035111 := by
  unfold tailWord_4000183
  simp only [CollatzResearch.WordTrace]
  refine ⟨145898660067027642711021203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97265773378018428474014135 145898660067027642711021203)
  ·
    refine ⟨218847990100541464066531805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145898660067027642711021203 218847990100541464066531805)
    ·
      refine ⟨82067996287703049024949427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218847990100541464066531805 82067996287703049024949427)
      ·
        refine ⟨123101994431554573537424141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82067996287703049024949427 123101994431554573537424141)
        ·
          refine ⟨46163247911832965076534053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123101994431554573537424141 46163247911832965076534053)
          ·
            refine ⟨8655608983468680951850135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46163247911832965076534053 8655608983468680951850135)
            ·
              refine ⟨12983413475203021427775203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8655608983468680951850135 12983413475203021427775203)
              ·
                refine ⟨19475120212804532141662805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12983413475203021427775203 19475120212804532141662805)
                ·
                  refine ⟨228224064993803111035111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19475120212804532141662805 228224064993803111035111)
                  ·
                    rfl

theorem cell23_4000183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 8].length) (baseStart_4000183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000183 prefixEnd_4000183 := by exact prefixLift 4000183
  have htrace : WordTrace (prefixWord ++ tailWord_4000183) baseStart_4000183 baseEnd_4000183 := by
    simpa [prefixWord, tailWord_4000183, baseEnd_4000183] using wordTrace_append hprefix tailTrace_4000183
  have hstable : (prefixWord ++ tailWord_4000183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000183).length < 2 ^ (prefixWord ++ tailWord_4000183).sum := by decide
  have hdescent : baseEnd_4000183 < baseStart_4000183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000250 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2]
def baseStart_4000250 : Nat := 118140960795 + 4000250 * 2 ^ 59
def prefixEnd_4000250 : Nat := 4983230072969 + 3 ^ 40 * 4000250 * 2
def baseEnd_4000250 : Nat := 2054050988148079237178191

theorem tailTrace_4000250 : CollatzResearch.WordTrace tailWord_4000250 prefixEnd_4000250 2054050988148079237178191 := by
  unfold tailWord_4000250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36475275939446228288427551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97267402505189942102473469 36475275939446228288427551)
  ·
    refine ⟨54712913909169342432641327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36475275939446228288427551 54712913909169342432641327)
    ·
      refine ⟨82069370863754013648961991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54712913909169342432641327 82069370863754013648961991)
      ·
        refine ⟨123104056295631020473442987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82069370863754013648961991 123104056295631020473442987)
        ·
          refine ⟨184656084443446530710164481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123104056295631020473442987 184656084443446530710164481)
          ·
            refine ⟨138492063332584898032623361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184656084443446530710164481 138492063332584898032623361)
            ·
              refine ⟨103869047499438673524467521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138492063332584898032623361 103869047499438673524467521)
              ·
                refine ⟨77901785624579005143350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103869047499438673524467521 77901785624579005143350641)
                ·
                  refine ⟨58426339218434253857512981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77901785624579005143350641 58426339218434253857512981)
                  ·
                    refine ⟨2738734650864105649570921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58426339218434253857512981 2738734650864105649570921)
                    ·
                      refine ⟨2054050988148079237178191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738734650864105649570921 2054050988148079237178191)
                      ·
                        rfl

theorem cell23_4000250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_4000250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000250 prefixEnd_4000250 := by exact prefixLift 4000250
  have htrace : WordTrace (prefixWord ++ tailWord_4000250) baseStart_4000250 baseEnd_4000250 := by
    simpa [prefixWord, tailWord_4000250, baseEnd_4000250] using wordTrace_append hprefix tailTrace_4000250
  have hstable : (prefixWord ++ tailWord_4000250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000250).length < 2 ^ (prefixWord ++ tailWord_4000250).sum := by decide
  have hdescent : baseEnd_4000250 < baseStart_4000250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000267 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 4]
def baseStart_4000267 : Nat := 118140960795 + 4000267 * 2 ^ 59
def prefixEnd_4000267 : Nat := 4983230072969 + 3 ^ 40 * 4000267 * 2
def baseEnd_4000267 : Nat := 2054059717319205670665613

theorem tailTrace_4000267 : CollatzResearch.WordTrace tailWord_4000267 prefixEnd_4000267 2054059717319205670665613 := by
  unfold tailWord_4000267
  simp only [CollatzResearch.WordTrace]
  refine ⟨145901723798723325057079055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97267815865815550038052703 145901723798723325057079055)
  ·
    refine ⟨218852585698084987585618583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145901723798723325057079055 218852585698084987585618583)
    ·
      refine ⟨328278878547127481378427875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218852585698084987585618583 328278878547127481378427875)
      ·
        refine ⟨492418317820691222067641813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328278878547127481378427875 492418317820691222067641813)
        ·
          refine ⟨11541054323922450517210355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 492418317820691222067641813 11541054323922450517210355)
          ·
            refine ⟨17311581485883675775815533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11541054323922450517210355 17311581485883675775815533)
            ·
              refine ⟨6491843057206378415930825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17311581485883675775815533 6491843057206378415930825)
              ·
                refine ⟨4868882292904783811948119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6491843057206378415930825 4868882292904783811948119)
                ·
                  refine ⟨7303323439357175717922179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868882292904783811948119 7303323439357175717922179)
                  ·
                    refine ⟨10954985159035763576883269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303323439357175717922179 10954985159035763576883269)
                    ·
                      refine ⟨2054059717319205670665613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10954985159035763576883269 2054059717319205670665613)
                      ·
                        rfl

theorem cell23_4000267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 4].length) (baseStart_4000267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000267 prefixEnd_4000267 := by exact prefixLift 4000267
  have htrace : WordTrace (prefixWord ++ tailWord_4000267) baseStart_4000267 baseEnd_4000267 := by
    simpa [prefixWord, tailWord_4000267, baseEnd_4000267] using wordTrace_append hprefix tailTrace_4000267
  have hstable : (prefixWord ++ tailWord_4000267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000267).length < 2 ^ (prefixWord ++ tailWord_4000267).sum := by decide
  have hdescent : baseEnd_4000267 < baseStart_4000267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000280 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4000280 : Nat := 118140960795 + 4000280 * 2 ^ 59
def prefixEnd_4000280 : Nat := 4983230072969 + 3 ^ 40 * 4000280 * 2
def baseEnd_4000280 : Nat := 2054066392567714119803053

theorem tailTrace_4000280 : CollatzResearch.WordTrace tailWord_4000280 prefixEnd_4000280 2054066392567714119803053 := by
  unfold tailWord_4000280
  simp only [CollatzResearch.WordTrace]
  refine ⟨72951098973838114138651147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97268131965117485518201529 72951098973838114138651147)
  ·
    refine ⟨109426648460757171207976721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72951098973838114138651147 109426648460757171207976721)
    ·
      refine ⟨82069986345567878405982541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109426648460757171207976721 82069986345567878405982541)
      ·
        refine ⟨30776244879587954402243453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82069986345567878405982541 30776244879587954402243453)
        ·
          refine ⟨11541091829845482900841295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30776244879587954402243453 11541091829845482900841295)
          ·
            refine ⟨17311637744768224351261943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11541091829845482900841295 17311637744768224351261943)
            ·
              refine ⟨25967456617152336526892915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17311637744768224351261943 25967456617152336526892915)
              ·
                refine ⟨38951184925728504790339373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25967456617152336526892915 38951184925728504790339373)
                ·
                  refine ⟨14606694347148189296377265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38951184925728504790339373 14606694347148189296377265)
                  ·
                    refine ⟨10955020760361141972282949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14606694347148189296377265 10955020760361141972282949)
                    ·
                      refine ⟨2054066392567714119803053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10955020760361141972282949 2054066392567714119803053)
                      ·
                        rfl

theorem cell23_4000280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4000280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000280 prefixEnd_4000280 := by exact prefixLift 4000280
  have htrace : WordTrace (prefixWord ++ tailWord_4000280) baseStart_4000280 baseEnd_4000280 := by
    simpa [prefixWord, tailWord_4000280, baseEnd_4000280] using wordTrace_append hprefix tailTrace_4000280
  have hstable : (prefixWord ++ tailWord_4000280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000280).length < 2 ^ (prefixWord ++ tailWord_4000280).sum := by decide
  have hdescent : baseEnd_4000280 < baseStart_4000280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000284 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_4000284 : Nat := 118140960795 + 4000284 * 2 ^ 59
def prefixEnd_4000284 : Nat := 4983230072969 + 3 ^ 40 * 4000284 * 2
def baseEnd_4000284 : Nat := 2054068446490332104153035

theorem tailTrace_4000284 : CollatzResearch.WordTrace tailWord_4000284 prefixEnd_4000284 2054068446490332104153035 := by
  unfold tailWord_4000284
  simp only [CollatzResearch.WordTrace]
  refine ⟨72951171919830868480223953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97268229226441157973631937 72951171919830868480223953)
  ·
    refine ⟨54713378939873151360167965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72951171919830868480223953 54713378939873151360167965)
    ·
      refine ⟨20517517102452431760062987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54713378939873151360167965 20517517102452431760062987)
      ·
        refine ⟨30776275653678647640094481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20517517102452431760062987 30776275653678647640094481)
        ·
          refine ⟨23082206740258985730070861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30776275653678647640094481 23082206740258985730070861)
          ·
            refine ⟨8655827527597119648776573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23082206740258985730070861 8655827527597119648776573)
            ·
              refine ⟨3245935322848919868291215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8655827527597119648776573 3245935322848919868291215)
              ·
                refine ⟨4868902984273379802436823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245935322848919868291215 4868902984273379802436823)
                ·
                  refine ⟨7303354476410069703655235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868902984273379802436823 7303354476410069703655235)
                  ·
                    refine ⟨10955031714615104555482853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303354476410069703655235 10955031714615104555482853)
                    ·
                      refine ⟨2054068446490332104153035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10955031714615104555482853 2054068446490332104153035)
                      ·
                        rfl

theorem cell23_4000284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_4000284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000284 prefixEnd_4000284 := by exact prefixLift 4000284
  have htrace : WordTrace (prefixWord ++ tailWord_4000284) baseStart_4000284 baseEnd_4000284 := by
    simpa [prefixWord, tailWord_4000284, baseEnd_4000284] using wordTrace_append hprefix tailTrace_4000284
  have hstable : (prefixWord ++ tailWord_4000284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000284).length < 2 ^ (prefixWord ++ tailWord_4000284).sum := by decide
  have hdescent : baseEnd_4000284 < baseStart_4000284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000317 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_4000317 : Nat := 118140960795 + 4000317 * 2 ^ 59
def prefixEnd_4000317 : Nat := 4983230072969 + 3 ^ 40 * 4000317 * 2
def baseEnd_4000317 : Nat := 2054085391351930475040383

theorem tailTrace_4000317 : CollatzResearch.WordTrace tailWord_4000317 prefixEnd_4000317 2054085391351930475040383 := by
  unfold tailWord_4000317
  simp only [CollatzResearch.WordTrace]
  refine ⟨145903547448542183596399205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97269031632361455730932803 145903547448542183596399205)
  ·
    refine ⟨27356915146601659424324851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145903547448542183596399205 27356915146601659424324851)
    ·
      refine ⟨41035372719902489136487277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27356915146601659424324851 41035372719902489136487277)
      ·
        refine ⟨15388264769963433426182729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41035372719902489136487277 15388264769963433426182729)
        ·
          refine ⟨11541198577472575069637047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15388264769963433426182729 11541198577472575069637047)
          ·
            refine ⟨17311797866208862604455571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11541198577472575069637047 17311797866208862604455571)
            ·
              refine ⟨25967696799313293906683357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17311797866208862604455571 25967696799313293906683357)
              ·
                refine ⟨9737886299742485215006259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25967696799313293906683357 9737886299742485215006259)
                ·
                  refine ⟨14606829449613727822509389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9737886299742485215006259 14606829449613727822509389)
                  ·
                    refine ⟨5477561043605147933441021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14606829449613727822509389 5477561043605147933441021)
                    ·
                      refine ⟨2054085391351930475040383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5477561043605147933441021 2054085391351930475040383)
                      ·
                        rfl

theorem cell23_4000317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_4000317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000317 prefixEnd_4000317 := by exact prefixLift 4000317
  have htrace : WordTrace (prefixWord ++ tailWord_4000317) baseStart_4000317 baseEnd_4000317 := by
    simpa [prefixWord, tailWord_4000317, baseEnd_4000317] using wordTrace_append hprefix tailTrace_4000317
  have hstable : (prefixWord ++ tailWord_4000317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000317).length < 2 ^ (prefixWord ++ tailWord_4000317).sum := by decide
  have hdescent : baseEnd_4000317 < baseStart_4000317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000318 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4000318 : Nat := 118140960795 + 4000318 * 2 ^ 59
def prefixEnd_4000318 : Nat := 4983230072969 + 3 ^ 40 * 4000318 * 2
def baseEnd_4000318 : Nat := 2054085904832584971127879

theorem tailTrace_4000318 : CollatzResearch.WordTrace tailWord_4000318 prefixEnd_4000318 2054085904832584971127879 := by
  unfold tailWord_4000318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18237947990192320095898201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97269055947692373844790405 18237947990192320095898201)
  ·
    refine ⟨13678460992644240071923651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18237947990192320095898201 13678460992644240071923651)
    ·
      refine ⟨20517691488966360107885477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13678460992644240071923651 20517691488966360107885477)
      ·
        refine ⟨3847067154181192520228527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20517691488966360107885477 3847067154181192520228527)
        ·
          refine ⟨5770600731271788780342791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847067154181192520228527 5770600731271788780342791)
          ·
            refine ⟨8655901096907683170514187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5770600731271788780342791 8655901096907683170514187)
            ·
              refine ⟨12983851645361524755771281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8655901096907683170514187 12983851645361524755771281)
              ·
                refine ⟨9737888734021143566828461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12983851645361524755771281 9737888734021143566828461)
                ·
                  refine ⟨3651708275257928837560673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9737888734021143566828461 3651708275257928837560673)
                  ·
                    refine ⟨2738781206443446628170505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3651708275257928837560673 2738781206443446628170505)
                    ·
                      refine ⟨2054085904832584971127879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738781206443446628170505 2054085904832584971127879)
                      ·
                        rfl

theorem cell23_4000318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4000318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000318 prefixEnd_4000318 := by exact prefixLift 4000318
  have htrace : WordTrace (prefixWord ++ tailWord_4000318) baseStart_4000318 baseEnd_4000318 := by
    simpa [prefixWord, tailWord_4000318, baseEnd_4000318] using wordTrace_append hprefix tailTrace_4000318
  have hstable : (prefixWord ++ tailWord_4000318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000318).length < 2 ^ (prefixWord ++ tailWord_4000318).sum := by decide
  have hdescent : baseEnd_4000318 < baseStart_4000318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000380 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 7]
def baseStart_4000380 : Nat := 118140960795 + 4000380 * 2 ^ 59
def prefixEnd_4000380 : Nat := 4983230072969 + 3 ^ 40 * 4000380 * 2
def baseEnd_4000380 : Nat := 228235304514795969839177

theorem tailTrace_4000380 : CollatzResearch.WordTrace tailWord_4000380 prefixEnd_4000380 228235304514795969839177 := by
  unfold tailWord_4000380
  simp only [CollatzResearch.WordTrace]
  refine ⟨72952922623656972677971297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97270563498209296903961729 72952922623656972677971297)
  ·
    refine ⟨54714691967742729508478473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72952922623656972677971297 54714691967742729508478473)
    ·
      refine ⟨41036018975807047131358855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54714691967742729508478473 41036018975807047131358855)
      ·
        refine ⟨61554028463710570697038283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41036018975807047131358855 61554028463710570697038283)
        ·
          refine ⟨92331042695565856045557425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61554028463710570697038283 92331042695565856045557425)
          ·
            refine ⟨69248282021674392034168069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92331042695565856045557425 69248282021674392034168069)
            ·
              refine ⟨12984052879063948506406513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69248282021674392034168069 12984052879063948506406513)
              ·
                refine ⟨9738039659297961379804885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12984052879063948506406513 9738039659297961379804885)
                ·
                  refine ⟨228235304514795969839177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9738039659297961379804885 228235304514795969839177)
                  ·
                    rfl

theorem cell23_4000380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_4000380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000380 prefixEnd_4000380 := by exact prefixLift 4000380
  have htrace : WordTrace (prefixWord ++ tailWord_4000380) baseStart_4000380 baseEnd_4000380 := by
    simpa [prefixWord, tailWord_4000380, baseEnd_4000380] using wordTrace_append hprefix tailTrace_4000380
  have hstable : (prefixWord ++ tailWord_4000380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000380).length < 2 ^ (prefixWord ++ tailWord_4000380).sum := by decide
  have hdescent : baseEnd_4000380 < baseStart_4000380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000386 : List Nat := [3, 4, 3, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4000386 : Nat := 118140960795 + 4000386 * 2 ^ 59
def prefixEnd_4000386 : Nat := 4983230072969 + 3 ^ 40 * 4000386 * 2
def baseEnd_4000386 : Nat := 2054120821517090705077567

theorem tailTrace_4000386 : CollatzResearch.WordTrace tailWord_4000386 prefixEnd_4000386 2054120821517090705077567 := by
  unfold tailWord_4000386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36476516021323052095165253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97270709390194805587107341 36476516021323052095165253)
  ·
    refine ⟨6839346753998072267843485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36476516021323052095165253 6839346753998072267843485)
    ·
      refine ⟨2564755032749277100441307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6839346753998072267843485 2564755032749277100441307)
      ·
        refine ⟨3847132549123915650661961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564755032749277100441307 3847132549123915650661961)
        ·
          refine ⟨2885349411842936737996471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3847132549123915650661961 2885349411842936737996471)
          ·
            refine ⟨4328024117764405106994707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885349411842936737996471 4328024117764405106994707)
            ·
              refine ⟨6492036176646607660492061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328024117764405106994707 6492036176646607660492061)
              ·
                refine ⟨2434513566242477872684523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6492036176646607660492061 2434513566242477872684523)
                ·
                  refine ⟨3651770349363716809026785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434513566242477872684523 3651770349363716809026785)
                  ·
                    refine ⟨2738827762022787606770089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3651770349363716809026785 2738827762022787606770089)
                    ·
                      refine ⟨2054120821517090705077567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738827762022787606770089 2054120821517090705077567)
                      ·
                        rfl

theorem cell23_4000386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4000386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000386 prefixEnd_4000386 := by exact prefixLift 4000386
  have htrace : WordTrace (prefixWord ++ tailWord_4000386) baseStart_4000386 baseEnd_4000386 := by
    simpa [prefixWord, tailWord_4000386, baseEnd_4000386] using wordTrace_append hprefix tailTrace_4000386
  have hstable : (prefixWord ++ tailWord_4000386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000386).length < 2 ^ (prefixWord ++ tailWord_4000386).sum := by decide
  have hdescent : baseEnd_4000386 < baseStart_4000386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000447 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_4000447 : Nat := 118140960795 + 4000447 * 2 ^ 59
def prefixEnd_4000447 : Nat := 4983230072969 + 3 ^ 40 * 4000447 * 2
def baseEnd_4000447 : Nat := 2054152143837014966414785

theorem tailTrace_4000447 : CollatzResearch.WordTrace tailWord_4000447 prefixEnd_4000447 2054152143837014966414785 := by
  unfold tailWord_4000447
  simp only [CollatzResearch.WordTrace]
  refine ⟨145908288938071215798631595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97272192625380810532421063 145908288938071215798631595)
  ·
    refine ⟨218862433407106823697947393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145908288938071215798631595 218862433407106823697947393)
    ·
      refine ⟨164146825055330117773460545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218862433407106823697947393 164146825055330117773460545)
      ·
        refine ⟨123110118791497588330095409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164146825055330117773460545 123110118791497588330095409)
        ·
          refine ⟨92332589093623191247571557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123110118791497588330095409 92332589093623191247571557)
          ·
            refine ⟨17312360455054348358919667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92332589093623191247571557 17312360455054348358919667)
            ·
              refine ⟨25968540682581522538379501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17312360455054348358919667 25968540682581522538379501)
              ·
                refine ⟨9738202755968070951892313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25968540682581522538379501 9738202755968070951892313)
                ·
                  refine ⟨7303652066976053213919235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9738202755968070951892313 7303652066976053213919235)
                  ·
                    refine ⟨10955478100464079820878853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303652066976053213919235 10955478100464079820878853)
                    ·
                      refine ⟨2054152143837014966414785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10955478100464079820878853 2054152143837014966414785)
                      ·
                        rfl

theorem cell23_4000447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_4000447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000447 prefixEnd_4000447 := by exact prefixLift 4000447
  have htrace : WordTrace (prefixWord ++ tailWord_4000447) baseStart_4000447 baseEnd_4000447 := by
    simpa [prefixWord, tailWord_4000447, baseEnd_4000447] using wordTrace_append hprefix tailTrace_4000447
  have hstable : (prefixWord ++ tailWord_4000447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000447).length < 2 ^ (prefixWord ++ tailWord_4000447).sum := by decide
  have hdescent : baseEnd_4000447 < baseStart_4000447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000524 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 4, 3, 2]
def baseStart_4000524 : Nat := 118140960795 + 4000524 * 2 ^ 59
def prefixEnd_4000524 : Nat := 4983230072969 + 3 ^ 40 * 4000524 * 2
def baseEnd_4000524 : Nat := 2054191681847411165151931

theorem tailTrace_4000524 : CollatzResearch.WordTrace tailWord_4000524 prefixEnd_4000524 2054191681847411165151931 := by
  unfold tailWord_4000524
  simp only [CollatzResearch.WordTrace]
  refine ⟨72955548679396128974592313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97274064905861505299456417 72955548679396128974592313)
  ·
    refine ⟨54716661509547096730944235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72955548679396128974592313 54716661509547096730944235)
    ·
      refine ⟨82074992264320645096416353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54716661509547096730944235 82074992264320645096416353)
      ·
        refine ⟨61556244198240483822312265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82074992264320645096416353 61556244198240483822312265)
        ·
          refine ⟨46167183148680362866734199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61556244198240483822312265 46167183148680362866734199)
          ·
            refine ⟨69250774723020544300101299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46167183148680362866734199 69250774723020544300101299)
            ·
              refine ⟨103876162084530816450151949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69250774723020544300101299 103876162084530816450151949)
              ·
                refine ⟨38953560781699056168806981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103876162084530816450151949 38953560781699056168806981)
                ·
                  refine ⟨7303792646568573031651309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38953560781699056168806981 7303792646568573031651309)
                  ·
                    refine ⟨2738922242463214886869241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7303792646568573031651309 2738922242463214886869241)
                    ·
                      refine ⟨2054191681847411165151931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738922242463214886869241 2054191681847411165151931)
                      ·
                        rfl

theorem cell23_4000524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_4000524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000524 prefixEnd_4000524 := by exact prefixLift 4000524
  have htrace : WordTrace (prefixWord ++ tailWord_4000524) baseStart_4000524 baseEnd_4000524 := by
    simpa [prefixWord, tailWord_4000524, baseEnd_4000524] using wordTrace_append hprefix tailTrace_4000524
  have hstable : (prefixWord ++ tailWord_4000524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000524).length < 2 ^ (prefixWord ++ tailWord_4000524).sum := by decide
  have hdescent : baseEnd_4000524 < baseStart_4000524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000531 : List Nat := [1, 1, 1, 2, 1, 3, 3, 6, 1, 1, 3]
def baseStart_4000531 : Nat := 118140960795 + 4000531 * 2 ^ 59
def prefixEnd_4000531 : Nat := 4983230072969 + 3 ^ 40 * 4000531 * 2
def baseEnd_4000531 : Nat := 2054195276211992637764399

theorem tailTrace_4000531 : CollatzResearch.WordTrace tailWord_4000531 prefixEnd_4000531 2054195276211992637764399 := by
  unfold tailWord_4000531
  simp only [CollatzResearch.WordTrace]
  refine ⟨145911352669766898144689447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97274235113177932096459631 145911352669766898144689447)
  ·
    refine ⟨218867029004650347217034171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145911352669766898144689447 218867029004650347217034171)
    ·
      refine ⟨328300543506975520825551257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218867029004650347217034171 328300543506975520825551257)
      ·
        refine ⟨246225407630231640619163443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328300543506975520825551257 246225407630231640619163443)
        ·
          refine ⟨369338111445347460928745165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246225407630231640619163443 369338111445347460928745165)
          ·
            refine ⟨138501791792005297848279437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369338111445347460928745165 138501791792005297848279437)
            ·
              refine ⟨51938171922001986693104789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138501791792005297848279437 51938171922001986693104789)
              ·
                refine ⟨2434601808843843126239287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51938171922001986693104789 2434601808843843126239287)
                ·
                  refine ⟨3651902713265764689358931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434601808843843126239287 3651902713265764689358931)
                  ·
                    refine ⟨5477854069898647034038397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3651902713265764689358931 5477854069898647034038397)
                    ·
                      refine ⟨2054195276211992637764399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5477854069898647034038397 2054195276211992637764399)
                      ·
                        rfl

theorem cell23_4000531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 1, 3].length) (baseStart_4000531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000531 prefixEnd_4000531 := by exact prefixLift 4000531
  have htrace : WordTrace (prefixWord ++ tailWord_4000531) baseStart_4000531 baseEnd_4000531 := by
    simpa [prefixWord, tailWord_4000531, baseEnd_4000531] using wordTrace_append hprefix tailTrace_4000531
  have hstable : (prefixWord ++ tailWord_4000531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000531).length < 2 ^ (prefixWord ++ tailWord_4000531).sum := by decide
  have hdescent : baseEnd_4000531 < baseStart_4000531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000537 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_4000537 : Nat := 118140960795 + 4000537 * 2 ^ 59
def prefixEnd_4000537 : Nat := 4983230072969 + 3 ^ 40 * 4000537 * 2
def baseEnd_4000537 : Nat := 2054198357095919614289371

theorem tailTrace_4000537 : CollatzResearch.WordTrace tailWord_4000537 prefixEnd_4000537 2054198357095919614289371 := by
  unfold tailWord_4000537
  simp only [CollatzResearch.WordTrace]
  refine ⟨145911571507745161169407865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97274381005163440779605243 145911571507745161169407865)
  ·
    refine ⟨109433678630808870877055899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145911571507745161169407865 109433678630808870877055899)
    ·
      refine ⟨164150517946213306315583849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109433678630808870877055899 164150517946213306315583849)
      ·
        refine ⟨123112888459659979736687887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164150517946213306315583849 123112888459659979736687887)
        ·
          refine ⟨184669332689489969605031831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123112888459659979736687887 184669332689489969605031831)
          ·
            refine ⟨277003999034234954407547747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184669332689489969605031831 277003999034234954407547747)
            ·
              refine ⟨415505998551352431611321621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277003999034234954407547747 415505998551352431611321621)
              ·
                refine ⟨19476843682094645231780701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 415505998551352431611321621 19476843682094645231780701)
                ·
                  refine ⟨7303816380785491961917763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19476843682094645231780701 7303816380785491961917763)
                  ·
                    refine ⟨10955724571178237942876645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303816380785491961917763 10955724571178237942876645)
                    ·
                      refine ⟨2054198357095919614289371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10955724571178237942876645 2054198357095919614289371)
                      ·
                        rfl

theorem cell23_4000537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_4000537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000537 prefixEnd_4000537 := by exact prefixLift 4000537
  have htrace : WordTrace (prefixWord ++ tailWord_4000537) baseStart_4000537 baseEnd_4000537 := by
    simpa [prefixWord, tailWord_4000537, baseEnd_4000537] using wordTrace_append hprefix tailTrace_4000537
  have hstable : (prefixWord ++ tailWord_4000537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000537).length < 2 ^ (prefixWord ++ tailWord_4000537).sum := by decide
  have hdescent : baseEnd_4000537 < baseStart_4000537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000565 : List Nat := [1, 3, 3, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_4000565 : Nat := 118140960795 + 4000565 * 2 ^ 59
def prefixEnd_4000565 : Nat := 4983230072969 + 3 ^ 40 * 4000565 * 2
def baseEnd_4000565 : Nat := 2054212734554245504739243

theorem tailTrace_4000565 : CollatzResearch.WordTrace tailWord_4000565 prefixEnd_4000565 2054212734554245504739243 := by
  unfold tailWord_4000565
  simp only [CollatzResearch.WordTrace]
  refine ⟨145912592751643721951427149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97275061834429147967618099 145912592751643721951427149)
  ·
    refine ⟨54717222281866395731785181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145912592751643721951427149 54717222281866395731785181)
    ·
      refine ⟨20518958355699898399419443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54717222281866395731785181 20518958355699898399419443)
      ·
        refine ⟨30778437533549847599129165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20518958355699898399419443 30778437533549847599129165)
        ·
          refine ⟨11541914075081192849673437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30778437533549847599129165 11541914075081192849673437)
          ·
            refine ⟨4328217778155447318627539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11541914075081192849673437 4328217778155447318627539)
            ·
              refine ⟨6492326667233170977941309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328217778155447318627539 6492326667233170977941309)
              ·
                refine ⟨2434622500212439116727991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6492326667233170977941309 2434622500212439116727991)
                ·
                  refine ⟨3651933750318658675091987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434622500212439116727991 3651933750318658675091987)
                  ·
                    refine ⟨5477900625477988012637981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3651933750318658675091987 5477900625477988012637981)
                    ·
                      refine ⟨2054212734554245504739243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5477900625477988012637981 2054212734554245504739243)
                      ·
                        rfl

theorem cell23_4000565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_4000565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000565 prefixEnd_4000565 := by exact prefixLift 4000565
  have htrace : WordTrace (prefixWord ++ tailWord_4000565) baseStart_4000565 baseEnd_4000565 := by
    simpa [prefixWord, tailWord_4000565, baseEnd_4000565] using wordTrace_append hprefix tailTrace_4000565
  have hstable : (prefixWord ++ tailWord_4000565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000565).length < 2 ^ (prefixWord ++ tailWord_4000565).sum := by decide
  have hdescent : baseEnd_4000565 < baseStart_4000565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000567 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_4000567 : Nat := 118140960795 + 4000567 * 2 ^ 59
def prefixEnd_4000567 : Nat := 4983230072969 + 3 ^ 40 * 4000567 * 2
def baseEnd_4000567 : Nat := 2054213761515554496914233

theorem tailTrace_4000567 : CollatzResearch.WordTrace tailWord_4000567 prefixEnd_4000567 2054213761515554496914233 := by
  unfold tailWord_4000567
  simp only [CollatzResearch.WordTrace]
  refine ⟨145912665697636476292999955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97275110465090984195333303 145912665697636476292999955)
  ·
    refine ⟨218868998546454714439499933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145912665697636476292999955 218868998546454714439499933)
    ·
      refine ⟨82075874454920517914812475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218868998546454714439499933 82075874454920517914812475)
      ·
        refine ⟨123113811682380776872218713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82075874454920517914812475 123113811682380776872218713)
        ·
          refine ⟨92335358761785582654164035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123113811682380776872218713 92335358761785582654164035)
          ·
            refine ⟨138503038142678373981246053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92335358761785582654164035 138503038142678373981246053)
            ·
              refine ⟨25969319651752195121483635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138503038142678373981246053 25969319651752195121483635)
              ·
                refine ⟨38953979477628292682225453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25969319651752195121483635 38953979477628292682225453)
                ·
                  refine ⟨14607742304110609755834545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38953979477628292682225453 14607742304110609755834545)
                  ·
                    refine ⟨10955806728082957316875909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14607742304110609755834545 10955806728082957316875909)
                    ·
                      refine ⟨2054213761515554496914233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10955806728082957316875909 2054213761515554496914233)
                      ·
                        rfl

theorem cell23_4000567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_4000567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000567 prefixEnd_4000567 := by exact prefixLift 4000567
  have htrace : WordTrace (prefixWord ++ tailWord_4000567) baseStart_4000567 baseEnd_4000567 := by
    simpa [prefixWord, tailWord_4000567, baseEnd_4000567] using wordTrace_append hprefix tailTrace_4000567
  have hstable : (prefixWord ++ tailWord_4000567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000567).length < 2 ^ (prefixWord ++ tailWord_4000567).sum := by decide
  have hdescent : baseEnd_4000567 < baseStart_4000567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000582 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4000582 : Nat := 118140960795 + 4000582 * 2 ^ 59
def prefixEnd_4000582 : Nat := 4983230072969 + 3 ^ 40 * 4000582 * 2
def baseEnd_4000582 : Nat := 2054221463725371938226665

theorem tailTrace_4000582 : CollatzResearch.WordTrace tailWord_4000582 prefixEnd_4000582 2054221463725371938226665 := by
  unfold tailWord_4000582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559787899768191682962375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97275475195054755903197333 4559787899768191682962375)
  ·
    refine ⟨6839681849652287524443563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4559787899768191682962375 6839681849652287524443563)
    ·
      refine ⟨10259522774478431286665345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839681849652287524443563 10259522774478431286665345)
      ·
        refine ⟨7694642080858823464999009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10259522774478431286665345 7694642080858823464999009)
        ·
          refine ⟨5770981560644117598749257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7694642080858823464999009 5770981560644117598749257)
          ·
            refine ⟨4328236170483088199061943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5770981560644117598749257 4328236170483088199061943)
            ·
              refine ⟨6492354255724632298592915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328236170483088199061943 6492354255724632298592915)
              ·
                refine ⟨9738531383586948447889373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492354255724632298592915 9738531383586948447889373)
                ·
                  refine ⟨3651949268845105667958515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9738531383586948447889373 3651949268845105667958515)
                  ·
                    refine ⟨5477923903267658501937773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3651949268845105667958515 5477923903267658501937773)
                    ·
                      refine ⟨2054221463725371938226665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5477923903267658501937773 2054221463725371938226665)
                      ·
                        rfl

theorem cell23_4000582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4000582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000582 prefixEnd_4000582 := by exact prefixLift 4000582
  have htrace : WordTrace (prefixWord ++ tailWord_4000582) baseStart_4000582 baseEnd_4000582 := by
    simpa [prefixWord, tailWord_4000582, baseEnd_4000582] using wordTrace_append hprefix tailTrace_4000582
  have hstable : (prefixWord ++ tailWord_4000582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000582).length < 2 ^ (prefixWord ++ tailWord_4000582).sum := by decide
  have hdescent : baseEnd_4000582 < baseStart_4000582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000588 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 3, 2, 2]
def baseStart_4000588 : Nat := 118140960795 + 4000588 * 2 ^ 59
def prefixEnd_4000588 : Nat := 4983230072969 + 3 ^ 40 * 4000588 * 2
def baseEnd_4000588 : Nat := 2054224544609298914751637

theorem tailTrace_4000588 : CollatzResearch.WordTrace tailWord_4000588 prefixEnd_4000588 2054224544609298914751637 := by
  unfold tailWord_4000588
  simp only [CollatzResearch.WordTrace]
  refine ⟨72956715815280198439757209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97275621087040264586342945 72956715815280198439757209)
  ·
    refine ⟨54717536861460148829817907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72956715815280198439757209 54717536861460148829817907)
    ·
      refine ⟨82076305292190223244726861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54717536861460148829817907 82076305292190223244726861)
      ·
        refine ⟨30778614484571333716772573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82076305292190223244726861 30778614484571333716772573)
        ·
          refine ⟨11541980431714250143789715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30778614484571333716772573 11541980431714250143789715)
          ·
            refine ⟨17312970647571375215684573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11541980431714250143789715 17312970647571375215684573)
            ·
              refine ⟨6492363992839265705881715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17312970647571375215684573 6492363992839265705881715)
              ·
                refine ⟨9738545989258898558822573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492363992839265705881715 9738545989258898558822573)
                ·
                  refine ⟨3651954745972086959558465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9738545989258898558822573 3651954745972086959558465)
                  ·
                    refine ⟨2738966059479065219668849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3651954745972086959558465 2738966059479065219668849)
                    ·
                      refine ⟨2054224544609298914751637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738966059479065219668849 2054224544609298914751637)
                      ·
                        rfl

theorem cell23_4000588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_4000588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000588 prefixEnd_4000588 := by exact prefixLift 4000588
  have htrace : WordTrace (prefixWord ++ tailWord_4000588) baseStart_4000588 baseEnd_4000588 := by
    simpa [prefixWord, tailWord_4000588, baseEnd_4000588] using wordTrace_append hprefix tailTrace_4000588
  have hstable : (prefixWord ++ tailWord_4000588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000588).length < 2 ^ (prefixWord ++ tailWord_4000588).sum := by decide
  have hdescent : baseEnd_4000588 < baseStart_4000588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000597 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4000597 : Nat := 118140960795 + 4000597 * 2 ^ 59
def prefixEnd_4000597 : Nat := 4983230072969 + 3 ^ 40 * 4000597 * 2
def baseEnd_4000597 : Nat := 2054229165935189379539095

theorem tailTrace_4000597 : CollatzResearch.WordTrace tailWord_4000597 prefixEnd_4000597 2054229165935189379539095 := by
  unfold tailWord_4000597
  simp only [CollatzResearch.WordTrace]
  refine ⟨145913759887527791416592045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97275839925018527611061363 145913759887527791416592045)
  ·
    refine ⟨54717659957822921781222017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145913759887527791416592045 54717659957822921781222017)
    ·
      refine ⟨41038244968367191335916513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54717659957822921781222017 41038244968367191335916513)
      ·
        refine ⟨30778683726275393501937385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41038244968367191335916513 30778683726275393501937385)
        ·
          refine ⟨23084012794706545126453039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30778683726275393501937385 23084012794706545126453039)
          ·
            refine ⟨34626019192059817689679559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23084012794706545126453039 34626019192059817689679559)
            ·
              refine ⟨51939028788089726534519339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34626019192059817689679559 51939028788089726534519339)
              ·
                refine ⟨77908543182134589801779009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51939028788089726534519339 77908543182134589801779009)
                ·
                  refine ⟨58431407386600942351334257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77908543182134589801779009 58431407386600942351334257)
                  ·
                    refine ⟨43823555539950706763500693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58431407386600942351334257 43823555539950706763500693)
                    ·
                      refine ⟨2054229165935189379539095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43823555539950706763500693 2054229165935189379539095)
                      ·
                        rfl

theorem cell23_4000597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4000597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000597 prefixEnd_4000597 := by exact prefixLift 4000597
  have htrace : WordTrace (prefixWord ++ tailWord_4000597) baseStart_4000597 baseEnd_4000597 := by
    simpa [prefixWord, tailWord_4000597, baseEnd_4000597] using wordTrace_append hprefix tailTrace_4000597
  have hstable : (prefixWord ++ tailWord_4000597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000597).length < 2 ^ (prefixWord ++ tailWord_4000597).sum := by decide
  have hdescent : baseEnd_4000597 < baseStart_4000597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000631 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 1, 3, 2]
def baseStart_4000631 : Nat := 118140960795 + 4000631 * 2 ^ 59
def prefixEnd_4000631 : Nat := 4983230072969 + 3 ^ 40 * 4000631 * 2
def baseEnd_4000631 : Nat := 2054246624277442246513939

theorem tailTrace_4000631 : CollatzResearch.WordTrace tailWord_4000631 prefixEnd_4000631 2054246624277442246513939 := by
  unfold tailWord_4000631
  simp only [CollatzResearch.WordTrace]
  refine ⟨145914999969404615223329747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97276666646269743482219831 145914999969404615223329747)
  ·
    refine ⟨218872499954106922834994621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145914999969404615223329747 218872499954106922834994621)
    ·
      refine ⟨82077187482790096063122983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218872499954106922834994621 82077187482790096063122983)
      ·
        refine ⟨123115781224185144094684475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82077187482790096063122983 123115781224185144094684475)
        ·
          refine ⟨184673671836277716142026713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123115781224185144094684475 184673671836277716142026713)
          ·
            refine ⟨138505253877208287106520035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184673671836277716142026713 138505253877208287106520035)
            ·
              refine ⟨207757880815812430659780053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138505253877208287106520035 207757880815812430659780053)
              ·
                refine ⟨4869325331620603843588595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207757880815812430659780053 4869325331620603843588595)
                ·
                  refine ⟨7303987997430905765382893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869325331620603843588595 7303987997430905765382893)
                  ·
                    refine ⟨2738995499036589662018585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7303987997430905765382893 2738995499036589662018585)
                    ·
                      refine ⟨2054246624277442246513939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2738995499036589662018585 2054246624277442246513939)
                      ·
                        rfl

theorem cell23_4000631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_4000631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000631 prefixEnd_4000631 := by exact prefixLift 4000631
  have htrace : WordTrace (prefixWord ++ tailWord_4000631) baseStart_4000631 baseEnd_4000631 := by
    simpa [prefixWord, tailWord_4000631, baseEnd_4000631] using wordTrace_append hprefix tailTrace_4000631
  have hstable : (prefixWord ++ tailWord_4000631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000631).length < 2 ^ (prefixWord ++ tailWord_4000631).sum := by decide
  have hdescent : baseEnd_4000631 < baseStart_4000631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000661 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_4000661 : Nat := 118140960795 + 4000661 * 2 ^ 59
def prefixEnd_4000661 : Nat := 4983230072969 + 3 ^ 40 * 4000661 * 2
def baseEnd_4000661 : Nat := 2054262028697077129138801

theorem tailTrace_4000661 : CollatzResearch.WordTrace tailWord_4000661 prefixEnd_4000661 2054262028697077129138801 := by
  unfold tailWord_4000661
  simp only [CollatzResearch.WordTrace]
  refine ⟨145916094159295930346921837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97277396106197286897947891 145916094159295930346921837)
  ·
    refine ⟨54718535309735973880095689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145916094159295930346921837 54718535309735973880095689)
    ·
      refine ⟨41038901482301980410071767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54718535309735973880095689 41038901482301980410071767)
      ·
        refine ⟨61558352223452970615107651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41038901482301980410071767 61558352223452970615107651)
        ·
          refine ⟨92337528335179455922661477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61558352223452970615107651 92337528335179455922661477)
          ·
            refine ⟨17313286562846147985499027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92337528335179455922661477 17313286562846147985499027)
            ·
              refine ⟨25969929844269221978248541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17313286562846147985499027 25969929844269221978248541)
              ·
                refine ⟨9738723691600958241843203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25969929844269221978248541 9738723691600958241843203)
                ·
                  refine ⟨14608085537401437362764805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9738723691600958241843203 14608085537401437362764805)
                  ·
                    refine ⟨2739016038262769505518401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14608085537401437362764805 2739016038262769505518401)
                    ·
                      refine ⟨2054262028697077129138801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739016038262769505518401 2054262028697077129138801)
                      ·
                        rfl

theorem cell23_4000661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_4000661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000661 prefixEnd_4000661 := by exact prefixLift 4000661
  have htrace : WordTrace (prefixWord ++ tailWord_4000661) baseStart_4000661 baseEnd_4000661 := by
    simpa [prefixWord, tailWord_4000661, baseEnd_4000661] using wordTrace_append hprefix tailTrace_4000661
  have hstable : (prefixWord ++ tailWord_4000661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000661).length < 2 ^ (prefixWord ++ tailWord_4000661).sum := by decide
  have hdescent : baseEnd_4000661 < baseStart_4000661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000677 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_4000677 : Nat := 118140960795 + 4000677 * 2 ^ 59
def prefixEnd_4000677 : Nat := 4983230072969 + 3 ^ 40 * 4000677 * 2
def baseEnd_4000677 : Nat := 2054270244387549066538727

theorem tailTrace_4000677 : CollatzResearch.WordTrace tailWord_4000677 prefixEnd_4000677 2054270244387549066538727 := by
  unfold tailWord_4000677
  simp only [CollatzResearch.WordTrace]
  refine ⟨145916677727237965079504285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97277785151491976719669523 145916677727237965079504285)
  ·
    refine ⟨54718754147714236904814107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145916677727237965079504285 54718754147714236904814107)
    ·
      refine ⟨82078131221571355357221161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54718754147714236904814107 82078131221571355357221161)
      ·
        refine ⟨61558598416178516517915871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82078131221571355357221161 61558598416178516517915871)
        ·
          refine ⟨92337897624267774776873807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61558598416178516517915871 92337897624267774776873807)
          ·
            refine ⟨138506846436401662165310711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92337897624267774776873807 138506846436401662165310711)
            ·
              refine ⟨207760269654602493247966067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138506846436401662165310711 207760269654602493247966067)
              ·
                refine ⟨311640404481903739871949101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207760269654602493247966067 311640404481903739871949101)
                ·
                  refine ⟨116865151680713902451980913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311640404481903739871949101 116865151680713902451980913)
                  ·
                    refine ⟨87648863760535426838985685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116865151680713902451980913 87648863760535426838985685)
                    ·
                      refine ⟨2054270244387549066538727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87648863760535426838985685 2054270244387549066538727)
                      ·
                        rfl

theorem cell23_4000677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_4000677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000677 prefixEnd_4000677 := by exact prefixLift 4000677
  have htrace : WordTrace (prefixWord ++ tailWord_4000677) baseStart_4000677 baseEnd_4000677 := by
    simpa [prefixWord, tailWord_4000677, baseEnd_4000677] using wordTrace_append hprefix tailTrace_4000677
  have hstable : (prefixWord ++ tailWord_4000677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000677).length < 2 ^ (prefixWord ++ tailWord_4000677).sum := by decide
  have hdescent : baseEnd_4000677 < baseStart_4000677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000701 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 7]
def baseStart_4000701 : Nat := 118140960795 + 4000701 * 2 ^ 59
def prefixEnd_4000701 : Nat := 4983230072969 + 3 ^ 40 * 4000701 * 2
def baseEnd_4000701 : Nat := 228253618658139663626513

theorem tailTrace_4000701 : CollatzResearch.WordTrace tailWord_4000701 prefixEnd_4000701 228253618658139663626513 := by
  unfold tailWord_4000701
  simp only [CollatzResearch.WordTrace]
  refine ⟨145917553079151017178377957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97278368719434011452251971 145917553079151017178377957)
  ·
    refine ⟨27359541202340815720945867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145917553079151017178377957 27359541202340815720945867)
    ·
      refine ⟨41039311803511223581418801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27359541202340815720945867 41039311803511223581418801)
      ·
        refine ⟨30779483852633417686064101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41039311803511223581418801 30779483852633417686064101)
        ·
          refine ⟨5771153222368765816137019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30779483852633417686064101 5771153222368765816137019)
          ·
            refine ⟨8656729833553148724205529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771153222368765816137019 8656729833553148724205529)
            ·
              refine ⟨6492547375164861543154147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8656729833553148724205529 6492547375164861543154147)
              ·
                refine ⟨9738821062747292314731221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492547375164861543154147 9738821062747292314731221)
                ·
                  refine ⟨228253618658139663626513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9738821062747292314731221 228253618658139663626513)
                  ·
                    rfl

theorem cell23_4000701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_4000701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000701 prefixEnd_4000701 := by exact prefixLift 4000701
  have htrace : WordTrace (prefixWord ++ tailWord_4000701) baseStart_4000701 baseEnd_4000701 := by
    simpa [prefixWord, tailWord_4000701, baseEnd_4000701] using wordTrace_append hprefix tailTrace_4000701
  have hstable : (prefixWord ++ tailWord_4000701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000701).length < 2 ^ (prefixWord ++ tailWord_4000701).sum := by decide
  have hdescent : baseEnd_4000701 < baseStart_4000701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000712 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_4000712 : Nat := 118140960795 + 4000712 * 2 ^ 59
def prefixEnd_4000712 : Nat := 4983230072969 + 3 ^ 40 * 4000712 * 2
def baseEnd_4000712 : Nat := 2054288216210456429601067

theorem tailTrace_4000712 : CollatzResearch.WordTrace tailWord_4000712 prefixEnd_4000712 2054288216210456429601067 := by
  unfold tailWord_4000712
  simp only [CollatzResearch.WordTrace]
  refine ⟨72958977141055583028514195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97278636188074110704685593 72958977141055583028514195)
  ·
    refine ⟨109438465711583374542771293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72958977141055583028514195 109438465711583374542771293)
    ·
      refine ⟨41039424641843765453539235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109438465711583374542771293 41039424641843765453539235)
      ·
        refine ⟨61559136962765648180308853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41039424641843765453539235 61559136962765648180308853)
        ·
          refine ⟨5771169090259279516903955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61559136962765648180308853 5771169090259279516903955)
          ·
            refine ⟨8656753635388919275355933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771169090259279516903955 8656753635388919275355933)
            ·
              refine ⟨3246282613270844728258475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8656753635388919275355933 3246282613270844728258475)
              ·
                refine ⟨4869423919906267092387713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246282613270844728258475 4869423919906267092387713)
                ·
                  refine ⟨3652067939929700319290785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4869423919906267092387713 3652067939929700319290785)
                  ·
                    refine ⟨2739050954947275239468089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3652067939929700319290785 2739050954947275239468089)
                    ·
                      refine ⟨2054288216210456429601067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739050954947275239468089 2054288216210456429601067)
                      ·
                        rfl

theorem cell23_4000712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_4000712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000712 prefixEnd_4000712 := by exact prefixLift 4000712
  have htrace : WordTrace (prefixWord ++ tailWord_4000712) baseStart_4000712 baseEnd_4000712 := by
    simpa [prefixWord, tailWord_4000712, baseEnd_4000712] using wordTrace_append hprefix tailTrace_4000712
  have hstable : (prefixWord ++ tailWord_4000712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000712).length < 2 ^ (prefixWord ++ tailWord_4000712).sum := by decide
  have hdescent : baseEnd_4000712 < baseStart_4000712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000735 : List Nat := [1, 1, 2, 3, 6, 1, 1, 3, 5]
def baseStart_4000735 : Nat := 118140960795 + 4000735 * 2 ^ 59
def prefixEnd_4000735 : Nat := 4983230072969 + 3 ^ 40 * 4000735 * 2
def baseEnd_4000735 : Nat := 228255558473945537734829

theorem tailTrace_4000735 : CollatzResearch.WordTrace tailWord_4000735 prefixEnd_4000735 228255558473945537734829 := by
  unfold tailWord_4000735
  simp only [CollatzResearch.WordTrace]
  refine ⟨145918793161027840985115659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97279195440685227323410439 145918793161027840985115659)
  ·
    refine ⟨218878189741541761477673489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145918793161027840985115659 218878189741541761477673489)
    ·
      refine ⟨164158642306156321108255117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218878189741541761477673489 164158642306156321108255117)
      ·
        refine ⟨61559490864808620415595669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164158642306156321108255117 61559490864808620415595669)
        ·
          refine ⟨2885601134287904081981047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61559490864808620415595669 2885601134287904081981047)
          ·
            refine ⟨4328401701431856122971571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885601134287904081981047 4328401701431856122971571)
            ·
              refine ⟨6492602552147784184457357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328401701431856122971571 6492602552147784184457357)
              ·
                refine ⟨2434725957055419069171509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6492602552147784184457357 2434725957055419069171509)
                ·
                  refine ⟨228255558473945537734829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2434725957055419069171509 228255558473945537734829)
                  ·
                    rfl

theorem cell23_4000735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 5].length) (baseStart_4000735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000735 prefixEnd_4000735 := by exact prefixLift 4000735
  have htrace : WordTrace (prefixWord ++ tailWord_4000735) baseStart_4000735 baseEnd_4000735 := by
    simpa [prefixWord, tailWord_4000735, baseEnd_4000735] using wordTrace_append hprefix tailTrace_4000735
  have hstable : (prefixWord ++ tailWord_4000735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000735).length < 2 ^ (prefixWord ++ tailWord_4000735).sum := by decide
  have hdescent : baseEnd_4000735 < baseStart_4000735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000751 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_4000751 : Nat := 118140960795 + 4000751 * 2 ^ 59
def prefixEnd_4000751 : Nat := 4983230072969 + 3 ^ 40 * 4000751 * 2
def baseEnd_4000751 : Nat := 2054308241955981777013387

theorem tailTrace_4000751 : CollatzResearch.WordTrace tailWord_4000751 prefixEnd_4000751 2054308241955981777013387 := by
  unfold tailWord_4000751
  simp only [CollatzResearch.WordTrace]
  refine ⟨145919376728969875717698107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97279584485979917145132071 145919376728969875717698107)
  ·
    refine ⟨218879065093454813576547161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145919376728969875717698107 218879065093454813576547161)
    ·
      refine ⟨164159298820091110182410371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218879065093454813576547161 164159298820091110182410371)
      ·
        refine ⟨246238948230136665273615557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164159298820091110182410371 246238948230136665273615557)
        ·
          refine ⟨46169802793150624738802917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246238948230136665273615557 46169802793150624738802917)
          ·
            refine ⟨8656838023715742138525547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46169802793150624738802917 8656838023715742138525547)
            ·
              refine ⟨12985257035573613207788321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656838023715742138525547 12985257035573613207788321)
              ·
                refine ⟨9738942776680209905841241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12985257035573613207788321 9738942776680209905841241)
                ·
                  refine ⟨7304207082510157429380931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9738942776680209905841241 7304207082510157429380931)
                  ·
                    refine ⟨10956310623765236144071397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304207082510157429380931 10956310623765236144071397)
                    ·
                      refine ⟨2054308241955981777013387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10956310623765236144071397 2054308241955981777013387)
                      ·
                        rfl

theorem cell23_4000751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_4000751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000751 prefixEnd_4000751 := by exact prefixLift 4000751
  have htrace : WordTrace (prefixWord ++ tailWord_4000751) baseStart_4000751 baseEnd_4000751 := by
    simpa [prefixWord, tailWord_4000751, baseEnd_4000751] using wordTrace_append hprefix tailTrace_4000751
  have hstable : (prefixWord ++ tailWord_4000751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000751).length < 2 ^ (prefixWord ++ tailWord_4000751).sum := by decide
  have hdescent : baseEnd_4000751 < baseStart_4000751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000818 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_4000818 : Nat := 118140960795 + 4000818 * 2 ^ 59
def prefixEnd_4000818 : Nat := 4983230072969 + 3 ^ 40 * 4000818 * 2
def baseEnd_4000818 : Nat := 2054342645159833014875579

theorem tailTrace_4000818 : CollatzResearch.WordTrace tailWord_4000818 prefixEnd_4000818 2054342645159833014875579 := by
  unfold tailWord_4000818
  simp only [CollatzResearch.WordTrace]
  refine ⟨36480455104931786540096777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97281213613151430773591405 36480455104931786540096777)
  ·
    refine ⟨27360341328698839905072583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36480455104931786540096777 27360341328698839905072583)
    ·
      refine ⟨41040511993048259857608875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27360341328698839905072583 41040511993048259857608875)
      ·
        refine ⟨61560767989572389786413313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41040511993048259857608875 61560767989572389786413313)
        ·
          refine ⟨46170575992179292339809985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61560767989572389786413313 46170575992179292339809985)
          ·
            refine ⟨34627931994134469254857489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46170575992179292339809985 34627931994134469254857489)
            ·
              refine ⟨25970948995600851941143117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34627931994134469254857489 25970948995600851941143117)
              ·
                refine ⟨9739105873350319477928669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25970948995600851941143117 9739105873350319477928669)
                ·
                  refine ⟨3652164702506369804223251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9739105873350319477928669 3652164702506369804223251)
                  ·
                    refine ⟨5478247053759554706334877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652164702506369804223251 5478247053759554706334877)
                    ·
                      refine ⟨2054342645159833014875579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5478247053759554706334877 2054342645159833014875579)
                      ·
                        rfl

theorem cell23_4000818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_4000818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000818 prefixEnd_4000818 := by exact prefixLift 4000818
  have htrace : WordTrace (prefixWord ++ tailWord_4000818) baseStart_4000818 baseEnd_4000818 := by
    simpa [prefixWord, tailWord_4000818, baseEnd_4000818] using wordTrace_append hprefix tailTrace_4000818
  have hstable : (prefixWord ++ tailWord_4000818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000818).length < 2 ^ (prefixWord ++ tailWord_4000818).sum := by decide
  have hdescent : baseEnd_4000818 < baseStart_4000818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000841 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 8, 2]
def baseStart_4000841 : Nat := 118140960795 + 4000841 * 2 ^ 59
def prefixEnd_4000841 : Nat := 4983230072969 + 3 ^ 40 * 4000841 * 2
def baseEnd_4000841 : Nat := 2054354455214886424887973

theorem tailTrace_4000841 : CollatzResearch.WordTrace tailWord_4000841 prefixEnd_4000841 2054354455214886424887973 := by
  unfold tailWord_4000841
  simp only [CollatzResearch.WordTrace]
  refine ⟨145922659298643821088474377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97281772865762547392316251 145922659298643821088474377)
  ·
    refine ⟨109441994473982865816355783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145922659298643821088474377 109441994473982865816355783)
    ·
      refine ⟨164162991710974298724533675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109441994473982865816355783 164162991710974298724533675)
      ·
        refine ⟨246244487566461448086800513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164162991710974298724533675 246244487566461448086800513)
        ·
          refine ⟨184683365674846086065100385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246244487566461448086800513 184683365674846086065100385)
          ·
            refine ⟨138512524256134564548825289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184683365674846086065100385 138512524256134564548825289)
            ·
              refine ⟨103884393192100923411618967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138512524256134564548825289 103884393192100923411618967)
              ·
                refine ⟨155826589788151385117428451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103884393192100923411618967 155826589788151385117428451)
                ·
                  refine ⟨233739884682227077676142677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155826589788151385117428451 233739884682227077676142677)
                  ·
                    refine ⟨2739139273619848566517297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 233739884682227077676142677 2739139273619848566517297)
                    ·
                      refine ⟨2054354455214886424887973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739139273619848566517297 2054354455214886424887973)
                      ·
                        rfl

theorem cell23_4000841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 8, 2].length) (baseStart_4000841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000841 prefixEnd_4000841 := by exact prefixLift 4000841
  have htrace : WordTrace (prefixWord ++ tailWord_4000841) baseStart_4000841 baseEnd_4000841 := by
    simpa [prefixWord, tailWord_4000841, baseEnd_4000841] using wordTrace_append hprefix tailTrace_4000841
  have hstable : (prefixWord ++ tailWord_4000841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000841).length < 2 ^ (prefixWord ++ tailWord_4000841).sum := by decide
  have hdescent : baseEnd_4000841 < baseStart_4000841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000845 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_4000845 : Nat := 118140960795 + 4000845 * 2 ^ 59
def prefixEnd_4000845 : Nat := 4983230072969 + 3 ^ 40 * 4000845 * 2
def baseEnd_4000845 : Nat := 2054356509137504409237955

theorem tailTrace_4000845 : CollatzResearch.WordTrace tailWord_4000845 prefixEnd_4000845 2054356509137504409237955 := by
  unfold tailWord_4000845
  simp only [CollatzResearch.WordTrace]
  refine ⟨145922805190629329771619989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97281870127086219847746659 145922805190629329771619989)
  ·
    refine ⟨6840131493310749833044687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145922805190629329771619989 6840131493310749833044687)
    ·
      refine ⟨10260197239966124749567031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840131493310749833044687 10260197239966124749567031)
      ·
        refine ⟨15390295859949187124350547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260197239966124749567031 15390295859949187124350547)
        ·
          refine ⟨23085443789923780686525821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390295859949187124350547 23085443789923780686525821)
          ·
            refine ⟨8657041421221417757447183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23085443789923780686525821 8657041421221417757447183)
            ·
              refine ⟨12985562131832126636170775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657041421221417757447183 12985562131832126636170775)
              ·
                refine ⟨19478343197748189954256163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12985562131832126636170775 19478343197748189954256163)
                ·
                  refine ⟨29217514796622284931384245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19478343197748189954256163 29217514796622284931384245)
                  ·
                    refine ⟨2739142012183339212317273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29217514796622284931384245 2739142012183339212317273)
                    ·
                      refine ⟨2054356509137504409237955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739142012183339212317273 2054356509137504409237955)
                      ·
                        rfl

theorem cell23_4000845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_4000845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000845 prefixEnd_4000845 := by exact prefixLift 4000845
  have htrace : WordTrace (prefixWord ++ tailWord_4000845) baseStart_4000845 baseEnd_4000845 := by
    simpa [prefixWord, tailWord_4000845, baseEnd_4000845] using wordTrace_append hprefix tailTrace_4000845
  have hstable : (prefixWord ++ tailWord_4000845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000845).length < 2 ^ (prefixWord ++ tailWord_4000845).sum := by decide
  have hdescent : baseEnd_4000845 < baseStart_4000845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000864 : List Nat := [2, 1, 1, 3, 2, 2, 12]
def baseStart_4000864 : Nat := 118140960795 + 4000864 * 2 ^ 59
def prefixEnd_4000864 : Nat := 4983230072969 + 3 ^ 40 * 4000864 * 2
def baseEnd_4000864 : Nat := 25362546484814072035807

theorem tailTrace_4000864 : CollatzResearch.WordTrace tailWord_4000864 prefixEnd_4000864 25362546484814072035807 := by
  unfold tailWord_4000864
  simp only [CollatzResearch.WordTrace]
  refine ⟨72961749088780248008280823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97282332118373664011041097 72961749088780248008280823)
  ·
    refine ⟨109442623633170372012421235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72961749088780248008280823 109442623633170372012421235)
    ·
      refine ⟨164163935449755558018631853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109442623633170372012421235 164163935449755558018631853)
      ·
        refine ⟨61561475793658334256986945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164163935449755558018631853 61561475793658334256986945)
        ·
          refine ⟨46171106845243750692740209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61561475793658334256986945 46171106845243750692740209)
          ·
            refine ⟨34628330133932813019555157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46171106845243750692740209 34628330133932813019555157)
            ·
              refine ⟨25362546484814072035807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34628330133932813019555157 25362546484814072035807)
              ·
                rfl

theorem cell23_4000864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 12].length) (baseStart_4000864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000864 prefixEnd_4000864 := by exact prefixLift 4000864
  have htrace : WordTrace (prefixWord ++ tailWord_4000864) baseStart_4000864 baseEnd_4000864 := by
    simpa [prefixWord, tailWord_4000864, baseEnd_4000864] using wordTrace_append hprefix tailTrace_4000864
  have hstable : (prefixWord ++ tailWord_4000864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000864).length < 2 ^ (prefixWord ++ tailWord_4000864).sum := by decide
  have hdescent : baseEnd_4000864 < baseStart_4000864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000878 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4000878 : Nat := 118140960795 + 4000878 * 2 ^ 59
def prefixEnd_4000878 : Nat := 4983230072969 + 3 ^ 40 * 4000878 * 2
def baseEnd_4000878 : Nat := 2054373453999102780125303

theorem tailTrace_4000878 : CollatzResearch.WordTrace tailWord_4000878 prefixEnd_4000878 2054373453999102780125303 := by
  unfold tailWord_4000878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18240501099938722050946411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97282672533006517605047525 18240501099938722050946411)
  ·
    refine ⟨27360751649908083076419617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18240501099938722050946411 27360751649908083076419617)
    ·
      refine ⟨20520563737431062307314713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27360751649908083076419617 20520563737431062307314713)
      ·
        refine ⟨15390422803073296730486035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20520563737431062307314713 15390422803073296730486035)
        ·
          refine ⟨23085634204609945095729053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390422803073296730486035 23085634204609945095729053)
          ·
            refine ⟨8657112826728729410898395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23085634204609945095729053 8657112826728729410898395)
            ·
              refine ⟨12985669240093094116347593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657112826728729410898395 12985669240093094116347593)
              ·
                refine ⟨9739251930069820587260695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12985669240093094116347593 9739251930069820587260695)
                ·
                  refine ⟨14608877895104730880891043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9739251930069820587260695 14608877895104730880891043)
                  ·
                    refine ⟨21913316842657096321336565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14608877895104730880891043 21913316842657096321336565)
                    ·
                      refine ⟨2054373453999102780125303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21913316842657096321336565 2054373453999102780125303)
                      ·
                        rfl

theorem cell23_4000878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4000878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000878 prefixEnd_4000878 := by exact prefixLift 4000878
  have htrace : WordTrace (prefixWord ++ tailWord_4000878) baseStart_4000878 baseEnd_4000878 := by
    simpa [prefixWord, tailWord_4000878, baseEnd_4000878] using wordTrace_append hprefix tailTrace_4000878
  have hstable : (prefixWord ++ tailWord_4000878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000878).length < 2 ^ (prefixWord ++ tailWord_4000878).sum := by decide
  have hdescent : baseEnd_4000878 < baseStart_4000878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000925 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_4000925 : Nat := 118140960795 + 4000925 * 2 ^ 59
def prefixEnd_4000925 : Nat := 4983230072969 + 3 ^ 40 * 4000925 * 2
def baseEnd_4000925 : Nat := 2054397587589864096237587

theorem tailTrace_4000925 : CollatzResearch.WordTrace tailWord_4000925 prefixEnd_4000925 2054397587589864096237587 := by
  unfold tailWord_4000925
  simp only [CollatzResearch.WordTrace]
  refine ⟨145925723030339503434532229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97283815353559668956354819 145925723030339503434532229)
  ·
    refine ⟨27361073068188656893974793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145925723030339503434532229 27361073068188656893974793)
    ·
      refine ⟨20520804801141492670481095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27361073068188656893974793 20520804801141492670481095)
      ·
        refine ⟨30781207201712239005721643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20520804801141492670481095 30781207201712239005721643)
        ·
          refine ⟨46171810802568358508582465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30781207201712239005721643 46171810802568358508582465)
          ·
            refine ⟨34628858101926268881436849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46171810802568358508582465 34628858101926268881436849)
            ·
              refine ⟨25971643576444701661077637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34628858101926268881436849 25971643576444701661077637)
              ·
                refine ⟨4869683170583381561452057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25971643576444701661077637 4869683170583381561452057)
                ·
                  refine ⟨3652262377937536171089043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4869683170583381561452057 3652262377937536171089043)
                  ·
                    refine ⟨5478393566906304256633565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652262377937536171089043 5478393566906304256633565)
                    ·
                      refine ⟨2054397587589864096237587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5478393566906304256633565 2054397587589864096237587)
                      ·
                        rfl

theorem cell23_4000925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_4000925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000925 prefixEnd_4000925 := by exact prefixLift 4000925
  have htrace : WordTrace (prefixWord ++ tailWord_4000925) baseStart_4000925 baseEnd_4000925 := by
    simpa [prefixWord, tailWord_4000925, baseEnd_4000925] using wordTrace_append hprefix tailTrace_4000925
  have hstable : (prefixWord ++ tailWord_4000925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000925).length < 2 ^ (prefixWord ++ tailWord_4000925).sum := by decide
  have hdescent : baseEnd_4000925 < baseStart_4000925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000951 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_4000951 : Nat := 118140960795 + 4000951 * 2 ^ 59
def prefixEnd_4000951 : Nat := 4983230072969 + 3 ^ 40 * 4000951 * 2
def baseEnd_4000951 : Nat := 2054410938086880994512467

theorem tailTrace_4000951 : CollatzResearch.WordTrace tailWord_4000951 prefixEnd_4000951 2054410938086880994512467 := by
  unfold tailWord_4000951
  simp only [CollatzResearch.WordTrace]
  refine ⟨145926671328245309874978707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97284447552163539916652471 145926671328245309874978707)
  ·
    refine ⟨218890006992367964812468061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145926671328245309874978707 218890006992367964812468061)
    ·
      refine ⟨82083752622137986804675523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218890006992367964812468061 82083752622137986804675523)
      ·
        refine ⟨123125628933206980207013285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82083752622137986804675523 123125628933206980207013285)
        ·
          refine ⟨23086055424976308788814991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123125628933206980207013285 23086055424976308788814991)
          ·
            refine ⟨34629083137464463183222487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23086055424976308788814991 34629083137464463183222487)
            ·
              refine ⟨51943624706196694774833731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34629083137464463183222487 51943624706196694774833731)
              ·
                refine ⟨77915437059295042162250597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51943624706196694774833731 77915437059295042162250597)
                ·
                  refine ⟨14609144448617820405421987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77915437059295042162250597 14609144448617820405421987)
                  ·
                    refine ⟨21913716672926730608132981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14609144448617820405421987 21913716672926730608132981)
                    ·
                      refine ⟨2054410938086880994512467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21913716672926730608132981 2054410938086880994512467)
                      ·
                        rfl

theorem cell23_4000951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_4000951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000951 prefixEnd_4000951 := by exact prefixLift 4000951
  have htrace : WordTrace (prefixWord ++ tailWord_4000951) baseStart_4000951 baseEnd_4000951 := by
    simpa [prefixWord, tailWord_4000951, baseEnd_4000951] using wordTrace_append hprefix tailTrace_4000951
  have hstable : (prefixWord ++ tailWord_4000951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000951).length < 2 ^ (prefixWord ++ tailWord_4000951).sum := by decide
  have hdescent : baseEnd_4000951 < baseStart_4000951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4000978 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4000978 : Nat := 118140960795 + 4000978 * 2 ^ 59
def prefixEnd_4000978 : Nat := 4983230072969 + 3 ^ 40 * 4000978 * 2
def baseEnd_4000978 : Nat := 2054424802064552388874843

theorem tailTrace_4000978 : CollatzResearch.WordTrace tailWord_4000978 prefixEnd_4000978 2054424802064552388874843 := by
  unfold tailWord_4000978
  simp only [CollatzResearch.WordTrace]
  refine ⟨36481914024786873371552897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97285104066098328990807725 36481914024786873371552897)
  ·
    refine ⟨27361435518590155028664673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36481914024786873371552897 27361435518590155028664673)
    ·
      refine ⟨20521076638942616271498505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27361435518590155028664673 20521076638942616271498505)
      ·
        refine ⟨15390807479206962203623879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20521076638942616271498505 15390807479206962203623879)
        ·
          refine ⟨23086211218810443305435819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390807479206962203623879 23086211218810443305435819)
          ·
            refine ⟨34629316828215664958153729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23086211218810443305435819 34629316828215664958153729)
            ·
              refine ⟨25971987621161748718615297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34629316828215664958153729 25971987621161748718615297)
              ·
                refine ⟨19478990715871311538961473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25971987621161748718615297 19478990715871311538961473)
                ·
                  refine ⟨14609243036903483654221105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19478990715871311538961473 14609243036903483654221105)
                  ·
                    refine ⟨10956932277677612740665829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14609243036903483654221105 10956932277677612740665829)
                    ·
                      refine ⟨2054424802064552388874843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10956932277677612740665829 2054424802064552388874843)
                      ·
                        rfl

theorem cell23_4000978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4000978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4000978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4000978 prefixEnd_4000978 := by exact prefixLift 4000978
  have htrace : WordTrace (prefixWord ++ tailWord_4000978) baseStart_4000978 baseEnd_4000978 := by
    simpa [prefixWord, tailWord_4000978, baseEnd_4000978] using wordTrace_append hprefix tailTrace_4000978
  have hstable : (prefixWord ++ tailWord_4000978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4000978).length < 2 ^ (prefixWord ++ tailWord_4000978).sum := by decide
  have hdescent : baseEnd_4000978 < baseStart_4000978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4000978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001022 : List Nat := [4, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_4001022 : Nat := 118140960795 + 4001022 * 2 ^ 59
def prefixEnd_4001022 : Nat := 4983230072969 + 3 ^ 40 * 4001022 * 2
def baseEnd_4001022 : Nat := 228271932801483357413849

theorem tailTrace_4001022 : CollatzResearch.WordTrace tailWord_4001022 prefixEnd_4001022 228271932801483357413849 := by
  unfold tailWord_4001022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18241157613873511125101665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97286173940658726000542213 18241157613873511125101665)
  ·
    refine ⟨13680868210405133343826249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18241157613873511125101665 13680868210405133343826249)
    ·
      refine ⟨10260651157803850007869687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13680868210405133343826249 10260651157803850007869687)
      ·
        refine ⟨15390976736705775011804531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260651157803850007869687 15390976736705775011804531)
        ·
          refine ⟨23086465105058662517706797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390976736705775011804531 23086465105058662517706797)
          ·
            refine ⟨8657424414396998444140049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23086465105058662517706797 8657424414396998444140049)
            ·
              refine ⟨6493068310797748833105037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657424414396998444140049 6493068310797748833105037)
              ·
                refine ⟨2434900616549155812414389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6493068310797748833105037 2434900616549155812414389)
                ·
                  refine ⟨228271932801483357413849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2434900616549155812414389 228271932801483357413849)
                  ·
                    rfl

theorem cell23_4001022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_4001022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001022 prefixEnd_4001022 := by exact prefixLift 4001022
  have htrace : WordTrace (prefixWord ++ tailWord_4001022) baseStart_4001022 baseEnd_4001022 := by
    simpa [prefixWord, tailWord_4001022, baseEnd_4001022] using wordTrace_append hprefix tailTrace_4001022
  have hstable : (prefixWord ++ tailWord_4001022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001022).length < 2 ^ (prefixWord ++ tailWord_4001022).sum := by decide
  have hdescent : baseEnd_4001022 < baseStart_4001022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001051 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6]
def baseStart_4001051 : Nat := 118140960795 + 4001051 * 2 ^ 59
def prefixEnd_4001051 : Nat := 4983230072969 + 3 ^ 40 * 4001051 * 2
def baseEnd_4001051 : Nat := 2054462286152330603262007

theorem tailTrace_4001051 : CollatzResearch.WordTrace tailWord_4001051 prefixEnd_4001051 2054462286152330603262007 := by
  unfold tailWord_4001051
  simp only [CollatzResearch.WordTrace]
  refine ⟨145930318627883026953619007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97286879085255351302412671 145930318627883026953619007)
  ·
    refine ⟨218895477941824540430428511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145930318627883026953619007 218895477941824540430428511)
    ·
      refine ⟨328343216912736810645642767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218895477941824540430428511 328343216912736810645642767)
      ·
        refine ⟨492514825369105215968464151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328343216912736810645642767 492514825369105215968464151)
        ·
          refine ⟨738772238053657823952696227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492514825369105215968464151 738772238053657823952696227)
          ·
            refine ⟨1108158357080486735929044341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738772238053657823952696227 1108158357080486735929044341)
            ·
              refine ⟨103889845976295631493347907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1108158357080486735929044341 103889845976295631493347907)
              ·
                refine ⟨155834768964443447240021861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103889845976295631493347907 155834768964443447240021861)
                ·
                  refine ⟨29219019180833146357504099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155834768964443447240021861 29219019180833146357504099)
                  ·
                    refine ⟨43828528771249719536256149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29219019180833146357504099 43828528771249719536256149)
                    ·
                      refine ⟨2054462286152330603262007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43828528771249719536256149 2054462286152330603262007)
                      ·
                        rfl

theorem cell23_4001051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_4001051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001051 prefixEnd_4001051 := by exact prefixLift 4001051
  have htrace : WordTrace (prefixWord ++ tailWord_4001051) baseStart_4001051 baseEnd_4001051 := by
    simpa [prefixWord, tailWord_4001051, baseEnd_4001051] using wordTrace_append hprefix tailTrace_4001051
  have hstable : (prefixWord ++ tailWord_4001051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001051).length < 2 ^ (prefixWord ++ tailWord_4001051).sum := by decide
  have hdescent : baseEnd_4001051 < baseStart_4001051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001092 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4001092 : Nat := 118140960795 + 4001092 * 2 ^ 59
def prefixEnd_4001092 : Nat := 4983230072969 + 3 ^ 40 * 4001092 * 2
def baseEnd_4001092 : Nat := 2054483338859164942849319

theorem tailTrace_4001092 : CollatzResearch.WordTrace tailWord_4001092 prefixEnd_4001092 2054483338859164942849319 := by
  unfold tailWord_4001092
  simp only [CollatzResearch.WordTrace]
  refine ⟨72965907010367245477930765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97287876013822993970574353 72965907010367245477930765)
  ·
    refine ⟨27362215128887717054224037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72965907010367245477930765 27362215128887717054224037)
    ·
      refine ⟨5130415336666446947667007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27362215128887717054224037 5130415336666446947667007)
      ·
        refine ⟨7695623004999670421500511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130415336666446947667007 7695623004999670421500511)
        ·
          refine ⟨11543434507499505632250767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695623004999670421500511 11543434507499505632250767)
          ·
            refine ⟨17315151761249258448376151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543434507499505632250767 17315151761249258448376151)
            ·
              refine ⟨25972727641873887672564227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17315151761249258448376151 25972727641873887672564227)
              ·
                refine ⟨38959091462810831508846341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25972727641873887672564227 38959091462810831508846341)
                ·
                  refine ⟨7304829649277030907908689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38959091462810831508846341 7304829649277030907908689)
                  ·
                    refine ⟨5478622236957773180931517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7304829649277030907908689 5478622236957773180931517)
                    ·
                      refine ⟨2054483338859164942849319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5478622236957773180931517 2054483338859164942849319)
                      ·
                        rfl

theorem cell23_4001092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4001092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001092 prefixEnd_4001092 := by exact prefixLift 4001092
  have htrace : WordTrace (prefixWord ++ tailWord_4001092) baseStart_4001092 baseEnd_4001092 := by
    simpa [prefixWord, tailWord_4001092, baseEnd_4001092] using wordTrace_append hprefix tailTrace_4001092
  have hstable : (prefixWord ++ tailWord_4001092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001092).length < 2 ^ (prefixWord ++ tailWord_4001092).sum := by decide
  have hdescent : baseEnd_4001092 < baseStart_4001092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001122 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4001122 : Nat := 118140960795 + 4001122 * 2 ^ 59
def prefixEnd_4001122 : Nat := 4983230072969 + 3 ^ 40 * 4001122 * 2
def baseEnd_4001122 : Nat := 2054498743278799825474181

theorem tailTrace_4001122 : CollatzResearch.WordTrace tailWord_4001122 prefixEnd_4001122 2054498743278799825474181 := by
  unfold tailWord_4001122
  simp only [CollatzResearch.WordTrace]
  refine ⟨36483227052656451519863405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97288605473750537386302413 36483227052656451519863405)
  ·
    refine ⟨13681210144746169319948777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36483227052656451519863405 13681210144746169319948777)
    ·
      refine ⟨10260907608559626989961583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13681210144746169319948777 10260907608559626989961583)
      ·
        refine ⟨15391361412839440484942375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260907608559626989961583 15391361412839440484942375)
        ·
          refine ⟨23087042119259160727413563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15391361412839440484942375 23087042119259160727413563)
          ·
            refine ⟨34630563178888741091120345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23087042119259160727413563 34630563178888741091120345)
            ·
              refine ⟨25972922384166555818340259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34630563178888741091120345 25972922384166555818340259)
              ·
                refine ⟨38959383576249833727510389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25972922384166555818340259 38959383576249833727510389)
                ·
                  refine ⟨3652442210273421911954099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38959383576249833727510389 3652442210273421911954099)
                  ·
                    refine ⟨5478663315410132867931149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652442210273421911954099 5478663315410132867931149)
                    ·
                      refine ⟨2054498743278799825474181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5478663315410132867931149 2054498743278799825474181)
                      ·
                        rfl

theorem cell23_4001122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4001122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001122 prefixEnd_4001122 := by exact prefixLift 4001122
  have htrace : WordTrace (prefixWord ++ tailWord_4001122) baseStart_4001122 baseEnd_4001122 := by
    simpa [prefixWord, tailWord_4001122, baseEnd_4001122] using wordTrace_append hprefix tailTrace_4001122
  have hstable : (prefixWord ++ tailWord_4001122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001122).length < 2 ^ (prefixWord ++ tailWord_4001122).sum := by decide
  have hdescent : baseEnd_4001122 < baseStart_4001122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001132 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 2, 3, 2]
def baseStart_4001132 : Nat := 118140960795 + 4001132 * 2 ^ 59
def prefixEnd_4001132 : Nat := 4983230072969 + 3 ^ 40 * 4001132 * 2
def baseEnd_4001132 : Nat := 2054503878085344786349135

theorem tailTrace_4001132 : CollatzResearch.WordTrace tailWord_4001132 prefixEnd_4001132 2054503878085344786349135 := by
  unfold tailWord_4001132
  simp only [CollatzResearch.WordTrace]
  refine ⟨72966636470294788893658825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97288848627059718524878433 72966636470294788893658825)
  ·
    refine ⟨54724977352721091670244119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72966636470294788893658825 54724977352721091670244119)
    ·
      refine ⟨82087466029081637505366179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54724977352721091670244119 82087466029081637505366179)
      ·
        refine ⟨123131199043622456258049269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82087466029081637505366179 123131199043622456258049269)
        ·
          refine ⟨11543549910339605274192119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123131199043622456258049269 11543549910339605274192119)
          ·
            refine ⟨17315324865509407911288179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543549910339605274192119 17315324865509407911288179)
            ·
              refine ⟨25972987298264111866932269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17315324865509407911288179 25972987298264111866932269)
              ·
                refine ⟨9739870236849041950099601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25972987298264111866932269 9739870236849041950099601)
                ·
                  refine ⟨7304902677636781462574701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9739870236849041950099601 7304902677636781462574701)
                  ·
                    refine ⟨2739338504113793048465513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7304902677636781462574701 2739338504113793048465513)
                    ·
                      refine ⟨2054503878085344786349135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739338504113793048465513 2054503878085344786349135)
                      ·
                        rfl

theorem cell23_4001132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_4001132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001132 prefixEnd_4001132 := by exact prefixLift 4001132
  have htrace : WordTrace (prefixWord ++ tailWord_4001132) baseStart_4001132 baseEnd_4001132 := by
    simpa [prefixWord, tailWord_4001132, baseEnd_4001132] using wordTrace_append hprefix tailTrace_4001132
  have hstable : (prefixWord ++ tailWord_4001132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001132).length < 2 ^ (prefixWord ++ tailWord_4001132).sum := by decide
  have hdescent : baseEnd_4001132 < baseStart_4001132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001145 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 4]
def baseStart_4001145 : Nat := 118140960795 + 4001145 * 2 ^ 59
def prefixEnd_4001145 : Nat := 4983230072969 + 3 ^ 40 * 4001145 * 2
def baseEnd_4001145 : Nat := 2054510553333853235486575

theorem tailTrace_4001145 : CollatzResearch.WordTrace tailWord_4001145 prefixEnd_4001145 2054510553333853235486575 := by
  unfold tailWord_4001145
  simp only [CollatzResearch.WordTrace]
  refine ⟨145933747089542481007540889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97289164726361654005027259 145933747089542481007540889)
  ·
    refine ⟨109450310317156860755655667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145933747089542481007540889 109450310317156860755655667)
    ·
      refine ⟨164175465475735291133483501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109450310317156860755655667 164175465475735291133483501)
      ·
        refine ⟨61565799553400734175056313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164175465475735291133483501 61565799553400734175056313)
        ·
          refine ⟨46174349665050550631292235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61565799553400734175056313 46174349665050550631292235)
          ·
            refine ⟨69261524497575825946938353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46174349665050550631292235 69261524497575825946938353)
            ·
              refine ⟨51946143373181869460203765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69261524497575825946938353 51946143373181869460203765)
              ·
                refine ⟨4869950941235800261894103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51946143373181869460203765 4869950941235800261894103)
                ·
                  refine ⟨7304926411853700392841155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869950941235800261894103 7304926411853700392841155)
                  ·
                    refine ⟨10957389617780550589261733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304926411853700392841155 10957389617780550589261733)
                    ·
                      refine ⟨2054510553333853235486575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10957389617780550589261733 2054510553333853235486575)
                      ·
                        rfl

theorem cell23_4001145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_4001145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001145 prefixEnd_4001145 := by exact prefixLift 4001145
  have htrace : WordTrace (prefixWord ++ tailWord_4001145) baseStart_4001145 baseEnd_4001145 := by
    simpa [prefixWord, tailWord_4001145, baseEnd_4001145] using wordTrace_append hprefix tailTrace_4001145
  have hstable : (prefixWord ++ tailWord_4001145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001145).length < 2 ^ (prefixWord ++ tailWord_4001145).sum := by decide
  have hdescent : baseEnd_4001145 < baseStart_4001145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001150 : List Nat := [4, 2, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4001150 : Nat := 118140960795 + 4001150 * 2 ^ 59
def prefixEnd_4001150 : Nat := 4983230072969 + 3 ^ 40 * 4001150 * 2
def baseEnd_4001150 : Nat := 684837706912375238641351

theorem tailTrace_4001150 : CollatzResearch.WordTrace tailWord_4001150 prefixEnd_4001150 684837706912375238641351 := by
  unfold tailWord_4001150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18241741181815545857684113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97289286303016244574315269 18241741181815545857684113)
  ·
    refine ⟨13681305886361659393263085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18241741181815545857684113 13681305886361659393263085)
    ·
      refine ⟨5130489707385622272473657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13681305886361659393263085 5130489707385622272473657)
      ·
        refine ⟨3847867280539216704355243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5130489707385622272473657 3847867280539216704355243)
        ·
          refine ⟨5771800920808825056532865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847867280539216704355243 5771800920808825056532865)
          ·
            refine ⟨4328850690606618792399649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771800920808825056532865 4328850690606618792399649)
            ·
              refine ⟨3246638017954964094299737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328850690606618792399649 3246638017954964094299737)
              ·
                refine ⟨2434978513466223070724803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246638017954964094299737 2434978513466223070724803)
                ·
                  refine ⟨3652467770199334606087205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434978513466223070724803 3652467770199334606087205)
                  ·
                    refine ⟨684837706912375238641351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3652467770199334606087205 684837706912375238641351)
                    ·
                      rfl

theorem cell23_4001150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4001150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001150 prefixEnd_4001150 := by exact prefixLift 4001150
  have htrace : WordTrace (prefixWord ++ tailWord_4001150) baseStart_4001150 baseEnd_4001150 := by
    simpa [prefixWord, tailWord_4001150, baseEnd_4001150] using wordTrace_append hprefix tailTrace_4001150
  have hstable : (prefixWord ++ tailWord_4001150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001150).length < 2 ^ (prefixWord ++ tailWord_4001150).sum := by decide
  have hdescent : baseEnd_4001150 < baseStart_4001150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001156 : List Nat := [2, 3, 2, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_4001156 : Nat := 118140960795 + 4001156 * 2 ^ 59
def prefixEnd_4001156 : Nat := 4983230072969 + 3 ^ 40 * 4001156 * 2
def baseEnd_4001156 : Nat := 2054516201621052692449025

theorem tailTrace_4001156 : CollatzResearch.WordTrace tailWord_4001156 prefixEnd_4001156 2054516201621052692449025 := by
  unfold tailWord_4001156
  simp only [CollatzResearch.WordTrace]
  refine ⟨72967074146251314943095661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97289432195001753257460881 72967074146251314943095661)
  ·
    refine ⟨27362652804844243103660873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72967074146251314943095661 27362652804844243103660873)
    ·
      refine ⟨20521989603633182327745655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27362652804844243103660873 20521989603633182327745655)
      ·
        refine ⟨30782984405449773491618483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20521989603633182327745655 30782984405449773491618483)
        ·
          refine ⟨46174476608174660237427725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30782984405449773491618483 46174476608174660237427725)
          ·
            refine ⟨17315428728065497589035397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46174476608174660237427725 17315428728065497589035397)
            ·
              refine ⟨3246642886512280797944137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17315428728065497589035397 3246642886512280797944137)
              ·
                refine ⟨2434982164884210598458103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246642886512280797944137 2434982164884210598458103)
                ·
                  refine ⟨3652473247326315897687155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434982164884210598458103 3652473247326315897687155)
                  ·
                    refine ⟨5478709870989473846530733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652473247326315897687155 5478709870989473846530733)
                    ·
                      refine ⟨2054516201621052692449025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5478709870989473846530733 2054516201621052692449025)
                      ·
                        rfl

theorem cell23_4001156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_4001156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001156 prefixEnd_4001156 := by exact prefixLift 4001156
  have htrace : WordTrace (prefixWord ++ tailWord_4001156) baseStart_4001156 baseEnd_4001156 := by
    simpa [prefixWord, tailWord_4001156, baseEnd_4001156] using wordTrace_append hprefix tailTrace_4001156
  have hstable : (prefixWord ++ tailWord_4001156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001156).length < 2 ^ (prefixWord ++ tailWord_4001156).sum := by decide
  have hdescent : baseEnd_4001156 < baseStart_4001156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001172 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_4001172 : Nat := 118140960795 + 4001172 * 2 ^ 59
def prefixEnd_4001172 : Nat := 4983230072969 + 3 ^ 40 * 4001172 * 2
def baseEnd_4001172 : Nat := 684841472437174876616317

theorem tailTrace_4001172 : CollatzResearch.WordTrace tailWord_4001172 prefixEnd_4001172 684841472437174876616317 := by
  unfold tailWord_4001172
  simp only [CollatzResearch.WordTrace]
  refine ⟨72967365930222332309386885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97289821240296443079182513 72967365930222332309386885)
  ·
    refine ⟨13681381111916687308010041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72967365930222332309386885 13681381111916687308010041)
    ·
      refine ⟨10261035833937515481007531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13681381111916687308010041 10261035833937515481007531)
      ·
        refine ⟨15391553750906273221511297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10261035833937515481007531 15391553750906273221511297)
        ·
          refine ⟨11543665313179704916133473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15391553750906273221511297 11543665313179704916133473)
          ·
            refine ⟨8657748984884778687100105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11543665313179704916133473 8657748984884778687100105)
            ·
              refine ⟨6493311738663584015325079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657748984884778687100105 6493311738663584015325079)
              ·
                refine ⟨9739967607995376022987619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493311738663584015325079 9739967607995376022987619)
                ·
                  refine ⟨14609951411993064034481429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9739967607995376022987619 14609951411993064034481429)
                  ·
                    refine ⟨684841472437174876616317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14609951411993064034481429 684841472437174876616317)
                    ·
                      rfl

theorem cell23_4001172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_4001172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001172 prefixEnd_4001172 := by exact prefixLift 4001172
  have htrace : WordTrace (prefixWord ++ tailWord_4001172) baseStart_4001172 baseEnd_4001172 := by
    simpa [prefixWord, tailWord_4001172, baseEnd_4001172] using wordTrace_append hprefix tailTrace_4001172
  have hstable : (prefixWord ++ tailWord_4001172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001172).length < 2 ^ (prefixWord ++ tailWord_4001172).sum := by decide
  have hdescent : baseEnd_4001172 < baseStart_4001172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001252 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_4001252 : Nat := 118140960795 + 4001252 * 2 ^ 59
def prefixEnd_4001252 : Nat := 4983230072969 + 3 ^ 40 * 4001252 * 2
def baseEnd_4001252 : Nat := 2054565495763884316848583

theorem tailTrace_4001252 : CollatzResearch.WordTrace tailWord_4001252 prefixEnd_4001252 2054565495763884316848583 := by
  unfold tailWord_4001252
  simp only [CollatzResearch.WordTrace]
  refine ⟨72968824850077419140843005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97291766466769892187790673 72968824850077419140843005)
  ·
    refine ⟨27363309318779032177816127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72968824850077419140843005 27363309318779032177816127)
    ·
      refine ⟨41044963978168548266724191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27363309318779032177816127 41044963978168548266724191)
      ·
        refine ⟨61567445967252822400086287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41044963978168548266724191 61567445967252822400086287)
        ·
          refine ⟨92351168950879233600129431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61567445967252822400086287 92351168950879233600129431)
          ·
            refine ⟨138526753426318850400194147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92351168950879233600129431 138526753426318850400194147)
            ·
              refine ⟨207790130139478275600291221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138526753426318850400194147 207790130139478275600291221)
              ·
                refine ⟨9740162350288044168763651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207790130139478275600291221 9740162350288044168763651)
                ·
                  refine ⟨14610243525432066253145477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740162350288044168763651 14610243525432066253145477)
                  ·
                    refine ⟨2739420661018512422464777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14610243525432066253145477 2739420661018512422464777)
                    ·
                      refine ⟨2054565495763884316848583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739420661018512422464777 2054565495763884316848583)
                      ·
                        rfl

theorem cell23_4001252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_4001252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001252 prefixEnd_4001252 := by exact prefixLift 4001252
  have htrace : WordTrace (prefixWord ++ tailWord_4001252) baseStart_4001252 baseEnd_4001252 := by
    simpa [prefixWord, tailWord_4001252, baseEnd_4001252] using wordTrace_append hprefix tailTrace_4001252
  have hstable : (prefixWord ++ tailWord_4001252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001252).length < 2 ^ (prefixWord ++ tailWord_4001252).sum := by decide
  have hdescent : baseEnd_4001252 < baseStart_4001252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001255 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4001255 : Nat := 118140960795 + 4001255 * 2 ^ 59
def prefixEnd_4001255 : Nat := 4983230072969 + 3 ^ 40 * 4001255 * 2
def baseEnd_4001255 : Nat := 2054567036205847805111069

theorem tailTrace_4001255 : CollatzResearch.WordTrace tailWord_4001255 prefixEnd_4001255 2054567036205847805111069 := by
  unfold tailWord_4001255
  simp only [CollatzResearch.WordTrace]
  refine ⟨145937759119143969794045219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97291839412762646529363479 145937759119143969794045219)
  ·
    refine ⟨218906638678715954691067829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145937759119143969794045219 218906638678715954691067829)
    ·
      refine ⟨20522497376129620752287609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218906638678715954691067829 20522497376129620752287609)
      ·
        refine ⟨15391873032097215564215707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20522497376129620752287609 15391873032097215564215707)
        ·
          refine ⟨23087809548145823346323561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15391873032097215564215707 23087809548145823346323561)
          ·
            refine ⟨17315857161109367509742671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23087809548145823346323561 17315857161109367509742671)
            ·
              refine ⟨25973785741664051264614007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17315857161109367509742671 25973785741664051264614007)
              ·
                refine ⟨38960678612496076896921011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25973785741664051264614007 38960678612496076896921011)
                ·
                  refine ⟨58441017918744115345381517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38960678612496076896921011 58441017918744115345381517)
                  ·
                    refine ⟨21915381719529043254518069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58441017918744115345381517 21915381719529043254518069)
                    ·
                      refine ⟨2054567036205847805111069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21915381719529043254518069 2054567036205847805111069)
                      ·
                        rfl

theorem cell23_4001255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4001255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001255 prefixEnd_4001255 := by exact prefixLift 4001255
  have htrace : WordTrace (prefixWord ++ tailWord_4001255) baseStart_4001255 baseEnd_4001255 := by
    simpa [prefixWord, tailWord_4001255, baseEnd_4001255] using wordTrace_append hprefix tailTrace_4001255
  have hstable : (prefixWord ++ tailWord_4001255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001255).length < 2 ^ (prefixWord ++ tailWord_4001255).sum := by decide
  have hdescent : baseEnd_4001255 < baseStart_4001255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001285 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_4001285 : Nat := 118140960795 + 4001285 * 2 ^ 59
def prefixEnd_4001285 : Nat := 4983230072969 + 3 ^ 40 * 4001285 * 2
def baseEnd_4001285 : Nat := 2054582440625482687735931

theorem tailTrace_4001285 : CollatzResearch.WordTrace tailWord_4001285 prefixEnd_4001285 2054582440625482687735931 := by
  unfold tailWord_4001285
  simp only [CollatzResearch.WordTrace]
  refine ⟨145938853309035284917637309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97292568872690189945091539 145938853309035284917637309)
  ·
    refine ⟨54727069990888231844113991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145938853309035284917637309 54727069990888231844113991)
    ·
      refine ⟨82090604986332347766170987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54727069990888231844113991 82090604986332347766170987)
      ·
        refine ⟨123135907479498521649256481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82090604986332347766170987 123135907479498521649256481)
        ·
          refine ⟨92351930609623891236942361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123135907479498521649256481 92351930609623891236942361)
          ·
            refine ⟨69263947957217918427706771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92351930609623891236942361 69263947957217918427706771)
            ·
              refine ⟨103895921935826877641560157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69263947957217918427706771 103895921935826877641560157)
              ·
                refine ⟨38960970725935079115585059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103895921935826877641560157 38960970725935079115585059)
                ·
                  refine ⟨58441456088902618673377589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38960970725935079115585059 58441456088902618673377589)
                  ·
                    refine ⟨5478886508334620500629149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58441456088902618673377589 5478886508334620500629149)
                    ·
                      refine ⟨2054582440625482687735931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5478886508334620500629149 2054582440625482687735931)
                      ·
                        rfl

theorem cell23_4001285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_4001285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001285 prefixEnd_4001285 := by exact prefixLift 4001285
  have htrace : WordTrace (prefixWord ++ tailWord_4001285) baseStart_4001285 baseEnd_4001285 := by
    simpa [prefixWord, tailWord_4001285, baseEnd_4001285] using wordTrace_append hprefix tailTrace_4001285
  have hstable : (prefixWord ++ tailWord_4001285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001285).length < 2 ^ (prefixWord ++ tailWord_4001285).sum := by decide
  have hdescent : baseEnd_4001285 < baseStart_4001285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001322 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_4001322 : Nat := 118140960795 + 4001322 * 2 ^ 59
def prefixEnd_4001322 : Nat := 4983230072969 + 3 ^ 40 * 4001322 * 2
def baseEnd_4001322 : Nat := 684867146469899680991087

theorem tailTrace_4001322 : CollatzResearch.WordTrace tailWord_4001322 prefixEnd_4001322 684867146469899680991087 := by
  unfold tailWord_4001322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36485050702475310059183555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97293468539934160157822813 36485050702475310059183555)
  ·
    refine ⟨54727576053712965088775333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36485050702475310059183555 54727576053712965088775333)
    ·
      refine ⟨10261420510071180954145375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54727576053712965088775333 10261420510071180954145375)
      ·
        refine ⟨15392130765106771431218063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10261420510071180954145375 15392130765106771431218063)
        ·
          refine ⟨23088196147660157146827095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15392130765106771431218063 23088196147660157146827095)
          ·
            refine ⟨34632294221490235720240643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23088196147660157146827095 34632294221490235720240643)
            ·
              refine ⟨51948441332235353580360965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34632294221490235720240643 51948441332235353580360965)
              ·
                refine ⟨9740332749794128796317681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51948441332235353580360965 9740332749794128796317681)
                ·
                  refine ⟨7305249562345596597238261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9740332749794128796317681 7305249562345596597238261)
                  ·
                    refine ⟨684867146469899680991087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7305249562345596597238261 684867146469899680991087)
                    ·
                      rfl

theorem cell23_4001322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_4001322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001322 prefixEnd_4001322 := by exact prefixLift 4001322
  have htrace : WordTrace (prefixWord ++ tailWord_4001322) baseStart_4001322 baseEnd_4001322 := by
    simpa [prefixWord, tailWord_4001322, baseEnd_4001322] using wordTrace_append hprefix tailTrace_4001322
  have hstable : (prefixWord ++ tailWord_4001322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001322).length < 2 ^ (prefixWord ++ tailWord_4001322).sum := by decide
  have hdescent : baseEnd_4001322 < baseStart_4001322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001326 : List Nat := [4, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_4001326 : Nat := 118140960795 + 4001326 * 2 ^ 59
def prefixEnd_4001326 : Nat := 4983230072969 + 3 ^ 40 * 4001326 * 2
def baseEnd_4001326 : Nat := 228289277036924114147027

theorem tailTrace_4001326 : CollatzResearch.WordTrace tailWord_4001326 prefixEnd_4001326 228289277036924114147027 := by
  unfold tailWord_4001326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18242543587735843614984979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97293565801257832613253221 18242543587735843614984979)
  ·
    refine ⟨27363815381603765422477469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18242543587735843614984979 27363815381603765422477469)
    ·
      refine ⟨10261430768101412033429051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27363815381603765422477469 10261430768101412033429051)
      ·
        refine ⟨15392146152152118050143577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10261430768101412033429051 15392146152152118050143577)
        ·
          refine ⟨11544109614114088537607683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15392146152152118050143577 11544109614114088537607683)
          ·
            refine ⟨17316164421171132806411525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11544109614114088537607683 17316164421171132806411525)
            ·
              refine ⟨3246780828969587401202161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17316164421171132806411525 3246780828969587401202161)
              ·
                refine ⟨2435085621727190550901621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246780828969587401202161 2435085621727190550901621)
                ·
                  refine ⟨228289277036924114147027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2435085621727190550901621 228289277036924114147027)
                  ·
                    rfl

theorem cell23_4001326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_4001326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001326 prefixEnd_4001326 := by exact prefixLift 4001326
  have htrace : WordTrace (prefixWord ++ tailWord_4001326) baseStart_4001326 baseEnd_4001326 := by
    simpa [prefixWord, tailWord_4001326, baseEnd_4001326] using wordTrace_append hprefix tailTrace_4001326
  have hstable : (prefixWord ++ tailWord_4001326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001326).length < 2 ^ (prefixWord ++ tailWord_4001326).sum := by decide
  have hdescent : baseEnd_4001326 < baseStart_4001326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001365 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 8]
def baseStart_4001365 : Nat := 118140960795 + 4001365 * 2 ^ 59
def prefixEnd_4001365 : Nat := 4983230072969 + 3 ^ 40 * 4001365 * 2
def baseEnd_4001365 : Nat := 228291502119760263859507

theorem tailTrace_4001365 : CollatzResearch.WordTrace tailWord_4001365 prefixEnd_4001365 228291502119760263859507 := by
  unfold tailWord_4001365
  simp only [CollatzResearch.WordTrace]
  refine ⟨145941771148745458580549549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97294514099163639053699699 145941771148745458580549549)
  ·
    refine ⟨54728164180779546967706081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145941771148745458580549549 54728164180779546967706081)
    ·
      refine ⟨41046123135584660225779561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54728164180779546967706081 41046123135584660225779561)
      ·
        refine ⟨30784592351688495169334671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41046123135584660225779561 30784592351688495169334671)
        ·
          refine ⟨46176888527532742754002007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30784592351688495169334671 46176888527532742754002007)
          ·
            refine ⟨69265332791299114131003011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46176888527532742754002007 69265332791299114131003011)
            ·
              refine ⟨103897999186948671196504517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69265332791299114131003011 103897999186948671196504517)
              ·
                refine ⟨19480874847552875849344597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103897999186948671196504517 19480874847552875849344597)
                ·
                  refine ⟨228291502119760263859507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19480874847552875849344597 228291502119760263859507)
                  ·
                    rfl

theorem cell23_4001365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_4001365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001365 prefixEnd_4001365 := by exact prefixLift 4001365
  have htrace : WordTrace (prefixWord ++ tailWord_4001365) baseStart_4001365 baseEnd_4001365 := by
    simpa [prefixWord, tailWord_4001365, baseEnd_4001365] using wordTrace_append hprefix tailTrace_4001365
  have hstable : (prefixWord ++ tailWord_4001365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001365).length < 2 ^ (prefixWord ++ tailWord_4001365).sum := by decide
  have hdescent : baseEnd_4001365 < baseStart_4001365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001372 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_4001372 : Nat := 118140960795 + 4001372 * 2 ^ 59
def prefixEnd_4001372 : Nat := 4983230072969 + 3 ^ 40 * 4001372 * 2
def baseEnd_4001372 : Nat := 2054627113442423847348031

theorem tailTrace_4001372 : CollatzResearch.WordTrace tailWord_4001372 prefixEnd_4001372 2054627113442423847348031 := by
  unfold tailWord_4001372
  simp only [CollatzResearch.WordTrace]
  refine ⟨72971013229860049388027185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97294684306480065850702913 72971013229860049388027185)
  ·
    refine ⟨54728259922395037041020389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72971013229860049388027185 54728259922395037041020389)
    ·
      refine ⟨10261548735449069445191323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54728259922395037041020389 10261548735449069445191323)
      ·
        refine ⟨15392323103173604167786985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10261548735449069445191323 15392323103173604167786985)
        ·
          refine ⟨11544242327380203125840239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15392323103173604167786985 11544242327380203125840239)
          ·
            refine ⟨17316363491070304688760359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11544242327380203125840239 17316363491070304688760359)
            ·
              refine ⟨25974545236605457033140539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17316363491070304688760359 25974545236605457033140539)
              ·
                refine ⟨38961817854908185549710809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25974545236605457033140539 38961817854908185549710809)
                ·
                  refine ⟨29221363391181139162283107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38961817854908185549710809 29221363391181139162283107)
                  ·
                    refine ⟨43832045086771708743424661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29221363391181139162283107 43832045086771708743424661)
                    ·
                      refine ⟨2054627113442423847348031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43832045086771708743424661 2054627113442423847348031)
                      ·
                        rfl

theorem cell23_4001372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_4001372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001372 prefixEnd_4001372 := by exact prefixLift 4001372
  have htrace : WordTrace (prefixWord ++ tailWord_4001372) baseStart_4001372 baseEnd_4001372 := by
    simpa [prefixWord, tailWord_4001372, baseEnd_4001372] using wordTrace_append hprefix tailTrace_4001372
  have hstable : (prefixWord ++ tailWord_4001372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001372).length < 2 ^ (prefixWord ++ tailWord_4001372).sum := by decide
  have hdescent : baseEnd_4001372 < baseStart_4001372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001385 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_4001385 : Nat := 118140960795 + 4001385 * 2 ^ 59
def prefixEnd_4001385 : Nat := 4983230072969 + 3 ^ 40 * 4001385 * 2
def baseEnd_4001385 : Nat := 2054633788690932296485471

theorem tailTrace_4001385 : CollatzResearch.WordTrace tailWord_4001385 prefixEnd_4001385 2054633788690932296485471 := by
  unfold tailWord_4001385
  simp only [CollatzResearch.WordTrace]
  refine ⟨145942500608673001996277609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97295000405782001330851739 145942500608673001996277609)
  ·
    refine ⟨109456875456504751497208207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145942500608673001996277609 109456875456504751497208207)
    ·
      refine ⟨164185313184757127245812311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109456875456504751497208207 164185313184757127245812311)
      ·
        refine ⟨246277969777135690868718467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164185313184757127245812311 246277969777135690868718467)
        ·
          refine ⟨369416954665703536303077701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246277969777135690868718467 369416954665703536303077701)
          ·
            refine ⟨69265678999819413056827069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369416954665703536303077701 69265678999819413056827069)
            ·
              refine ⟨25974629624932279896310151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69265678999819413056827069 25974629624932279896310151)
              ·
                refine ⟨38961944437398419844465227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25974629624932279896310151 38961944437398419844465227)
                ·
                  refine ⟨58442916656097629766697841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38961944437398419844465227 58442916656097629766697841)
                  ·
                    refine ⟨43832187492073222325023381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58442916656097629766697841 43832187492073222325023381)
                    ·
                      refine ⟨2054633788690932296485471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43832187492073222325023381 2054633788690932296485471)
                      ·
                        rfl

theorem cell23_4001385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_4001385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001385 prefixEnd_4001385 := by exact prefixLift 4001385
  have htrace : WordTrace (prefixWord ++ tailWord_4001385) baseStart_4001385 baseEnd_4001385 := by
    simpa [prefixWord, tailWord_4001385, baseEnd_4001385] using wordTrace_append hprefix tailTrace_4001385
  have hstable : (prefixWord ++ tailWord_4001385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001385).length < 2 ^ (prefixWord ++ tailWord_4001385).sum := by decide
  have hdescent : baseEnd_4001385 < baseStart_4001385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001386 : List Nat := [3, 1, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_4001386 : Nat := 118140960795 + 4001386 * 2 ^ 59
def prefixEnd_4001386 : Nat := 4983230072969 + 3 ^ 40 * 4001386 * 2
def baseEnd_4001386 : Nat := 684878100723862264190989

theorem tailTrace_4001386 : CollatzResearch.WordTrace tailWord_4001386 prefixEnd_4001386 684878100723862264190989 := by
  unfold tailWord_4001386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36485634270417344791766003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97295024721112919444709341 36485634270417344791766003)
  ·
    refine ⟨54728451405626017187649005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36485634270417344791766003 54728451405626017187649005)
    ·
      refine ⟨20523169277109756445368377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54728451405626017187649005 20523169277109756445368377)
      ·
        refine ⟨15392376957832317334026283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20523169277109756445368377 15392376957832317334026283)
        ·
          refine ⟨23088565436748476001039425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15392376957832317334026283 23088565436748476001039425)
          ·
            refine ⟨17316424077561357000779569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23088565436748476001039425 17316424077561357000779569)
            ·
              refine ⟨12987318058171017750584677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17316424077561357000779569 12987318058171017750584677)
              ·
                refine ⟨2435122135907065828234627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12987318058171017750584677 2435122135907065828234627)
                ·
                  refine ⟨3652683203860598742351941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435122135907065828234627 3652683203860598742351941)
                  ·
                    refine ⟨684878100723862264190989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3652683203860598742351941 684878100723862264190989)
                    ·
                      rfl

theorem cell23_4001386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_4001386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001386 prefixEnd_4001386 := by exact prefixLift 4001386
  have htrace : WordTrace (prefixWord ++ tailWord_4001386) baseStart_4001386 baseEnd_4001386 := by
    simpa [prefixWord, tailWord_4001386, baseEnd_4001386] using wordTrace_append hprefix tailTrace_4001386
  have hstable : (prefixWord ++ tailWord_4001386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001386).length < 2 ^ (prefixWord ++ tailWord_4001386).sum := by decide
  have hdescent : baseEnd_4001386 < baseStart_4001386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001419 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 2, 3, 2]
def baseStart_4001419 : Nat := 118140960795 + 4001419 * 2 ^ 59
def prefixEnd_4001419 : Nat := 4983230072969 + 3 ^ 40 * 4001419 * 2
def baseEnd_4001419 : Nat := 2054651247033185163460315

theorem tailTrace_4001419 : CollatzResearch.WordTrace tailWord_4001419 prefixEnd_4001419 2054651247033185163460315 := by
  unfold tailWord_4001419
  simp only [CollatzResearch.WordTrace]
  refine ⟨145943740690549825803015311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97295827127033217202010207 145943740690549825803015311)
  ·
    refine ⟨218915611035824738704522967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145943740690549825803015311 218915611035824738704522967)
    ·
      refine ⟨328373416553737108056784451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218915611035824738704522967 328373416553737108056784451)
      ·
        refine ⟨492560124830605662085176677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328373416553737108056784451 492560124830605662085176677)
        ·
          refine ⟨92355023405738561640970627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 492560124830605662085176677 92355023405738561640970627)
          ·
            refine ⟨138532535108607842461455941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92355023405738561640970627 138532535108607842461455941)
            ·
              refine ⟨25974850332863970461522989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138532535108607842461455941 25974850332863970461522989)
              ·
                refine ⟨9740568874823988923071121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25974850332863970461522989 9740568874823988923071121)
                ·
                  refine ⟨7305426656117991692303341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9740568874823988923071121 7305426656117991692303341)
                  ·
                    refine ⟨2739534996044246884613753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7305426656117991692303341 2739534996044246884613753)
                    ·
                      refine ⟨2054651247033185163460315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739534996044246884613753 2054651247033185163460315)
                      ·
                        rfl

theorem cell23_4001419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3, 2].length) (baseStart_4001419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001419 prefixEnd_4001419 := by exact prefixLift 4001419
  have htrace : WordTrace (prefixWord ++ tailWord_4001419) baseStart_4001419 baseEnd_4001419 := by
    simpa [prefixWord, tailWord_4001419, baseEnd_4001419] using wordTrace_append hprefix tailTrace_4001419
  have hstable : (prefixWord ++ tailWord_4001419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001419).length < 2 ^ (prefixWord ++ tailWord_4001419).sum := by decide
  have hdescent : baseEnd_4001419 < baseStart_4001419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001435 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5]
def baseStart_4001435 : Nat := 118140960795 + 4001435 * 2 ^ 59
def prefixEnd_4001435 : Nat := 4983230072969 + 3 ^ 40 * 4001435 * 2
def baseEnd_4001435 : Nat := 2054659462723657100860241

theorem tailTrace_4001435 : CollatzResearch.WordTrace tailWord_4001435 prefixEnd_4001435 2054659462723657100860241 := by
  unfold tailWord_4001435
  simp only [CollatzResearch.WordTrace]
  refine ⟨145944324258491860535597759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97296216172327907023731839 145944324258491860535597759)
  ·
    refine ⟨218916486387737790803396639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145944324258491860535597759 218916486387737790803396639)
    ·
      refine ⟨328374729581606686205094959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218916486387737790803396639 328374729581606686205094959)
      ·
        refine ⟨492562094372410029307642439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328374729581606686205094959 492562094372410029307642439)
        ·
          refine ⟨738843141558615043961463659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492562094372410029307642439 738843141558615043961463659)
          ·
            refine ⟨1108264712337922565942195489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738843141558615043961463659 1108264712337922565942195489)
            ·
              refine ⟨831198534253441924456646617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108264712337922565942195489 831198534253441924456646617)
              ·
                refine ⟨623398900690081443342484963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831198534253441924456646617 623398900690081443342484963)
                ·
                  refine ⟨935098351035122165013727445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623398900690081443342484963 935098351035122165013727445)
                  ·
                    refine ⟨21916367602385675742509237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 935098351035122165013727445 21916367602385675742509237)
                    ·
                      refine ⟨2054659462723657100860241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21916367602385675742509237 2054659462723657100860241)
                      ·
                        rfl

theorem cell23_4001435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_4001435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001435 prefixEnd_4001435 := by exact prefixLift 4001435
  have htrace : WordTrace (prefixWord ++ tailWord_4001435) baseStart_4001435 baseEnd_4001435 := by
    simpa [prefixWord, tailWord_4001435, baseEnd_4001435] using wordTrace_append hprefix tailTrace_4001435
  have hstable : (prefixWord ++ tailWord_4001435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001435).length < 2 ^ (prefixWord ++ tailWord_4001435).sum := by decide
  have hdescent : baseEnd_4001435 < baseStart_4001435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001443 : List Nat := [1, 1, 1, 4, 1, 1, 7, 2, 1, 1, 3]
def baseStart_4001443 : Nat := 118140960795 + 4001443 * 2 ^ 59
def prefixEnd_4001443 : Nat := 4983230072969 + 3 ^ 40 * 4001443 * 2
def baseEnd_4001443 : Nat := 2054663570568893069560205

theorem tailTrace_4001443 : CollatzResearch.WordTrace tailWord_4001443 prefixEnd_4001443 2054663570568893069560205 := by
  unfold tailWord_4001443
  simp only [CollatzResearch.WordTrace]
  refine ⟨145944616042462877901888983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97296410694975251934592655 145944616042462877901888983)
  ·
    refine ⟨218916924063694316852833475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145944616042462877901888983 218916924063694316852833475)
    ·
      refine ⟨328375386095541475279250213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218916924063694316852833475 328375386095541475279250213)
      ·
        refine ⟨61570384892914026614859415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328375386095541475279250213 61570384892914026614859415)
        ·
          refine ⟨92355577339371039922289123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61570384892914026614859415 92355577339371039922289123)
          ·
            refine ⟨138533366009056559883433685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92355577339371039922289123 138533366009056559883433685)
            ·
              refine ⟨3246875765837263122267977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138533366009056559883433685 3246875765837263122267977)
              ·
                refine ⟨2435156824377947341700983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246875765837263122267977 2435156824377947341700983)
                ·
                  refine ⟨3652735236566921012551475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435156824377947341700983 3652735236566921012551475)
                  ·
                    refine ⟨5479102854850381518827213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652735236566921012551475 5479102854850381518827213)
                    ·
                      refine ⟨2054663570568893069560205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5479102854850381518827213 2054663570568893069560205)
                      ·
                        rfl

theorem cell23_4001443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_4001443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001443 prefixEnd_4001443 := by exact prefixLift 4001443
  have htrace : WordTrace (prefixWord ++ tailWord_4001443) baseStart_4001443 baseEnd_4001443 := by
    simpa [prefixWord, tailWord_4001443, baseEnd_4001443] using wordTrace_append hprefix tailTrace_4001443
  have hstable : (prefixWord ++ tailWord_4001443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001443).length < 2 ^ (prefixWord ++ tailWord_4001443).sum := by decide
  have hdescent : baseEnd_4001443 < baseStart_4001443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001459 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 2, 4]
def baseStart_4001459 : Nat := 118140960795 + 4001459 * 2 ^ 59
def prefixEnd_4001459 : Nat := 4983230072969 + 3 ^ 40 * 4001459 * 2
def baseEnd_4001459 : Nat := 684890595419788335653377

theorem tailTrace_4001459 : CollatzResearch.WordTrace tailWord_4001459 prefixEnd_4001459 684890595419788335653377 := by
  unfold tailWord_4001459
  simp only [CollatzResearch.WordTrace]
  refine ⟨145945199610404912634471431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97296799740269941756314287 145945199610404912634471431)
  ·
    refine ⟨218917799415607368951707147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145945199610404912634471431 218917799415607368951707147)
    ·
      refine ⟨328376699123411053427560721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218917799415607368951707147 328376699123411053427560721)
      ·
        refine ⟨246282524342558290070670541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328376699123411053427560721 246282524342558290070670541)
        ·
          refine ⟨92355946628459358776501453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246282524342558290070670541 92355946628459358776501453)
          ·
            refine ⟨34633479985672259541188045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92355946628459358776501453 34633479985672259541188045)
            ·
              refine ⟨12987554994627097327945517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34633479985672259541188045 12987554994627097327945517)
              ·
                refine ⟨4870333122985161497979569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12987554994627097327945517 4870333122985161497979569)
                ·
                  refine ⟨3652749842238871123484677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4870333122985161497979569 3652749842238871123484677)
                  ·
                    refine ⟨684890595419788335653377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3652749842238871123484677 684890595419788335653377)
                    ·
                      rfl

theorem cell23_4001459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 4].length) (baseStart_4001459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001459 prefixEnd_4001459 := by exact prefixLift 4001459
  have htrace : WordTrace (prefixWord ++ tailWord_4001459) baseStart_4001459 baseEnd_4001459 := by
    simpa [prefixWord, tailWord_4001459, baseEnd_4001459] using wordTrace_append hprefix tailTrace_4001459
  have hstable : (prefixWord ++ tailWord_4001459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001459).length < 2 ^ (prefixWord ++ tailWord_4001459).sum := by decide
  have hdescent : baseEnd_4001459 < baseStart_4001459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001466 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_4001466 : Nat := 118140960795 + 4001466 * 2 ^ 59
def prefixEnd_4001466 : Nat := 4983230072969 + 3 ^ 40 * 4001466 * 2
def baseEnd_4001466 : Nat := 2054675380623946479572599

theorem tailTrace_4001466 : CollatzResearch.WordTrace tailWord_4001466 prefixEnd_4001466 2054675380623946479572599 := by
  unfold tailWord_4001466
  simp only [CollatzResearch.WordTrace]
  refine ⟨36486363730344888207494063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97296969947586368553317501 36486363730344888207494063)
  ·
    refine ⟨54729545595517332311241095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36486363730344888207494063 54729545595517332311241095)
    ·
      refine ⟨82094318393275998466861643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54729545595517332311241095 82094318393275998466861643)
      ·
        refine ⟨123141477589913997700292465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82094318393275998466861643 123141477589913997700292465)
        ·
          refine ⟨92356108192435498275219349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123141477589913997700292465 92356108192435498275219349)
          ·
            refine ⟨4329192571520413981650907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92356108192435498275219349 4329192571520413981650907)
            ·
              refine ⟨6493788857280620972476361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329192571520413981650907 6493788857280620972476361)
              ·
                refine ⟨4870341642960465729357271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6493788857280620972476361 4870341642960465729357271)
                ·
                  refine ⟨7305512464440698594035907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4870341642960465729357271 7305512464440698594035907)
                  ·
                    refine ⟨10958268696661047891053861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7305512464440698594035907 10958268696661047891053861)
                    ·
                      refine ⟨2054675380623946479572599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10958268696661047891053861 2054675380623946479572599)
                      ·
                        rfl

theorem cell23_4001466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_4001466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001466 prefixEnd_4001466 := by exact prefixLift 4001466
  have htrace : WordTrace (prefixWord ++ tailWord_4001466) baseStart_4001466 baseEnd_4001466 := by
    simpa [prefixWord, tailWord_4001466, baseEnd_4001466] using wordTrace_append hprefix tailTrace_4001466
  have hstable : (prefixWord ++ tailWord_4001466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001466).length < 2 ^ (prefixWord ++ tailWord_4001466).sum := by decide
  have hdescent : baseEnd_4001466 < baseStart_4001466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001469 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_4001469 : Nat := 118140960795 + 4001469 * 2 ^ 59
def prefixEnd_4001469 : Nat := 4983230072969 + 3 ^ 40 * 4001469 * 2
def baseEnd_4001469 : Nat := 2054676921065909967835085

theorem tailTrace_4001469 : CollatzResearch.WordTrace tailWord_4001469 prefixEnd_4001469 2054676921065909967835085 := by
  unfold tailWord_4001469
  simp only [CollatzResearch.WordTrace]
  refine ⟨145945564340368684342335461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97297042893579122894890307 145945564340368684342335461)
  ·
    refine ⟨27364793313819128314187899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145945564340368684342335461 27364793313819128314187899)
    ·
      refine ⟨41047189970728692471281849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27364793313819128314187899 41047189970728692471281849)
      ·
        refine ⟨30785392478046519353461387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41047189970728692471281849 30785392478046519353461387)
        ·
          refine ⟨46178088717069779030192081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30785392478046519353461387 46178088717069779030192081)
          ·
            refine ⟨34633566537802334272644061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46178088717069779030192081 34633566537802334272644061)
            ·
              refine ⟨12987587451675875352241523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34633566537802334272644061 12987587451675875352241523)
              ·
                refine ⟨19481381177513813028362285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12987587451675875352241523 19481381177513813028362285)
                ·
                  refine ⟨7305517941567679885635857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19481381177513813028362285 7305517941567679885635857)
                  ·
                    refine ⟨5479138456175759914226893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7305517941567679885635857 5479138456175759914226893)
                    ·
                      refine ⟨2054676921065909967835085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5479138456175759914226893 2054676921065909967835085)
                      ·
                        rfl

theorem cell23_4001469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_4001469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001469 prefixEnd_4001469 := by exact prefixLift 4001469
  have htrace : WordTrace (prefixWord ++ tailWord_4001469) baseStart_4001469 baseEnd_4001469 := by
    simpa [prefixWord, tailWord_4001469, baseEnd_4001469] using wordTrace_append hprefix tailTrace_4001469
  have hstable : (prefixWord ++ tailWord_4001469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001469).length < 2 ^ (prefixWord ++ tailWord_4001469).sum := by decide
  have hdescent : baseEnd_4001469 < baseStart_4001469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001516 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_4001516 : Nat := 118140960795 + 4001516 * 2 ^ 59
def prefixEnd_4001516 : Nat := 4983230072969 + 3 ^ 40 * 4001516 * 2
def baseEnd_4001516 : Nat := 2054701054656671283947369

theorem tailTrace_4001516 : CollatzResearch.WordTrace tailWord_4001516 prefixEnd_4001516 2054701054656671283947369 := by
  unfold tailWord_4001516
  simp only [CollatzResearch.WordTrace]
  refine ⟨72973639285599205684648201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97298185714132274246197601 72973639285599205684648201)
  ·
    refine ⟨54730229464199404263486151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72973639285599205684648201 54730229464199404263486151)
    ·
      refine ⟨82095344196299106395229227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54730229464199404263486151 82095344196299106395229227)
      ·
        refine ⟨123143016294448659592843841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82095344196299106395229227 123143016294448659592843841)
        ·
          refine ⟨92357262220836494694632881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123143016294448659592843841 92357262220836494694632881)
          ·
            refine ⟨69267946665627371020974661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92357262220836494694632881 69267946665627371020974661)
            ·
              refine ⟨12987739999805132066432749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69267946665627371020974661 12987739999805132066432749)
              ·
                refine ⟨4870402499926924524912281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12987739999805132066432749 4870402499926924524912281)
                ·
                  refine ⟨3652801874945193393684211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4870402499926924524912281 3652801874945193393684211)
                  ·
                    refine ⟨5479202812417790090526317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652801874945193393684211 5479202812417790090526317)
                    ·
                      refine ⟨2054701054656671283947369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5479202812417790090526317 2054701054656671283947369)
                      ·
                        rfl

theorem cell23_4001516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_4001516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001516 prefixEnd_4001516 := by exact prefixLift 4001516
  have htrace : WordTrace (prefixWord ++ tailWord_4001516) baseStart_4001516 baseEnd_4001516 := by
    simpa [prefixWord, tailWord_4001516, baseEnd_4001516] using wordTrace_append hprefix tailTrace_4001516
  have hstable : (prefixWord ++ tailWord_4001516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001516).length < 2 ^ (prefixWord ++ tailWord_4001516).sum := by decide
  have hdescent : baseEnd_4001516 < baseStart_4001516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001532 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_4001532 : Nat := 118140960795 + 4001532 * 2 ^ 59
def prefixEnd_4001532 : Nat := 4983230072969 + 3 ^ 40 * 4001532 * 2
def baseEnd_4001532 : Nat := 684903090115714407115765

theorem tailTrace_4001532 : CollatzResearch.WordTrace tailWord_4001532 prefixEnd_4001532 684903090115714407115765 := by
  unfold tailWord_4001532
  simp only [CollatzResearch.WordTrace]
  refine ⟨72973931069570223050939425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97298574759426964067919233 72973931069570223050939425)
  ·
    refine ⟨54730448302177667288204569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72973931069570223050939425 54730448302177667288204569)
    ·
      refine ⟨41047836226633250466153427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54730448302177667288204569 41047836226633250466153427)
      ·
        refine ⟨61571754339949875699230141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41047836226633250466153427 61571754339949875699230141)
        ·
          refine ⟨23089407877481203387211303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61571754339949875699230141 23089407877481203387211303)
          ·
            refine ⟨34634111816221805080816955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23089407877481203387211303 34634111816221805080816955)
            ·
              refine ⟨51951167724332707621225433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34634111816221805080816955 51951167724332707621225433)
              ·
                refine ⟨38963375793249530715919075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51951167724332707621225433 38963375793249530715919075)
                ·
                  refine ⟨58445063689874296073878613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38963375793249530715919075 58445063689874296073878613)
                  ·
                    refine ⟨684903090115714407115765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58445063689874296073878613 684903090115714407115765)
                    ·
                      rfl

theorem cell23_4001532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_4001532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001532 prefixEnd_4001532 := by exact prefixLift 4001532
  have htrace : WordTrace (prefixWord ++ tailWord_4001532) baseStart_4001532 baseEnd_4001532 := by
    simpa [prefixWord, tailWord_4001532, baseEnd_4001532] using wordTrace_append hprefix tailTrace_4001532
  have hstable : (prefixWord ++ tailWord_4001532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001532).length < 2 ^ (prefixWord ++ tailWord_4001532).sum := by decide
  have hdescent : baseEnd_4001532 < baseStart_4001532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001569 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4001569 : Nat := 118140960795 + 4001569 * 2 ^ 59
def prefixEnd_4001569 : Nat := 4983230072969 + 3 ^ 40 * 4001569 * 2
def baseEnd_4001569 : Nat := 2054728269131359576584625

theorem tailTrace_4001569 : CollatzResearch.WordTrace tailWord_4001569 prefixEnd_4001569 2054728269131359576584625 := by
  unfold tailWord_4001569
  simp only [CollatzResearch.WordTrace]
  refine ⟨145949211640006401420975761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97299474426670934280650507 145949211640006401420975761)
  ·
    refine ⟨109461908730004801065731821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145949211640006401420975761 109461908730004801065731821)
    ·
      refine ⟨41048215773751800399649433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109461908730004801065731821 41048215773751800399649433)
      ·
        refine ⟨30786161830313850299737075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41048215773751800399649433 30786161830313850299737075)
        ·
          refine ⟨46179242745470775449605613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30786161830313850299737075 46179242745470775449605613)
          ·
            refine ⟨17317216029551540793602105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46179242745470775449605613 17317216029551540793602105)
            ·
              refine ⟨12987912022163655595201579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17317216029551540793602105 12987912022163655595201579)
              ·
                refine ⟨19481868033245483392802369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12987912022163655595201579 19481868033245483392802369)
                ·
                  refine ⟨14611401024934112544601777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19481868033245483392802369 14611401024934112544601777)
                  ·
                    refine ⟨10958550768700584408451333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14611401024934112544601777 10958550768700584408451333)
                    ·
                      refine ⟨2054728269131359576584625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10958550768700584408451333 2054728269131359576584625)
                      ·
                        rfl

theorem cell23_4001569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4001569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001569 prefixEnd_4001569 := by exact prefixLift 4001569
  have htrace : WordTrace (prefixWord ++ tailWord_4001569) baseStart_4001569 baseEnd_4001569 := by
    simpa [prefixWord, tailWord_4001569, baseEnd_4001569] using wordTrace_append hprefix tailTrace_4001569
  have hstable : (prefixWord ++ tailWord_4001569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001569).length < 2 ^ (prefixWord ++ tailWord_4001569).sum := by decide
  have hdescent : baseEnd_4001569 < baseStart_4001569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001573 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 1, 4, 2]
def baseStart_4001573 : Nat := 118140960795 + 4001573 * 2 ^ 59
def prefixEnd_4001573 : Nat := 4983230072969 + 3 ^ 40 * 4001573 * 2
def baseEnd_4001573 : Nat := 2054730323053977560934607

theorem tailTrace_4001573 : CollatzResearch.WordTrace tailWord_4001573 prefixEnd_4001573 2054730323053977560934607 := by
  unfold tailWord_4001573
  simp only [CollatzResearch.WordTrace]
  refine ⟨145949357531991910104121373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97299571687994606736080915 145949357531991910104121373)
  ·
    refine ⟨54731009074496966289045515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145949357531991910104121373 54731009074496966289045515)
    ·
      refine ⟨82096513611745449433568273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54731009074496966289045515 82096513611745449433568273)
      ·
        refine ⟨61572385208809087075176205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82096513611745449433568273 61572385208809087075176205)
        ·
          refine ⟨23089644453303407653191077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61572385208809087075176205 23089644453303407653191077)
          ·
            refine ⟨4329308334994388934973327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23089644453303407653191077 4329308334994388934973327)
            ·
              refine ⟨6493962502491583402459991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329308334994388934973327 6493962502491583402459991)
              ·
                refine ⟨9740943753737375103689987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493962502491583402459991 9740943753737375103689987)
                ·
                  refine ⟨14611415630606062655534981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740943753737375103689987 14611415630606062655534981)
                  ·
                    refine ⟨2739640430738636747912809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14611415630606062655534981 2739640430738636747912809)
                    ·
                      refine ⟨2054730323053977560934607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739640430738636747912809 2054730323053977560934607)
                      ·
                        rfl

theorem cell23_4001573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_4001573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001573 prefixEnd_4001573 := by exact prefixLift 4001573
  have htrace : WordTrace (prefixWord ++ tailWord_4001573) baseStart_4001573 baseEnd_4001573 := by
    simpa [prefixWord, tailWord_4001573, baseEnd_4001573] using wordTrace_append hprefix tailTrace_4001573
  have hstable : (prefixWord ++ tailWord_4001573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001573).length < 2 ^ (prefixWord ++ tailWord_4001573).sum := by decide
  have hdescent : baseEnd_4001573 < baseStart_4001573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001590 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4001590 : Nat := 118140960795 + 4001590 * 2 ^ 59
def prefixEnd_4001590 : Nat := 4983230072969 + 3 ^ 40 * 4001590 * 2
def baseEnd_4001590 : Nat := 2054739052225103994422029

theorem tailTrace_4001590 : CollatzResearch.WordTrace tailWord_4001590 prefixEnd_4001590 2054739052225103994422029 := by
  unfold tailWord_4001590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121873598308145125468139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97299985048620214671660149 9121873598308145125468139)
  ·
    refine ⟨13682810397462217688202209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9121873598308145125468139 13682810397462217688202209)
    ·
      refine ⟨10262107798096663266151657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13682810397462217688202209 10262107798096663266151657)
      ·
        refine ⟨7696580848572497449613743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10262107798096663266151657 7696580848572497449613743)
        ·
          refine ⟨11544871272858746174420615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7696580848572497449613743 11544871272858746174420615)
          ·
            refine ⟨17317306909288119261630923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11544871272858746174420615 17317306909288119261630923)
            ·
              refine ⟨25975960363932178892446385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17317306909288119261630923 25975960363932178892446385)
              ·
                refine ⟨19481970272949134169334789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25975960363932178892446385 19481970272949134169334789)
                ·
                  refine ⟨3652869426177962656750273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19481970272949134169334789 3652869426177962656750273)
                  ·
                    refine ⟨2739652069633471992562705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3652869426177962656750273 2739652069633471992562705)
                    ·
                      refine ⟨2054739052225103994422029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739652069633471992562705 2054739052225103994422029)
                      ·
                        rfl

theorem cell23_4001590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4001590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001590 prefixEnd_4001590 := by exact prefixLift 4001590
  have htrace : WordTrace (prefixWord ++ tailWord_4001590) baseStart_4001590 baseEnd_4001590 := by
    simpa [prefixWord, tailWord_4001590, baseEnd_4001590] using wordTrace_append hprefix tailTrace_4001590
  have hstable : (prefixWord ++ tailWord_4001590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001590).length < 2 ^ (prefixWord ++ tailWord_4001590).sum := by decide
  have hdescent : baseEnd_4001590 < baseStart_4001590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001596 : List Nat := [2, 2, 2, 2, 1, 1, 5, 3, 5]
def baseStart_4001596 : Nat := 118140960795 + 4001596 * 2 ^ 59
def prefixEnd_4001596 : Nat := 4983230072969 + 3 ^ 40 * 4001596 * 2
def baseEnd_4001596 : Nat := 228304681456558996771889

theorem tailTrace_4001596 : CollatzResearch.WordTrace tailWord_4001596 prefixEnd_4001596 228304681456558996771889 := by
  unfold tailWord_4001596
  simp only [CollatzResearch.WordTrace]
  refine ⟨72975098205454292516104321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97300130940605723354805761 72975098205454292516104321)
  ·
    refine ⟨54731323654090719387078241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72975098205454292516104321 54731323654090719387078241)
    ·
      refine ⟨41048492740568039540308681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54731323654090719387078241 41048492740568039540308681)
      ·
        refine ⟨30786369555426029655231511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41048492740568039540308681 30786369555426029655231511)
        ·
          refine ⟨46179554333139044482847267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30786369555426029655231511 46179554333139044482847267)
          ·
            refine ⟨69269331499708566724270901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46179554333139044482847267 69269331499708566724270901)
            ·
              refine ⟨6493999828097678130400397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69269331499708566724270901 6493999828097678130400397)
              ·
                refine ⟨2435249935536629298900149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6493999828097678130400397 2435249935536629298900149)
                ·
                  refine ⟨228304681456558996771889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2435249935536629298900149 228304681456558996771889)
                  ·
                    rfl

theorem cell23_4001596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_4001596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001596 prefixEnd_4001596 := by exact prefixLift 4001596
  have htrace : WordTrace (prefixWord ++ tailWord_4001596) baseStart_4001596 baseEnd_4001596 := by
    simpa [prefixWord, tailWord_4001596, baseEnd_4001596] using wordTrace_append hprefix tailTrace_4001596
  have hstable : (prefixWord ++ tailWord_4001596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001596).length < 2 ^ (prefixWord ++ tailWord_4001596).sum := by decide
  have hdescent : baseEnd_4001596 < baseStart_4001596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001609 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 2, 5]
def baseStart_4001609 : Nat := 118140960795 + 4001609 * 2 ^ 59
def prefixEnd_4001609 : Nat := 4983230072969 + 3 ^ 40 * 4001609 * 2
def baseEnd_4001609 : Nat := 684916269452513140028147

theorem tailTrace_4001609 : CollatzResearch.WordTrace tailWord_4001609 prefixEnd_4001609 684916269452513140028147 := by
  unfold tailWord_4001609
  simp only [CollatzResearch.WordTrace]
  refine ⟨145950670559861488252431881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97300447039907658834954587 145950670559861488252431881)
  ·
    refine ⟨109463002919896116189323911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145950670559861488252431881 109463002919896116189323911)
    ·
      refine ⟨164194504379844174283985867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109463002919896116189323911 164194504379844174283985867)
      ·
        refine ⟨246291756569766261425978801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164194504379844174283985867 246291756569766261425978801)
        ·
          refine ⟨184718817427324696069484101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246291756569766261425978801 184718817427324696069484101)
          ·
            refine ⟨34634778267623380513028269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184718817427324696069484101 34634778267623380513028269)
            ·
              refine ⟨12988041850358767692385601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34634778267623380513028269 12988041850358767692385601)
              ·
                refine ⟨9741031387769075769289201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12988041850358767692385601 9741031387769075769289201)
                ·
                  refine ⟨7305773540826806826966901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9741031387769075769289201 7305773540826806826966901)
                  ·
                    refine ⟨684916269452513140028147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7305773540826806826966901 684916269452513140028147)
                    ·
                      rfl

theorem cell23_4001609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_4001609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001609 prefixEnd_4001609 := by exact prefixLift 4001609
  have htrace : WordTrace (prefixWord ++ tailWord_4001609) baseStart_4001609 baseEnd_4001609 := by
    simpa [prefixWord, tailWord_4001609, baseEnd_4001609] using wordTrace_append hprefix tailTrace_4001609
  have hstable : (prefixWord ++ tailWord_4001609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001609).length < 2 ^ (prefixWord ++ tailWord_4001609).sum := by decide
  have hdescent : baseEnd_4001609 < baseStart_4001609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001613 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 7]
def baseStart_4001613 : Nat := 118140960795 + 4001613 * 2 ^ 59
def prefixEnd_4001613 : Nat := 4983230072969 + 3 ^ 40 * 4001613 * 2
def baseEnd_4001613 : Nat := 228305651364461933826047

theorem tailTrace_4001613 : CollatzResearch.WordTrace tailWord_4001613 prefixEnd_4001613 228305651364461933826047 := by
  unfold tailWord_4001613
  simp only [CollatzResearch.WordTrace]
  refine ⟨145950816451846996935577493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97300544301231331290384995 145950816451846996935577493)
  ·
    refine ⟨6841444521180327981355195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145950816451846996935577493 6841444521180327981355195)
    ·
      refine ⟨10262166781770491972032793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841444521180327981355195 10262166781770491972032793)
      ·
        refine ⟨7696625086327868979024595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10262166781770491972032793 7696625086327868979024595)
        ·
          refine ⟨11544937629491803468536893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7696625086327868979024595 11544937629491803468536893)
          ·
            refine ⟨4329351611059426300701335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11544937629491803468536893 4329351611059426300701335)
            ·
              refine ⟨6494027416589139451052003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329351611059426300701335 6494027416589139451052003)
              ·
                refine ⟨9741041124883709176578005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494027416589139451052003 9741041124883709176578005)
                ·
                  refine ⟨228305651364461933826047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9741041124883709176578005 228305651364461933826047)
                  ·
                    rfl

theorem cell23_4001613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_4001613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001613 prefixEnd_4001613 := by exact prefixLift 4001613
  have htrace : WordTrace (prefixWord ++ tailWord_4001613) baseStart_4001613 baseEnd_4001613 := by
    simpa [prefixWord, tailWord_4001613, baseEnd_4001613] using wordTrace_append hprefix tailTrace_4001613
  have hstable : (prefixWord ++ tailWord_4001613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001613).length < 2 ^ (prefixWord ++ tailWord_4001613).sum := by decide
  have hdescent : baseEnd_4001613 < baseStart_4001613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001673 : List Nat := [1, 2, 1, 1, 5, 1, 3, 4, 1, 4]
def baseStart_4001673 : Nat := 118140960795 + 4001673 * 2 ^ 59
def prefixEnd_4001673 : Nat := 4983230072969 + 3 ^ 40 * 4001673 * 2
def baseEnd_4001673 : Nat := 684927223706475723228049

theorem tailTrace_4001673 : CollatzResearch.WordTrace tailWord_4001673 prefixEnd_4001673 684927223706475723228049 := by
  unfold tailWord_4001673
  simp only [CollatzResearch.WordTrace]
  refine ⟨145953004831629627182761673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97302003221086418121841115 145953004831629627182761673)
  ·
    refine ⟨109464753623722220387071255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145953004831629627182761673 109464753623722220387071255)
    ·
      refine ⟨164197130435583330580606883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109464753623722220387071255 164197130435583330580606883)
      ·
        refine ⟨246295695653374995870910325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164197130435583330580606883 246295695653374995870910325)
        ·
          refine ⟨23090221467503905862897843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246295695653374995870910325 23090221467503905862897843)
          ·
            refine ⟨34635332201255858794346765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23090221467503905862897843 34635332201255858794346765)
            ·
              refine ⟨12988249575470947047880037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34635332201255858794346765 12988249575470947047880037)
              ·
                refine ⟨2435296795400802571477507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12988249575470947047880037 2435296795400802571477507)
                ·
                  refine ⟨3652945193101203857216261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435296795400802571477507 3652945193101203857216261)
                  ·
                    refine ⟨684927223706475723228049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3652945193101203857216261 684927223706475723228049)
                    ·
                      rfl

theorem cell23_4001673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 4].length) (baseStart_4001673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001673 prefixEnd_4001673 := by exact prefixLift 4001673
  have htrace : WordTrace (prefixWord ++ tailWord_4001673) baseStart_4001673 baseEnd_4001673 := by
    simpa [prefixWord, tailWord_4001673, baseEnd_4001673] using wordTrace_append hprefix tailTrace_4001673
  have hstable : (prefixWord ++ tailWord_4001673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001673).length < 2 ^ (prefixWord ++ tailWord_4001673).sum := by decide
  have hdescent : baseEnd_4001673 < baseStart_4001673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001809 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_4001809 : Nat := 118140960795 + 4001809 * 2 ^ 59
def prefixEnd_4001809 : Nat := 4983230072969 + 3 ^ 40 * 4001809 * 2
def baseEnd_4001809 : Nat := 2054851504488438637583521

theorem tailTrace_4001809 : CollatzResearch.WordTrace tailWord_4001809 prefixEnd_4001809 2054851504488438637583521 := by
  unfold tailWord_4001809
  simp only [CollatzResearch.WordTrace]
  refine ⟨145957965159136922409712481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97305310106091281606474987 145957965159136922409712481)
  ·
    refine ⟨109468473869352691807284361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145957965159136922409712481 109468473869352691807284361)
    ·
      refine ⟨82101355402014518855463271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109468473869352691807284361 82101355402014518855463271)
      ·
        refine ⟨123152033103021778283194907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82101355402014518855463271 123152033103021778283194907)
        ·
          refine ⟨184728049654532667424792361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123152033103021778283194907 184728049654532667424792361)
          ·
            refine ⟨138546037240899500568594271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184728049654532667424792361 138546037240899500568594271)
            ·
              refine ⟨207819055861349250852891407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138546037240899500568594271 207819055861349250852891407)
              ·
                refine ⟨311728583792023876279337111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207819055861349250852891407 311728583792023876279337111)
                ·
                  refine ⟨467592875688035814419005667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311728583792023876279337111 467592875688035814419005667)
                  ·
                    refine ⟨701389313532053721628508501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467592875688035814419005667 701389313532053721628508501)
                    ·
                      refine ⟨2054851504488438637583521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 701389313532053721628508501 2054851504488438637583521)
                      ·
                        rfl

theorem cell23_4001809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_4001809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001809 prefixEnd_4001809 := by exact prefixLift 4001809
  have htrace : WordTrace (prefixWord ++ tailWord_4001809) baseStart_4001809 baseEnd_4001809 := by
    simpa [prefixWord, tailWord_4001809, baseEnd_4001809] using wordTrace_append hprefix tailTrace_4001809
  have hstable : (prefixWord ++ tailWord_4001809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001809).length < 2 ^ (prefixWord ++ tailWord_4001809).sum := by decide
  have hdescent : baseEnd_4001809 < baseStart_4001809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001819 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 3, 8]
def baseStart_4001819 : Nat := 118140960795 + 4001819 * 2 ^ 59
def prefixEnd_4001819 : Nat := 4983230072969 + 3 ^ 40 * 4001819 * 2
def baseEnd_4001819 : Nat := 684952213098327866152825

theorem tailTrace_4001819 : CollatzResearch.WordTrace tailWord_4001819 prefixEnd_4001819 684952213098327866152825 := by
  unfold tailWord_4001819
  simp only [CollatzResearch.WordTrace]
  refine ⟨145958329889100694117576511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97305553259400462745051007 145958329889100694117576511)
  ·
    refine ⟨218937494833651041176364767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145958329889100694117576511 218937494833651041176364767)
    ·
      refine ⟨328406242250476561764547151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218937494833651041176364767 328406242250476561764547151)
      ·
        refine ⟨492609363375714842646820727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328406242250476561764547151 492609363375714842646820727)
        ·
          refine ⟨738914045063572263970231091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492609363375714842646820727 738914045063572263970231091)
          ·
            refine ⟨1108371067595358395955346637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738914045063572263970231091 1108371067595358395955346637)
            ·
              refine ⟨415639150348259398483254989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1108371067595358395955346637 415639150348259398483254989)
              ·
                refine ⟨155864681380597274431220621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415639150348259398483254989 155864681380597274431220621)
                ·
                  refine ⟨58449255517723977911707733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155864681380597274431220621 58449255517723977911707733)
                  ·
                    refine ⟨684952213098327866152825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58449255517723977911707733 684952213098327866152825)
                    ·
                      rfl

theorem cell23_4001819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_4001819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001819 prefixEnd_4001819 := by exact prefixLift 4001819
  have htrace : WordTrace (prefixWord ++ tailWord_4001819) baseStart_4001819 baseEnd_4001819 := by
    simpa [prefixWord, tailWord_4001819, baseEnd_4001819] using wordTrace_append hprefix tailTrace_4001819
  have hstable : (prefixWord ++ tailWord_4001819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001819).length < 2 ^ (prefixWord ++ tailWord_4001819).sum := by decide
  have hdescent : baseEnd_4001819 < baseStart_4001819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001856 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_4001856 : Nat := 118140960795 + 4001856 * 2 ^ 59
def prefixEnd_4001856 : Nat := 4983230072969 + 3 ^ 40 * 4001856 * 2
def baseEnd_4001856 : Nat := 2054875638079199953695805

theorem tailTrace_4001856 : CollatzResearch.WordTrace tailWord_4001856 prefixEnd_4001856 2054875638079199953695805 := by
  unfold tailWord_4001856
  simp only [CollatzResearch.WordTrace]
  refine ⟨72979839694983324718336711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97306452926644432957782281 72979839694983324718336711)
  ·
    refine ⟨109469759542474987077505067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72979839694983324718336711 109469759542474987077505067)
    ·
      refine ⟨164204639313712480616257601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109469759542474987077505067 164204639313712480616257601)
      ·
        refine ⟨123153479485284360462193201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164204639313712480616257601 123153479485284360462193201)
        ·
          refine ⟨92365109613963270346644901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123153479485284360462193201 92365109613963270346644901)
          ·
            refine ⟨17318458052618113189995919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92365109613963270346644901 17318458052618113189995919)
            ·
              refine ⟨25977687078927169784993879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17318458052618113189995919 25977687078927169784993879)
              ·
                refine ⟨38966530618390754677490819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25977687078927169784993879 38966530618390754677490819)
                ·
                  refine ⟨58449795927586132016236229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38966530618390754677490819 58449795927586132016236229)
                  ·
                    refine ⟨10959336736422399753044293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58449795927586132016236229 10959336736422399753044293)
                    ·
                      refine ⟨2054875638079199953695805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10959336736422399753044293 2054875638079199953695805)
                      ·
                        rfl

theorem cell23_4001856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_4001856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001856 prefixEnd_4001856 := by exact prefixLift 4001856
  have htrace : WordTrace (prefixWord ++ tailWord_4001856) baseStart_4001856 baseEnd_4001856 := by
    simpa [prefixWord, tailWord_4001856, baseEnd_4001856] using wordTrace_append hprefix tailTrace_4001856
  have hstable : (prefixWord ++ tailWord_4001856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001856).length < 2 ^ (prefixWord ++ tailWord_4001856).sum := by decide
  have hdescent : baseEnd_4001856 < baseStart_4001856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001876 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_4001876 : Nat := 118140960795 + 4001876 * 2 ^ 59
def prefixEnd_4001876 : Nat := 4983230072969 + 3 ^ 40 * 4001876 * 2
def baseEnd_4001876 : Nat := 2054885907692289875445713

theorem tailTrace_4001876 : CollatzResearch.WordTrace tailWord_4001876 prefixEnd_4001876 2054885907692289875445713 := by
  unfold tailWord_4001876
  simp only [CollatzResearch.WordTrace]
  refine ⟨72980204424947096426200741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97306939233262795234934321 72980204424947096426200741)
  ·
    refine ⟨13683788329677580579912639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72980204424947096426200741 13683788329677580579912639)
    ·
      refine ⟨20525682494516370869868959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13683788329677580579912639 20525682494516370869868959)
      ·
        refine ⟨30788523741774556304803439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20525682494516370869868959 30788523741774556304803439)
        ·
          refine ⟨46182785612661834457205159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30788523741774556304803439 46182785612661834457205159)
          ·
            refine ⟨69274178418992751685807739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46182785612661834457205159 69274178418992751685807739)
            ·
              refine ⟨103911267628489127528711609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69274178418992751685807739 103911267628489127528711609)
              ·
                refine ⟨77933450721366845646533707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103911267628489127528711609 77933450721366845646533707)
                ·
                  refine ⟨116900176082050268469800561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77933450721366845646533707 116900176082050268469800561)
                  ·
                    refine ⟨87675132061537701352350421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116900176082050268469800561 87675132061537701352350421)
                    ·
                      refine ⟨2054885907692289875445713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87675132061537701352350421 2054885907692289875445713)
                      ·
                        rfl

theorem cell23_4001876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_4001876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001876 prefixEnd_4001876 := by exact prefixLift 4001876
  have htrace : WordTrace (prefixWord ++ tailWord_4001876) baseStart_4001876 baseEnd_4001876 := by
    simpa [prefixWord, tailWord_4001876, baseEnd_4001876] using wordTrace_append hprefix tailTrace_4001876
  have hstable : (prefixWord ++ tailWord_4001876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001876).length < 2 ^ (prefixWord ++ tailWord_4001876).sum := by decide
  have hdescent : baseEnd_4001876 < baseStart_4001876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001893 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_4001893 : Nat := 118140960795 + 4001893 * 2 ^ 59
def prefixEnd_4001893 : Nat := 4983230072969 + 3 ^ 40 * 4001893 * 2
def baseEnd_4001893 : Nat := 2054894636863416308933135

theorem tailTrace_4001893 : CollatzResearch.WordTrace tailWord_4001893 prefixEnd_4001893 2054894636863416308933135 := by
  unfold tailWord_4001893
  simp only [CollatzResearch.WordTrace]
  refine ⟨145961028890832604755770333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97307352593888403170513555 145961028890832604755770333)
  ·
    refine ⟨54735385834062226783413875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145961028890832604755770333 54735385834062226783413875)
    ·
      refine ⟨82103078751093340175120813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54735385834062226783413875 82103078751093340175120813)
      ·
        refine ⟨30788654531660002565670305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82103078751093340175120813 30788654531660002565670305)
        ·
          refine ⟨23091490898745001924252729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30788654531660002565670305 23091490898745001924252729)
          ·
            refine ⟨17318618174058751443189547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23091490898745001924252729 17318618174058751443189547)
            ·
              refine ⟨25977927261088127164784321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17318618174058751443189547 25977927261088127164784321)
              ·
                refine ⟨19483445445816095373588241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25977927261088127164784321 19483445445816095373588241)
                ·
                  refine ⟨14612584084362071530191181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19483445445816095373588241 14612584084362071530191181)
                  ·
                    refine ⟨5479719031635776823821693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14612584084362071530191181 5479719031635776823821693)
                    ·
                      refine ⟨2054894636863416308933135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5479719031635776823821693 2054894636863416308933135)
                      ·
                        rfl

theorem cell23_4001893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_4001893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001893 prefixEnd_4001893 := by exact prefixLift 4001893
  have htrace : WordTrace (prefixWord ++ tailWord_4001893) baseStart_4001893 baseEnd_4001893 := by
    simpa [prefixWord, tailWord_4001893, baseEnd_4001893] using wordTrace_append hprefix tailTrace_4001893
  have hstable : (prefixWord ++ tailWord_4001893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001893).length < 2 ^ (prefixWord ++ tailWord_4001893).sum := by decide
  have hdescent : baseEnd_4001893 < baseStart_4001893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001910 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4001910 : Nat := 118140960795 + 4001910 * 2 ^ 59
def prefixEnd_4001910 : Nat := 4983230072969 + 3 ^ 40 * 4001910 * 2
def baseEnd_4001910 : Nat := 2054903366034542742420557

theorem tailTrace_4001910 : CollatzResearch.WordTrace tailWord_4001910 prefixEnd_4001910 2054903366034542742420557 := by
  unfold tailWord_4001910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9122603058235688541196199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97307765954514011106092789 9122603058235688541196199)
  ·
    refine ⟨13683904587353532811794299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9122603058235688541196199 13683904587353532811794299)
    ·
      refine ⟨20525856881030299217691449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13683904587353532811794299 20525856881030299217691449)
      ·
        refine ⟨15394392660772724413268587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20525856881030299217691449 15394392660772724413268587)
        ·
          refine ⟨23091588991159086619902881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15394392660772724413268587 23091588991159086619902881)
          ·
            refine ⟨17318691743369314964927161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23091588991159086619902881 17318691743369314964927161)
            ·
              refine ⟨12989018807526986223695371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17318691743369314964927161 12989018807526986223695371)
              ·
                refine ⟨19483528211290479335543057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12989018807526986223695371 19483528211290479335543057)
                ·
                  refine ⟨14612646158467859501657293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19483528211290479335543057 14612646158467859501657293)
                  ·
                    refine ⟨5479742309425447313121485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14612646158467859501657293 5479742309425447313121485)
                    ·
                      refine ⟨2054903366034542742420557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5479742309425447313121485 2054903366034542742420557)
                      ·
                        rfl

theorem cell23_4001910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4001910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001910 prefixEnd_4001910 := by exact prefixLift 4001910
  have htrace : WordTrace (prefixWord ++ tailWord_4001910) baseStart_4001910 baseEnd_4001910 := by
    simpa [prefixWord, tailWord_4001910, baseEnd_4001910] using wordTrace_append hprefix tailTrace_4001910
  have hstable : (prefixWord ++ tailWord_4001910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001910).length < 2 ^ (prefixWord ++ tailWord_4001910).sum := by decide
  have hdescent : baseEnd_4001910 < baseStart_4001910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4001934 : List Nat := [4, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_4001934 : Nat := 118140960795 + 4001934 * 2 ^ 59
def prefixEnd_4001934 : Nat := 4983230072969 + 3 ^ 40 * 4001934 * 2
def baseEnd_4001934 : Nat := 228323965507805627613383

theorem tailTrace_4001934 : CollatzResearch.WordTrace tailWord_4001934 prefixEnd_4001934 228323965507805627613383 := by
  unfold tailWord_4001934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245315535460508594751607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97308349522456045838675237 18245315535460508594751607)
  ·
    refine ⟨27367973303190762892127411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18245315535460508594751607 27367973303190762892127411)
    ·
      refine ⟨41051959954786144338191117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27367973303190762892127411 41051959954786144338191117)
      ·
        refine ⟨15394484983044804126821669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41051959954786144338191117 15394484983044804126821669)
        ·
          refine ⟨2886465934320900773779063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15394484983044804126821669 2886465934320900773779063)
          ·
            refine ⟨4329698901481351160668595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886465934320900773779063 4329698901481351160668595)
            ·
              refine ⟨6494548352222026741002893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329698901481351160668595 6494548352222026741002893)
              ·
                refine ⟨2435455632083260027876085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6494548352222026741002893 2435455632083260027876085)
                ·
                  refine ⟨228323965507805627613383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2435455632083260027876085 228323965507805627613383)
                  ·
                    rfl

theorem cell23_4001934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_4001934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4001934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4001934 prefixEnd_4001934 := by exact prefixLift 4001934
  have htrace : WordTrace (prefixWord ++ tailWord_4001934) baseStart_4001934 baseEnd_4001934 := by
    simpa [prefixWord, tailWord_4001934, baseEnd_4001934] using wordTrace_append hprefix tailTrace_4001934
  have hstable : (prefixWord ++ tailWord_4001934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4001934).length < 2 ^ (prefixWord ++ tailWord_4001934).sum := by decide
  have hdescent : baseEnd_4001934 < baseStart_4001934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4001934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002033 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 1, 6]
def baseStart_4002033 : Nat := 118140960795 + 4002033 * 2 ^ 59
def prefixEnd_4002033 : Nat := 4983230072969 + 3 ^ 40 * 4002033 * 2
def baseEnd_4002033 : Nat := 684988841385015253727497

theorem tailTrace_4002033 : CollatzResearch.WordTrace tailWord_4002033 prefixEnd_4002033 684988841385015253727497 := by
  unfold tailWord_4002033
  simp only [CollatzResearch.WordTrace]
  refine ⟨145966135110325408665866753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97310756740216939110577835 145966135110325408665866753)
  ·
    refine ⟨109474601332744056499400065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145966135110325408665866753 109474601332744056499400065)
    ·
      refine ⟨82105950999558042374550049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109474601332744056499400065 82105950999558042374550049)
      ·
        refine ⟨61579463249668531780912537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82105950999558042374550049 61579463249668531780912537)
        ·
          refine ⟨46184597437251398835684403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61579463249668531780912537 46184597437251398835684403)
          ·
            refine ⟨69276896155877098253526605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46184597437251398835684403 69276896155877098253526605)
            ·
              refine ⟨25978836058453911845072477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69276896155877098253526605 25978836058453911845072477)
              ·
                refine ⟨9742063521920216941902179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25978836058453911845072477 9742063521920216941902179)
                ·
                  refine ⟨14613095282880325412853269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9742063521920216941902179 14613095282880325412853269)
                  ·
                    refine ⟨684988841385015253727497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14613095282880325412853269 684988841385015253727497)
                    ·
                      rfl

theorem cell23_4002033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_4002033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002033 prefixEnd_4002033 := by exact prefixLift 4002033
  have htrace : WordTrace (prefixWord ++ tailWord_4002033) baseStart_4002033 baseEnd_4002033 := by
    simpa [prefixWord, tailWord_4002033, baseEnd_4002033] using wordTrace_append hprefix tailTrace_4002033
  have hstable : (prefixWord ++ tailWord_4002033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002033).length < 2 ^ (prefixWord ++ tailWord_4002033).sum := by decide
  have hdescent : baseEnd_4002033 < baseStart_4002033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002044 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_4002044 : Nat := 118140960795 + 4002044 * 2 ^ 59
def prefixEnd_4002044 : Nat := 4983230072969 + 3 ^ 40 * 4002044 * 2
def baseEnd_4002044 : Nat := 2054972172442245218144941

theorem tailTrace_4002044 : CollatzResearch.WordTrace tailWord_4002044 prefixEnd_4002044 2054972172442245218144941 := by
  unfold tailWord_4002044
  simp only [CollatzResearch.WordTrace]
  refine ⟨72983268156642778772258593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97311024208857038363011457 72983268156642778772258593)
  ·
    refine ⟨54737451117482084079193945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72983268156642778772258593 54737451117482084079193945)
    ·
      refine ⟨41053088338111563059395459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54737451117482084079193945 41053088338111563059395459)
      ·
        refine ⟨61579632507167344589093189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41053088338111563059395459 61579632507167344589093189)
        ·
          refine ⟨11546181095093877110454973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61579632507167344589093189 11546181095093877110454973)
          ·
            refine ⟨4329817910660203916420615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11546181095093877110454973 4329817910660203916420615)
            ·
              refine ⟨6494726865990305874630923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329817910660203916420615 6494726865990305874630923)
              ·
                refine ⟨9742090298985458811946385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494726865990305874630923 9742090298985458811946385)
                ·
                  refine ⟨7306567724239094108959789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9742090298985458811946385 7306567724239094108959789)
                  ·
                    refine ⟨2739962896589660290859921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7306567724239094108959789 2739962896589660290859921)
                    ·
                      refine ⟨2054972172442245218144941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2739962896589660290859921 2054972172442245218144941)
                      ·
                        rfl

theorem cell23_4002044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_4002044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002044 prefixEnd_4002044 := by exact prefixLift 4002044
  have htrace : WordTrace (prefixWord ++ tailWord_4002044) baseStart_4002044 baseEnd_4002044 := by
    simpa [prefixWord, tailWord_4002044, baseEnd_4002044] using wordTrace_append hprefix tailTrace_4002044
  have hstable : (prefixWord ++ tailWord_4002044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002044).length < 2 ^ (prefixWord ++ tailWord_4002044).sum := by decide
  have hdescent : baseEnd_4002044 < baseStart_4002044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002053 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_4002053 : Nat := 118140960795 + 4002053 * 2 ^ 59
def prefixEnd_4002053 : Nat := 4983230072969 + 3 ^ 40 * 4002053 * 2
def baseEnd_4002053 : Nat := 2054976793768135682932399

theorem tailTrace_4002053 : CollatzResearch.WordTrace tailWord_4002053 prefixEnd_4002053 2054976793768135682932399 := by
  unfold tailWord_4002053
  simp only [CollatzResearch.WordTrace]
  refine ⟨145966864570252952081594813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97311243046835301387729875 145966864570252952081594813)
  ·
    refine ⟨54737574213844857030598055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145966864570252952081594813 54737574213844857030598055)
    ·
      refine ⟨82106361320767285545897083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54737574213844857030598055 82106361320767285545897083)
      ·
        refine ⟨123159541981150928318845625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82106361320767285545897083 123159541981150928318845625)
        ·
          refine ⟨92369656485863196239134219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123159541981150928318845625 92369656485863196239134219)
          ·
            refine ⟨138554484728794794358701329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92369656485863196239134219 138554484728794794358701329)
            ·
              refine ⟨103915863546596095769025997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138554484728794794358701329 103915863546596095769025997)
              ·
                refine ⟨38968448829973535913384749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103915863546596095769025997 38968448829973535913384749)
                ·
                  refine ⟨14613168311240075967519281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38968448829973535913384749 14613168311240075967519281)
                  ·
                    refine ⟨10959876233430056975639461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14613168311240075967519281 10959876233430056975639461)
                    ·
                      refine ⟨2054976793768135682932399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10959876233430056975639461 2054976793768135682932399)
                      ·
                        rfl

theorem cell23_4002053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_4002053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002053 prefixEnd_4002053 := by exact prefixLift 4002053
  have htrace : WordTrace (prefixWord ++ tailWord_4002053) baseStart_4002053 baseEnd_4002053 := by
    simpa [prefixWord, tailWord_4002053, baseEnd_4002053] using wordTrace_append hprefix tailTrace_4002053
  have hstable : (prefixWord ++ tailWord_4002053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002053).length < 2 ^ (prefixWord ++ tailWord_4002053).sum := by decide
  have hdescent : baseEnd_4002053 < baseStart_4002053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002057 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 1, 1, 4]
def baseStart_4002057 : Nat := 118140960795 + 4002057 * 2 ^ 59
def prefixEnd_4002057 : Nat := 4983230072969 + 3 ^ 40 * 4002057 * 2
def baseEnd_4002057 : Nat := 2054978847690753667282381

theorem tailTrace_4002057 : CollatzResearch.WordTrace tailWord_4002057 prefixEnd_4002057 2054978847690753667282381 := by
  unfold tailWord_4002057
  simp only [CollatzResearch.WordTrace]
  refine ⟨145967010462238460764740425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97311340308158973843160283 145967010462238460764740425)
  ·
    refine ⟨109475257846678845573555319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145967010462238460764740425 109475257846678845573555319)
    ·
      refine ⟨164212886770018268360332979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109475257846678845573555319 164212886770018268360332979)
      ·
        refine ⟨246319330155027402540499469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164212886770018268360332979 246319330155027402540499469)
        ·
          refine ⟨92369748808135275952687301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246319330155027402540499469 92369748808135275952687301)
          ·
            refine ⟨17319327901525364241128869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92369748808135275952687301 17319327901525364241128869)
            ·
              refine ⟨3247373981536005795211663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17319327901525364241128869 3247373981536005795211663)
              ·
                refine ⟨4871060972304008692817495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247373981536005795211663 4871060972304008692817495)
                ·
                  refine ⟨7306591458456013039226243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871060972304008692817495 7306591458456013039226243)
                  ·
                    refine ⟨10959887187684019558839365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7306591458456013039226243 10959887187684019558839365)
                    ·
                      refine ⟨2054978847690753667282381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10959887187684019558839365 2054978847690753667282381)
                      ·
                        rfl

theorem cell23_4002057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 1, 4].length) (baseStart_4002057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002057 prefixEnd_4002057 := by exact prefixLift 4002057
  have htrace : WordTrace (prefixWord ++ tailWord_4002057) baseStart_4002057 baseEnd_4002057 := by
    simpa [prefixWord, tailWord_4002057, baseEnd_4002057] using wordTrace_append hprefix tailTrace_4002057
  have hstable : (prefixWord ++ tailWord_4002057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002057).length < 2 ^ (prefixWord ++ tailWord_4002057).sum := by decide
  have hdescent : baseEnd_4002057 < baseStart_4002057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002073 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 3]
def baseStart_4002073 : Nat := 118140960795 + 4002073 * 2 ^ 59
def prefixEnd_4002073 : Nat := 4983230072969 + 3 ^ 40 * 4002073 * 2
def baseEnd_4002073 : Nat := 2054987063381225604682307

theorem tailTrace_4002073 : CollatzResearch.WordTrace tailWord_4002073 prefixEnd_4002073 2054987063381225604682307 := by
  unfold tailWord_4002073
  simp only [CollatzResearch.WordTrace]
  refine ⟨145967594030180495497322873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97311729353453663664881915 145967594030180495497322873)
  ·
    refine ⟨109475695522635371622992155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145967594030180495497322873 109475695522635371622992155)
    ·
      refine ⟨164213543283953057434488233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109475695522635371622992155 164213543283953057434488233)
      ·
        refine ⟨123160157462964793075866175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164213543283953057434488233 123160157462964793075866175)
        ·
          refine ⟨184740236194447189613799263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123160157462964793075866175 184740236194447189613799263)
          ·
            refine ⟨277110354291670784420698895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184740236194447189613799263 277110354291670784420698895)
            ·
              refine ⟨415665531437506176631048343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277110354291670784420698895 415665531437506176631048343)
              ·
                refine ⟨623498297156259264946572515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415665531437506176631048343 623498297156259264946572515)
                ·
                  refine ⟨935247445734388897419858773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623498297156259264946572515 935247445734388897419858773)
                  ·
                    refine ⟨5479965502349934945819485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 935247445734388897419858773 5479965502349934945819485)
                    ·
                      refine ⟨2054987063381225604682307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5479965502349934945819485 2054987063381225604682307)
                      ·
                        rfl

theorem cell23_4002073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_4002073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002073 prefixEnd_4002073 := by exact prefixLift 4002073
  have htrace : WordTrace (prefixWord ++ tailWord_4002073) baseStart_4002073 baseEnd_4002073 := by
    simpa [prefixWord, tailWord_4002073, baseEnd_4002073] using wordTrace_append hprefix tailTrace_4002073
  have hstable : (prefixWord ++ tailWord_4002073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002073).length < 2 ^ (prefixWord ++ tailWord_4002073).sum := by decide
  have hdescent : baseEnd_4002073 < baseStart_4002073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002077 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4002077 : Nat := 118140960795 + 4002077 * 2 ^ 59
def prefixEnd_4002077 : Nat := 4983230072969 + 3 ^ 40 * 4002077 * 2
def baseEnd_4002077 : Nat := 2054989117303843589032289

theorem tailTrace_4002077 : CollatzResearch.WordTrace tailWord_4002077 prefixEnd_4002077 2054989117303843589032289 := by
  unfold tailWord_4002077
  simp only [CollatzResearch.WordTrace]
  refine ⟨145967739922166004180468485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97311826614777336120312323 145967739922166004180468485)
  ·
    refine ⟨27368951235406125783837841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145967739922166004180468485 27368951235406125783837841)
    ·
      refine ⟨20526713426554594337878381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27368951235406125783837841 20526713426554594337878381)
      ·
        refine ⟨7697517534957972876704393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20526713426554594337878381 7697517534957972876704393)
        ·
          refine ⟨5773138151218479657528295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697517534957972876704393 5773138151218479657528295)
          ·
            refine ⟨8659707226827719486292443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773138151218479657528295 8659707226827719486292443)
            ·
              refine ⟨12989560840241579229438665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8659707226827719486292443 12989560840241579229438665)
              ·
                refine ⟨9742170630181184422078999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12989560840241579229438665 9742170630181184422078999)
                ·
                  refine ⟨14613255945271776633118499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9742170630181184422078999 14613255945271776633118499)
                  ·
                    refine ⟨21919883917907664949677749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14613255945271776633118499 21919883917907664949677749)
                    ·
                      refine ⟨2054989117303843589032289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21919883917907664949677749 2054989117303843589032289)
                      ·
                        rfl

theorem cell23_4002077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4002077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002077 prefixEnd_4002077 := by exact prefixLift 4002077
  have htrace : WordTrace (prefixWord ++ tailWord_4002077) baseStart_4002077 baseEnd_4002077 := by
    simpa [prefixWord, tailWord_4002077, baseEnd_4002077] using wordTrace_append hprefix tailTrace_4002077
  have hstable : (prefixWord ++ tailWord_4002077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002077).length < 2 ^ (prefixWord ++ tailWord_4002077).sum := by decide
  have hdescent : baseEnd_4002077 < baseStart_4002077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002084 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_4002084 : Nat := 118140960795 + 4002084 * 2 ^ 59
def prefixEnd_4002084 : Nat := 4983230072969 + 3 ^ 40 * 4002084 * 2
def baseEnd_4002084 : Nat := 684997570556141687214919

theorem tailTrace_4002084 : CollatzResearch.WordTrace tailWord_4002084 prefixEnd_4002084 684997570556141687214919 := by
  unfold tailWord_4002084
  simp only [CollatzResearch.WordTrace]
  refine ⟨72983997616570322187986653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97311996822093762917315537 72983997616570322187986653)
  ·
    refine ⟨27368999106213870820494995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72983997616570322187986653 27368999106213870820494995)
    ·
      refine ⟨41053498659320806230742493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27368999106213870820494995 41053498659320806230742493)
      ·
        refine ⟨15395061997245302336528435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41053498659320806230742493 15395061997245302336528435)
        ·
          refine ⟨23092592995867953504792653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15395061997245302336528435 23092592995867953504792653)
          ·
            refine ⟨8659722373450482564297245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23092592995867953504792653 8659722373450482564297245)
            ·
              refine ⟨3247395890043930961611467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8659722373450482564297245 3247395890043930961611467)
              ·
                refine ⟨4871093835065896442417201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247395890043930961611467 4871093835065896442417201)
                ·
                  refine ⟨3653320376299422331812901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871093835065896442417201 3653320376299422331812901)
                  ·
                    refine ⟨684997570556141687214919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3653320376299422331812901 684997570556141687214919)
                    ·
                      rfl

theorem cell23_4002084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_4002084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002084 prefixEnd_4002084 := by exact prefixLift 4002084
  have htrace : WordTrace (prefixWord ++ tailWord_4002084) baseStart_4002084 baseEnd_4002084 := by
    simpa [prefixWord, tailWord_4002084, baseEnd_4002084] using wordTrace_append hprefix tailTrace_4002084
  have hstable : (prefixWord ++ tailWord_4002084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002084).length < 2 ^ (prefixWord ++ tailWord_4002084).sum := by decide
  have hdescent : baseEnd_4002084 < baseStart_4002084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002097 : List Nat := [1, 2, 2, 3, 4, 2, 2, 7]
def baseStart_4002097 : Nat := 118140960795 + 4002097 * 2 ^ 59
def prefixEnd_4002097 : Nat := 4983230072969 + 3 ^ 40 * 4002097 * 2
def baseEnd_4002097 : Nat := 76111088404330870769711

theorem tailTrace_4002097 : CollatzResearch.WordTrace tailWord_4002097 prefixEnd_4002097 76111088404330870769711 := by
  unfold tailWord_4002097
  simp only [CollatzResearch.WordTrace]
  refine ⟨145968469382093547596196545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97312312921395698397464363 145968469382093547596196545)
  ·
    refine ⟨109476352036570160697147409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145968469382093547596196545 109476352036570160697147409)
    ·
      refine ⟨82107264027427620522860557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109476352036570160697147409 82107264027427620522860557)
      ·
        refine ⟨30790224010285357696072709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82107264027427620522860557 30790224010285357696072709)
        ·
          refine ⟨5773167001928504568013633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30790224010285357696072709 5773167001928504568013633)
          ·
            refine ⟨4329875251446378426010225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773167001928504568013633 4329875251446378426010225)
            ·
              refine ⟨3247406438584783819507669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329875251446378426010225 3247406438584783819507669)
              ·
                refine ⟨76111088404330870769711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3247406438584783819507669 76111088404330870769711)
                ·
                  rfl

theorem cell23_4002097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 7].length) (baseStart_4002097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002097 prefixEnd_4002097 := by exact prefixLift 4002097
  have htrace : WordTrace (prefixWord ++ tailWord_4002097) baseStart_4002097 baseEnd_4002097 := by
    simpa [prefixWord, tailWord_4002097, baseEnd_4002097] using wordTrace_append hprefix tailTrace_4002097
  have hstable : (prefixWord ++ tailWord_4002097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002097).length < 2 ^ (prefixWord ++ tailWord_4002097).sum := by decide
  have hdescent : baseEnd_4002097 < baseStart_4002097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002123 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 2, 6]
def baseStart_4002123 : Nat := 118140960795 + 4002123 * 2 ^ 59
def prefixEnd_4002123 : Nat := 4983230072969 + 3 ^ 40 * 4002123 * 2
def baseEnd_4002123 : Nat := 685004245804650136352359

theorem tailTrace_4002123 : CollatzResearch.WordTrace tailWord_4002123 prefixEnd_4002123 685004245804650136352359 := by
  unfold tailWord_4002123
  simp only [CollatzResearch.WordTrace]
  refine ⟨145969417679999354036643023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97312945119999569357762015 145969417679999354036643023)
  ·
    refine ⟨218954126519999031054964535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145969417679999354036643023 218954126519999031054964535)
    ·
      refine ⟨328431189779998546582446803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218954126519999031054964535 328431189779998546582446803)
      ·
        refine ⟨492646784669997819873670205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328431189779998546582446803 492646784669997819873670205)
        ·
          refine ⟨184742544251249182452626327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492646784669997819873670205 184742544251249182452626327)
          ·
            refine ⟨277113816376873773678939491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184742544251249182452626327 277113816376873773678939491)
            ·
              refine ⟨415670724565310660518409237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277113816376873773678939491 415670724565310660518409237)
              ·
                refine ⟨19484565213998937211800433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 415670724565310660518409237 19484565213998937211800433)
                ·
                  refine ⟨14613423910499202908850325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19484565213998937211800433 14613423910499202908850325)
                  ·
                    refine ⟨685004245804650136352359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14613423910499202908850325 685004245804650136352359)
                    ·
                      rfl

theorem cell23_4002123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 6].length) (baseStart_4002123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002123 prefixEnd_4002123 := by exact prefixLift 4002123
  have htrace : WordTrace (prefixWord ++ tailWord_4002123) baseStart_4002123 baseEnd_4002123 := by
    simpa [prefixWord, tailWord_4002123, baseEnd_4002123] using wordTrace_append hprefix tailTrace_4002123
  have hstable : (prefixWord ++ tailWord_4002123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002123).length < 2 ^ (prefixWord ++ tailWord_4002123).sum := by decide
  have hdescent : baseEnd_4002123 < baseStart_4002123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002142 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4002142 : Nat := 118140960795 + 4002142 * 2 ^ 59
def prefixEnd_4002142 : Nat := 4983230072969 + 3 ^ 40 * 4002142 * 2
def baseEnd_4002142 : Nat := 2055022493546385834719491

theorem tailTrace_4002142 : CollatzResearch.WordTrace tailWord_4002142 prefixEnd_4002142 2055022493546385834719491 := by
  unfold tailWord_4002142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18246263833366315035198085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97313407111287013521056453 18246263833366315035198085)
  ·
    refine ⟨3421174468756184069099641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18246263833366315035198085 3421174468756184069099641)
    ·
      refine ⟨2565880851567138051824731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3421174468756184069099641 2565880851567138051824731)
      ·
        refine ⟨3848821277350707077737097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565880851567138051824731 3848821277350707077737097)
        ·
          refine ⟨2886615958013030308302823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848821277350707077737097 2886615958013030308302823)
          ·
            refine ⟨4329923937019545462454235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886615958013030308302823 4329923937019545462454235)
            ·
              refine ⟨6494885905529318193681353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329923937019545462454235 6494885905529318193681353)
              ·
                refine ⟨4871164429146988645261015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6494885905529318193681353 4871164429146988645261015)
                ·
                  refine ⟨7306746643720482967891523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871164429146988645261015 7306746643720482967891523)
                  ·
                    refine ⟨10960119965580724451837285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7306746643720482967891523 10960119965580724451837285)
                    ·
                      refine ⟨2055022493546385834719491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10960119965580724451837285 2055022493546385834719491)
                      ·
                        rfl

theorem cell23_4002142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4002142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002142 prefixEnd_4002142 := by exact prefixLift 4002142
  have htrace : WordTrace (prefixWord ++ tailWord_4002142) baseStart_4002142 baseEnd_4002142 := by
    simpa [prefixWord, tailWord_4002142, baseEnd_4002142] using wordTrace_append hprefix tailTrace_4002142
  have hstable : (prefixWord ++ tailWord_4002142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002142).length < 2 ^ (prefixWord ++ tailWord_4002142).sum := by decide
  have hdescent : baseEnd_4002142 < baseStart_4002142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002147 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 1, 4, 2]
def baseStart_4002147 : Nat := 118140960795 + 4002147 * 2 ^ 59
def prefixEnd_4002147 : Nat := 4983230072969 + 3 ^ 40 * 4002147 * 2
def baseEnd_4002147 : Nat := 2055025060949658315156967

theorem tailTrace_4002147 : CollatzResearch.WordTrace tailWord_4002147 prefixEnd_4002147 2055025060949658315156967 := by
  unfold tailWord_4002147
  simp only [CollatzResearch.WordTrace]
  refine ⟨145970293031912406135516695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97313528687941604090344463 145970293031912406135516695)
  ·
    refine ⟨218955439547868609203275043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145970293031912406135516695 218955439547868609203275043)
    ·
      refine ⟨328433159321802913804912565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218955439547868609203275043 328433159321802913804912565)
      ·
        refine ⟨30790608686419023169210553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328433159321802913804912565 30790608686419023169210553)
        ·
          refine ⟨23092956514814267376907915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30790608686419023169210553 23092956514814267376907915)
          ·
            refine ⟨34639434772221401065361873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23092956514814267376907915 34639434772221401065361873)
            ·
              refine ⟨25979576079166050799021405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34639434772221401065361873 25979576079166050799021405)
              ·
                refine ⟨9742341029687269049633027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25979576079166050799021405 9742341029687269049633027)
                ·
                  refine ⟨14613511544530903574449541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9742341029687269049633027 14613511544530903574449541)
                  ·
                    refine ⟨2740033414599544420209289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14613511544530903574449541 2740033414599544420209289)
                    ·
                      refine ⟨2055025060949658315156967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740033414599544420209289 2055025060949658315156967)
                      ·
                        rfl

theorem cell23_4002147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_4002147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002147 prefixEnd_4002147 := by exact prefixLift 4002147
  have htrace : WordTrace (prefixWord ++ tailWord_4002147) baseStart_4002147 baseEnd_4002147 := by
    simpa [prefixWord, tailWord_4002147, baseEnd_4002147] using wordTrace_append hprefix tailTrace_4002147
  have hstable : (prefixWord ++ tailWord_4002147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002147).length < 2 ^ (prefixWord ++ tailWord_4002147).sum := by decide
  have hdescent : baseEnd_4002147 < baseStart_4002147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002151 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_4002151 : Nat := 118140960795 + 4002151 * 2 ^ 59
def prefixEnd_4002151 : Nat := 4983230072969 + 3 ^ 40 * 4002151 * 2
def baseEnd_4002151 : Nat := 2055027114872276299506949

theorem tailTrace_4002151 : CollatzResearch.WordTrace tailWord_4002151 prefixEnd_4002151 2055027114872276299506949 := by
  unfold tailWord_4002151
  simp only [CollatzResearch.WordTrace]
  refine ⟨145970438923897914818662307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97313625949265276545774871 145970438923897914818662307)
  ·
    refine ⟨218955658385846872227993461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145970438923897914818662307 218955658385846872227993461)
    ·
      refine ⟨20527092973673144271374387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218955658385846872227993461 20527092973673144271374387)
      ·
        refine ⟨30790639460509716407061581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20527092973673144271374387 30790639460509716407061581)
        ·
          refine ⟨11546489797691143652648093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30790639460509716407061581 11546489797691143652648093)
          ·
            refine ⟨4329933674134178869743035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11546489797691143652648093 4329933674134178869743035)
            ·
              refine ⟨6494900511201268304614553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329933674134178869743035 6494900511201268304614553)
              ·
                refine ⟨4871175383400951228460915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6494900511201268304614553 4871175383400951228460915)
                ·
                  refine ⟨7306763075101426842691373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871175383400951228460915 7306763075101426842691373)
                  ·
                    refine ⟨2740036153163035066009265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7306763075101426842691373 2740036153163035066009265)
                    ·
                      refine ⟨2055027114872276299506949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740036153163035066009265 2055027114872276299506949)
                      ·
                        rfl

theorem cell23_4002151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_4002151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002151 prefixEnd_4002151 := by exact prefixLift 4002151
  have htrace : WordTrace (prefixWord ++ tailWord_4002151) baseStart_4002151 baseEnd_4002151 := by
    simpa [prefixWord, tailWord_4002151, baseEnd_4002151] using wordTrace_append hprefix tailTrace_4002151
  have hstable : (prefixWord ++ tailWord_4002151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002151).length < 2 ^ (prefixWord ++ tailWord_4002151).sum := by decide
  have hdescent : baseEnd_4002151 < baseStart_4002151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002153 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 9]
def baseStart_4002153 : Nat := 118140960795 + 4002153 * 2 ^ 59
def prefixEnd_4002153 : Nat := 4983230072969 + 3 ^ 40 * 4002153 * 2
def baseEnd_4002153 : Nat := 228336460203731699075771

theorem tailTrace_4002153 : CollatzResearch.WordTrace tailWord_4002153 prefixEnd_4002153 228336460203731699075771 := by
  unfold tailWord_4002153
  simp only [CollatzResearch.WordTrace]
  refine ⟨145970511869890669160235113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97313674579927112773490075 145970511869890669160235113)
  ·
    refine ⟨109477883902418001870176335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145970511869890669160235113 109477883902418001870176335)
    ·
      refine ⟨164216825853627002805264503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109477883902418001870176335 164216825853627002805264503)
      ·
        refine ⟨246325238780440504207896755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164216825853627002805264503 246325238780440504207896755)
        ·
          refine ⟨369487858170660756311845133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246325238780440504207896755 369487858170660756311845133)
          ·
            refine ⟨138557946813997783616941925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369487858170660756311845133 138557946813997783616941925)
            ·
              refine ⟨25979615027624584428176611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138557946813997783616941925 25979615027624584428176611)
              ·
                refine ⟨38969422541436876642264917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25979615027624584428176611 38969422541436876642264917)
                ·
                  refine ⟨228336460203731699075771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38969422541436876642264917 228336460203731699075771)
                  ·
                    rfl

theorem cell23_4002153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_4002153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002153 prefixEnd_4002153 := by exact prefixLift 4002153
  have htrace : WordTrace (prefixWord ++ tailWord_4002153) baseStart_4002153 baseEnd_4002153 := by
    simpa [prefixWord, tailWord_4002153, baseEnd_4002153] using wordTrace_append hprefix tailTrace_4002153
  have hstable : (prefixWord ++ tailWord_4002153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002153).length < 2 ^ (prefixWord ++ tailWord_4002153).sum := by decide
  have hdescent : baseEnd_4002153 < baseStart_4002153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002187 : List Nat := [1, 1, 1, 1, 4, 5, 1, 4, 5]
def baseStart_4002187 : Nat := 118140960795 + 4002187 * 2 ^ 59
def prefixEnd_4002187 : Nat := 4983230072969 + 3 ^ 40 * 4002187 * 2
def baseEnd_4002187 : Nat := 228338400019537573184087

theorem tailTrace_4002187 : CollatzResearch.WordTrace tailWord_4002187 prefixEnd_4002187 228338400019537573184087 := by
  unfold tailWord_4002187
  simp only [CollatzResearch.WordTrace]
  refine ⟨145971751951767492966972815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97314501301178328644648543 145971751951767492966972815)
  ·
    refine ⟨218957627927651239450459223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145971751951767492966972815 218957627927651239450459223)
    ·
      refine ⟨328436441891476859175688835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218957627927651239450459223 328436441891476859175688835)
      ·
        refine ⟨492654662837215288763533253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328436441891476859175688835 492654662837215288763533253)
        ·
          refine ⟨92372749281977866643162485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 492654662837215288763533253 92372749281977866643162485)
          ·
            refine ⟨8659945245185424997796483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92372749281977866643162485 8659945245185424997796483)
            ·
              refine ⟨12989917867778137496694725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8659945245185424997796483 12989917867778137496694725)
              ·
                refine ⟨2435609600208400780630261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12989917867778137496694725 2435609600208400780630261)
                ·
                  refine ⟨228338400019537573184087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2435609600208400780630261 228338400019537573184087)
                  ·
                    rfl

theorem cell23_4002187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 5].length) (baseStart_4002187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002187 prefixEnd_4002187 := by exact prefixLift 4002187
  have htrace : WordTrace (prefixWord ++ tailWord_4002187) baseStart_4002187 baseEnd_4002187 := by
    simpa [prefixWord, tailWord_4002187, baseEnd_4002187] using wordTrace_append hprefix tailTrace_4002187
  have hstable : (prefixWord ++ tailWord_4002187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002187).length < 2 ^ (prefixWord ++ tailWord_4002187).sum := by decide
  have hdescent : baseEnd_4002187 < baseStart_4002187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002207 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 2, 5, 2]
def baseStart_4002207 : Nat := 118140960795 + 4002207 * 2 ^ 59
def prefixEnd_4002207 : Nat := 4983230072969 + 3 ^ 40 * 4002207 * 2
def baseEnd_4002207 : Nat := 2055055869788928080406691

theorem tailTrace_4002207 : CollatzResearch.WordTrace tailWord_4002207 prefixEnd_4002207 2055055869788928080406691 := by
  unfold tailWord_4002207
  simp only [CollatzResearch.WordTrace]
  refine ⟨145972481411695036382700875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97314987607796690921800583 145972481411695036382700875)
  ·
    refine ⟨218958722117542554574051313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145972481411695036382700875 218958722117542554574051313)
    ·
      refine ⟨164219041588156915930538485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218958722117542554574051313 164219041588156915930538485)
      ·
        refine ⟨15395535148889710868487983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164219041588156915930538485 15395535148889710868487983)
        ·
          refine ⟨23093302723334566302731975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15395535148889710868487983 23093302723334566302731975)
          ·
            refine ⟨34639954085001849454097963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23093302723334566302731975 34639954085001849454097963)
            ·
              refine ⟨51959931127502774181146945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34639954085001849454097963 51959931127502774181146945)
              ·
                refine ⟨38969948345627080635860209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51959931127502774181146945 38969948345627080635860209)
                ·
                  refine ⟨29227461259220310476895157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38969948345627080635860209 29227461259220310476895157)
                  ·
                    refine ⟨2740074493051904107208921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29227461259220310476895157 2740074493051904107208921)
                    ·
                      refine ⟨2055055869788928080406691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740074493051904107208921 2055055869788928080406691)
                      ·
                        rfl

theorem cell23_4002207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_4002207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002207 prefixEnd_4002207 := by exact prefixLift 4002207
  have htrace : WordTrace (prefixWord ++ tailWord_4002207) baseStart_4002207 baseEnd_4002207 := by
    simpa [prefixWord, tailWord_4002207, baseEnd_4002207] using wordTrace_append hprefix tailTrace_4002207
  have hstable : (prefixWord ++ tailWord_4002207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002207).length < 2 ^ (prefixWord ++ tailWord_4002207).sum := by decide
  have hdescent : baseEnd_4002207 < baseStart_4002207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002221 : List Nat := [1, 5, 2, 2, 2, 1, 2, 3, 5]
def baseStart_4002221 : Nat := 118140960795 + 4002221 * 2 ^ 59
def prefixEnd_4002221 : Nat := 4983230072969 + 3 ^ 40 * 4002221 * 2
def baseEnd_4002221 : Nat := 228340339835343447292403

theorem tailTrace_4002221 : CollatzResearch.WordTrace tailWord_4002221 prefixEnd_4002221 228340339835343447292403 := by
  unfold tailWord_4002221
  simp only [CollatzResearch.WordTrace]
  refine ⟨145972992033644316773710517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97315328022429544515807011 145972992033644316773710517)
  ·
    refine ⟨13684968003154154697535361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145972992033644316773710517 13684968003154154697535361)
    ·
      refine ⟨10263726002365616023151521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13684968003154154697535361 10263726002365616023151521)
      ·
        refine ⟨7697794501774212017363641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10263726002365616023151521 7697794501774212017363641)
        ·
          refine ⟨5773345876330659013022731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697794501774212017363641 5773345876330659013022731)
          ·
            refine ⟨8660018814495988519534097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773345876330659013022731 8660018814495988519534097)
            ·
              refine ⟨6495014110871991389650573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8660018814495988519534097 6495014110871991389650573)
              ·
                refine ⟨2435630291576996771118965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6495014110871991389650573 2435630291576996771118965)
                ·
                  refine ⟨228340339835343447292403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2435630291576996771118965 228340339835343447292403)
                  ·
                    rfl

theorem cell23_4002221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_4002221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002221 prefixEnd_4002221 := by exact prefixLift 4002221
  have htrace : WordTrace (prefixWord ++ tailWord_4002221) baseStart_4002221 baseEnd_4002221 := by
    simpa [prefixWord, tailWord_4002221, baseEnd_4002221] using wordTrace_append hprefix tailTrace_4002221
  have hstable : (prefixWord ++ tailWord_4002221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002221).length < 2 ^ (prefixWord ++ tailWord_4002221).sum := by decide
  have hdescent : baseEnd_4002221 < baseStart_4002221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002247 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 3, 4]
def baseStart_4002247 : Nat := 118140960795 + 4002247 * 2 ^ 59
def prefixEnd_4002247 : Nat := 4983230072969 + 3 ^ 40 * 4002247 * 2
def baseEnd_4002247 : Nat := 685025469671702641302169

theorem tailTrace_4002247 : CollatzResearch.WordTrace tailWord_4002247 prefixEnd_4002247 685025469671702641302169 := by
  unfold tailWord_4002247
  simp only [CollatzResearch.WordTrace]
  refine ⟨145973940331550123214156995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97315960221033415476104663 145973940331550123214156995)
  ·
    refine ⟨218960910497325184821235493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145973940331550123214156995 218960910497325184821235493)
    ·
      refine ⟨41055170718248472153981655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218960910497325184821235493 41055170718248472153981655)
      ·
        refine ⟨61582756077372708230972483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41055170718248472153981655 61582756077372708230972483)
        ·
          refine ⟨92374134116059062346458725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61582756077372708230972483 92374134116059062346458725)
          ·
            refine ⟨17320150146761074189961011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92374134116059062346458725 17320150146761074189961011)
            ·
              refine ⟨25980225220141611284941517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17320150146761074189961011 25980225220141611284941517)
              ·
                refine ⟨9742584457553104231853069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25980225220141611284941517 9742584457553104231853069)
                ·
                  refine ⟨3653469171582414086944901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9742584457553104231853069 3653469171582414086944901)
                  ·
                    refine ⟨685025469671702641302169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3653469171582414086944901 685025469671702641302169)
                    ·
                      rfl

theorem cell23_4002247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_4002247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002247 prefixEnd_4002247 := by exact prefixLift 4002247
  have htrace : WordTrace (prefixWord ++ tailWord_4002247) baseStart_4002247 baseEnd_4002247 := by
    simpa [prefixWord, tailWord_4002247, baseEnd_4002247] using wordTrace_append hprefix tailTrace_4002247
  have hstable : (prefixWord ++ tailWord_4002247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002247).length < 2 ^ (prefixWord ++ tailWord_4002247).sum := by decide
  have hdescent : baseEnd_4002247 < baseStart_4002247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002250 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_4002250 : Nat := 118140960795 + 4002250 * 2 ^ 59
def prefixEnd_4002250 : Nat := 4983230072969 + 3 ^ 40 * 4002250 * 2
def baseEnd_4002250 : Nat := 2055077949457071412168993

theorem tailTrace_4002250 : CollatzResearch.WordTrace tailWord_4002250 prefixEnd_4002250 2055077949457071412168993 := by
  unfold tailWord_4002250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36493512437634813681629051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97316033167026169817677469 36493512437634813681629051)
  ·
    refine ⟨54740268656452220522443577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36493512437634813681629051 54740268656452220522443577)
    ·
      refine ⟨41055201492339165391832683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54740268656452220522443577 41055201492339165391832683)
      ·
        refine ⟨61582802238508748087749025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41055201492339165391832683 61582802238508748087749025)
        ·
          refine ⟨46187101678881561065811769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61582802238508748087749025 46187101678881561065811769)
          ·
            refine ⟨34640326259161170799358827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46187101678881561065811769 34640326259161170799358827)
            ·
              refine ⟨51960489388741756199038241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34640326259161170799358827 51960489388741756199038241)
              ·
                refine ⟨38970367041556317149278681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51960489388741756199038241 38970367041556317149278681)
                ·
                  refine ⟨29227775281167237861959011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38970367041556317149278681 29227775281167237861959011)
                  ·
                    refine ⟨43841662921750856792938517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29227775281167237861959011 43841662921750856792938517)
                    ·
                      refine ⟨2055077949457071412168993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43841662921750856792938517 2055077949457071412168993)
                      ·
                        rfl

theorem cell23_4002250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_4002250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002250 prefixEnd_4002250 := by exact prefixLift 4002250
  have htrace : WordTrace (prefixWord ++ tailWord_4002250) baseStart_4002250 baseEnd_4002250 := by
    simpa [prefixWord, tailWord_4002250, baseEnd_4002250] using wordTrace_append hprefix tailTrace_4002250
  have hstable : (prefixWord ++ tailWord_4002250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002250).length < 2 ^ (prefixWord ++ tailWord_4002250).sum := by decide
  have hdescent : baseEnd_4002250 < baseStart_4002250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002300 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_4002300 : Nat := 118140960795 + 4002300 * 2 ^ 59
def prefixEnd_4002300 : Nat := 4983230072969 + 3 ^ 40 * 4002300 * 2
def baseEnd_4002300 : Nat := 2055103623489796216543763

theorem tailTrace_4002300 : CollatzResearch.WordTrace tailWord_4002300 prefixEnd_4002300 2055103623489796216543763 := by
  unfold tailWord_4002300
  simp only [CollatzResearch.WordTrace]
  refine ⟨72987936700179056632918177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97317248933572075510557569 72987936700179056632918177)
  ·
    refine ⟨54740952525134292474688633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72987936700179056632918177 54740952525134292474688633)
    ·
      refine ⟨41055714393850719356016475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54740952525134292474688633 41055714393850719356016475)
      ·
        refine ⟨61583571590776079034024713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41055714393850719356016475 61583571590776079034024713)
        ·
          refine ⟨46187678693082059275518535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61583571590776079034024713 46187678693082059275518535)
          ·
            refine ⟨69281518039623088913277803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46187678693082059275518535 69281518039623088913277803)
            ·
              refine ⟨103922277059434633369916705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69281518039623088913277803 103922277059434633369916705)
              ·
                refine ⟨77941707794575975027437529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103922277059434633369916705 77941707794575975027437529)
                ·
                  refine ⟨58456280845931981270578147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77941707794575975027437529 58456280845931981270578147)
                  ·
                    refine ⟨87684421268897971905867221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58456280845931981270578147 87684421268897971905867221)
                    ·
                      refine ⟨2055103623489796216543763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87684421268897971905867221 2055103623489796216543763)
                      ·
                        rfl

theorem cell23_4002300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_4002300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002300 prefixEnd_4002300 := by exact prefixLift 4002300
  have htrace : WordTrace (prefixWord ++ tailWord_4002300) baseStart_4002300 baseEnd_4002300 := by
    simpa [prefixWord, tailWord_4002300, baseEnd_4002300] using wordTrace_append hprefix tailTrace_4002300
  have hstable : (prefixWord ++ tailWord_4002300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002300).length < 2 ^ (prefixWord ++ tailWord_4002300).sum := by decide
  have hdescent : baseEnd_4002300 < baseStart_4002300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002311 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 6]
def baseStart_4002311 : Nat := 118140960795 + 4002311 * 2 ^ 59
def prefixEnd_4002311 : Nat := 4983230072969 + 3 ^ 40 * 4002311 * 2
def baseEnd_4002311 : Nat := 228345474641888408167357

theorem tailTrace_4002311 : CollatzResearch.WordTrace tailWord_4002311 prefixEnd_4002311 228345474641888408167357 := by
  unfold tailWord_4002311
  simp only [CollatzResearch.WordTrace]
  refine ⟨145976274603318262144486787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97317516402212174762991191 145976274603318262144486787)
  ·
    refine ⟨218964411904977393216730181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145976274603318262144486787 218964411904977393216730181)
    ·
      refine ⟨41055827232183261228136909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218964411904977393216730181 41055827232183261228136909)
      ·
        refine ⟨15395935212068722960551341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41055827232183261228136909 15395935212068722960551341)
        ·
          refine ⟨5773475704525771110206753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15395935212068722960551341 5773475704525771110206753)
          ·
            refine ⟨4330106778394328332655065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773475704525771110206753 4330106778394328332655065)
            ·
              refine ⟨3247580083795746249491299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330106778394328332655065 3247580083795746249491299)
              ·
                refine ⟨4871370125693619374236949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247580083795746249491299 4871370125693619374236949)
                ·
                  refine ⟨228345474641888408167357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4871370125693619374236949 228345474641888408167357)
                  ·
                    rfl

theorem cell23_4002311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 6].length) (baseStart_4002311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002311 prefixEnd_4002311 := by exact prefixLift 4002311
  have htrace : WordTrace (prefixWord ++ tailWord_4002311) baseStart_4002311 baseEnd_4002311 := by
    simpa [prefixWord, tailWord_4002311, baseEnd_4002311] using wordTrace_append hprefix tailTrace_4002311
  have hstable : (prefixWord ++ tailWord_4002311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002311).length < 2 ^ (prefixWord ++ tailWord_4002311).sum := by decide
  have hdescent : baseEnd_4002311 < baseStart_4002311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002314 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_4002314 : Nat := 118140960795 + 4002314 * 2 ^ 59
def prefixEnd_4002314 : Nat := 4983230072969 + 3 ^ 40 * 4002314 * 2
def baseEnd_4002314 : Nat := 2055110812218959161768699

theorem tailTrace_4002314 : CollatzResearch.WordTrace tailWord_4002314 prefixEnd_4002314 2055110812218959161768699 := by
  unfold tailWord_4002314
  simp only [CollatzResearch.WordTrace]
  refine ⟨36494096005576848414211499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97317589348204929104563997 36494096005576848414211499)
  ·
    refine ⟨54741144008365272621317249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36494096005576848414211499 54741144008365272621317249)
    ·
      refine ⟨41055858006273954465987937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54741144008365272621317249 41055858006273954465987937)
      ·
        refine ⟨30791893504705465849490953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41055858006273954465987937 30791893504705465849490953)
        ·
          refine ⟨23093920128529099387118215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30791893504705465849490953 23093920128529099387118215)
          ·
            refine ⟨34640880192793649080677323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23093920128529099387118215 34640880192793649080677323)
            ·
              refine ⟨51961320289190473621015985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34640880192793649080677323 51961320289190473621015985)
              ·
                refine ⟨38970990216892855215761989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51961320289190473621015985 38970990216892855215761989)
                ·
                  refine ⟨7307060665667410352955373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38970990216892855215761989 7307060665667410352955373)
                  ·
                    refine ⟨2740147749625278882358265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7307060665667410352955373 2740147749625278882358265)
                    ·
                      refine ⟨2055110812218959161768699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740147749625278882358265 2055110812218959161768699)
                      ·
                        rfl

theorem cell23_4002314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_4002314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002314 prefixEnd_4002314 := by exact prefixLift 4002314
  have htrace : WordTrace (prefixWord ++ tailWord_4002314) baseStart_4002314 baseEnd_4002314 := by
    simpa [prefixWord, tailWord_4002314, baseEnd_4002314] using wordTrace_append hprefix tailTrace_4002314
  have hstable : (prefixWord ++ tailWord_4002314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002314).length < 2 ^ (prefixWord ++ tailWord_4002314).sum := by decide
  have hdescent : baseEnd_4002314 < baseStart_4002314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002337 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 1, 6]
def baseStart_4002337 : Nat := 118140960795 + 4002337 * 2 ^ 59
def prefixEnd_4002337 : Nat := 4983230072969 + 3 ^ 40 * 4002337 * 2
def baseEnd_4002337 : Nat := 685040874091337523927031

theorem tailTrace_4002337 : CollatzResearch.WordTrace tailWord_4002337 prefixEnd_4002337 685040874091337523927031 := by
  unfold tailWord_4002337
  simp only [CollatzResearch.WordTrace]
  refine ⟨145977222901224068584933265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97318148600816045723288843 145977222901224068584933265)
  ·
    refine ⟨109482917175918051438699949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145977222901224068584933265 109482917175918051438699949)
    ·
      refine ⟨41056093940969269289512481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109482917175918051438699949 41056093940969269289512481)
      ·
        refine ⟨30792070455726951967134361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41056093940969269289512481 30792070455726951967134361)
        ·
          refine ⟨23094052841795213975350771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30792070455726951967134361 23094052841795213975350771)
          ·
            refine ⟨34641079262692820963026157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23094052841795213975350771 34641079262692820963026157)
            ·
              refine ⟨12990404723509807861134809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34641079262692820963026157 12990404723509807861134809)
              ·
                refine ⟨9742803542632355895851107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12990404723509807861134809 9742803542632355895851107)
                ·
                  refine ⟨14614205313948533843776661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9742803542632355895851107 14614205313948533843776661)
                  ·
                    refine ⟨685040874091337523927031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14614205313948533843776661 685040874091337523927031)
                    ·
                      rfl

theorem cell23_4002337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_4002337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002337 prefixEnd_4002337 := by exact prefixLift 4002337
  have htrace : WordTrace (prefixWord ++ tailWord_4002337) baseStart_4002337 baseEnd_4002337 := by
    simpa [prefixWord, tailWord_4002337, baseEnd_4002337] using wordTrace_append hprefix tailTrace_4002337
  have hstable : (prefixWord ++ tailWord_4002337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002337).length < 2 ^ (prefixWord ++ tailWord_4002337).sum := by decide
  have hdescent : baseEnd_4002337 < baseStart_4002337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002349 : List Nat := [1, 5, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4002349 : Nat := 118140960795 + 4002349 * 2 ^ 59
def prefixEnd_4002349 : Nat := 4983230072969 + 3 ^ 40 * 4002349 * 2
def baseEnd_4002349 : Nat := 685042928013955508277013

theorem tailTrace_4002349 : CollatzResearch.WordTrace tailWord_4002349 prefixEnd_4002349 685042928013955508277013 := by
  unfold tailWord_4002349
  simp only [CollatzResearch.WordTrace]
  refine ⟨145977660577180594634370101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97318440384787063089580067 145977660577180594634370101)
  ·
    refine ⟨13685405679110680746972197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145977660577180594634370101 13685405679110680746972197)
    ·
      refine ⟨2566013564833252640057287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13685405679110680746972197 2566013564833252640057287)
      ·
        refine ⟨3849020347249878960085931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566013564833252640057287 3849020347249878960085931)
        ·
          refine ⟨5773530520874818440128897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849020347249878960085931 5773530520874818440128897)
          ·
            refine ⟨4330147890656113830096673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773530520874818440128897 4330147890656113830096673)
            ·
              refine ⟨3247610917992085372572505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330147890656113830096673 3247610917992085372572505)
              ·
                refine ⟨2435708188494064029429379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3247610917992085372572505 2435708188494064029429379)
                ·
                  refine ⟨3653562282741096044144069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435708188494064029429379 3653562282741096044144069)
                  ·
                    refine ⟨685042928013955508277013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3653562282741096044144069 685042928013955508277013)
                    ·
                      rfl

theorem cell23_4002349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4002349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002349 prefixEnd_4002349 := by exact prefixLift 4002349
  have htrace : WordTrace (prefixWord ++ tailWord_4002349) baseStart_4002349 baseEnd_4002349 := by
    simpa [prefixWord, tailWord_4002349, baseEnd_4002349] using wordTrace_append hprefix tailTrace_4002349
  have hstable : (prefixWord ++ tailWord_4002349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002349).length < 2 ^ (prefixWord ++ tailWord_4002349).sum := by decide
  have hdescent : baseEnd_4002349 < baseStart_4002349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002354 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_4002354 : Nat := 118140960795 + 4002354 * 2 ^ 59
def prefixEnd_4002354 : Nat := 4983230072969 + 3 ^ 40 * 4002354 * 2
def baseEnd_4002354 : Nat := 685043783815046335089505

theorem tailTrace_4002354 : CollatzResearch.WordTrace tailWord_4002354 prefixEnd_4002354 685043783815046335089505 := by
  unfold tailWord_4002354
  simp only [CollatzResearch.WordTrace]
  refine ⟨36494460735540620122075529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97318561961441653658868077 36494460735540620122075529)
  ·
    refine ⟨27370845551655465091556647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36494460735540620122075529 27370845551655465091556647)
    ·
      refine ⟨41056268327483197637334971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27370845551655465091556647 41056268327483197637334971)
      ·
        refine ⟨61584402491224796456002457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41056268327483197637334971 61584402491224796456002457)
        ·
          refine ⟨46188301868418597342001843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61584402491224796456002457 46188301868418597342001843)
          ·
            refine ⟨69282452802627896013002765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46188301868418597342001843 69282452802627896013002765)
            ·
              refine ⟨25980919800985461004876037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69282452802627896013002765 25980919800985461004876037)
              ·
                refine ⟨4871422462684773938414257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25980919800985461004876037 4871422462684773938414257)
                ·
                  refine ⟨3653566847013580453810693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871422462684773938414257 3653566847013580453810693)
                  ·
                    refine ⟨685043783815046335089505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3653566847013580453810693 685043783815046335089505)
                    ·
                      rfl

theorem cell23_4002354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_4002354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002354 prefixEnd_4002354 := by exact prefixLift 4002354
  have htrace : WordTrace (prefixWord ++ tailWord_4002354) baseStart_4002354 baseEnd_4002354 := by
    simpa [prefixWord, tailWord_4002354, baseEnd_4002354] using wordTrace_append hprefix tailTrace_4002354
  have hstable : (prefixWord ++ tailWord_4002354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002354).length < 2 ^ (prefixWord ++ tailWord_4002354).sum := by decide
  have hdescent : baseEnd_4002354 < baseStart_4002354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002357 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4002357 : Nat := 118140960795 + 4002357 * 2 ^ 59
def prefixEnd_4002357 : Nat := 4983230072969 + 3 ^ 40 * 4002357 * 2
def baseEnd_4002357 : Nat := 2055132891887102493531001

theorem tailTrace_4002357 : CollatzResearch.WordTrace tailWord_4002357 prefixEnd_4002357 2055132891887102493531001 := by
  unfold tailWord_4002357
  simp only [CollatzResearch.WordTrace]
  refine ⟨145977952361151612000661325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97318634907434408000440883 145977952361151612000661325)
  ·
    refine ⟨54741732135431854500247997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145977952361151612000661325 54741732135431854500247997)
    ·
      refine ⟨20528149550786945437592999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54741732135431854500247997 20528149550786945437592999)
      ·
        refine ⟨30792224326180418156389499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20528149550786945437592999 30792224326180418156389499)
        ·
          refine ⟨46188336489270627234584249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30792224326180418156389499 46188336489270627234584249)
          ·
            refine ⟨34641252366952970425938187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46188336489270627234584249 34641252366952970425938187)
            ·
              refine ⟨51961878550429455638907281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34641252366952970425938187 51961878550429455638907281)
              ·
                refine ⟨38971408912822091729180461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51961878550429455638907281 38971408912822091729180461)
                ·
                  refine ⟨14614278342308284398442673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38971408912822091729180461 14614278342308284398442673)
                  ·
                    refine ⟨10960708756731213298832005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14614278342308284398442673 10960708756731213298832005)
                    ·
                      refine ⟨2055132891887102493531001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10960708756731213298832005 2055132891887102493531001)
                      ·
                        rfl

theorem cell23_4002357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4002357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002357 prefixEnd_4002357 := by exact prefixLift 4002357
  have htrace : WordTrace (prefixWord ++ tailWord_4002357) baseStart_4002357 baseEnd_4002357 := by
    simpa [prefixWord, tailWord_4002357, baseEnd_4002357] using wordTrace_append hprefix tailTrace_4002357
  have hstable : (prefixWord ++ tailWord_4002357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002357).length < 2 ^ (prefixWord ++ tailWord_4002357).sum := by decide
  have hdescent : baseEnd_4002357 < baseStart_4002357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002361 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4002361 : Nat := 118140960795 + 4002361 * 2 ^ 59
def prefixEnd_4002361 : Nat := 4983230072969 + 3 ^ 40 * 4002361 * 2
def baseEnd_4002361 : Nat := 2055134945809720477880983

theorem tailTrace_4002361 : CollatzResearch.WordTrace tailWord_4002361 prefixEnd_4002361 2055134945809720477880983 := by
  unfold tailWord_4002361
  simp only [CollatzResearch.WordTrace]
  refine ⟨145978098253137120683806937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97318732168758080455871291 145978098253137120683806937)
  ·
    refine ⟨109483573689852840512855203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145978098253137120683806937 109483573689852840512855203)
    ·
      refine ⟨164225360534779260769282805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109483573689852840512855203 164225360534779260769282805)
      ·
        refine ⟨15396127550135555697120263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164225360534779260769282805 15396127550135555697120263)
        ·
          refine ⟨23094191325203333545680395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15396127550135555697120263 23094191325203333545680395)
          ·
            refine ⟨34641286987805000318520593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23094191325203333545680395 34641286987805000318520593)
            ·
              refine ⟨25980965240853750238890445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34641286987805000318520593 25980965240853750238890445)
              ·
                refine ⟨9742861965320156339583917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25980965240853750238890445 9742861965320156339583917)
                ·
                  refine ⟨3653573236995058627343969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9742861965320156339583917 3653573236995058627343969)
                  ·
                    refine ⟨2740179927746293970507977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3653573236995058627343969 2740179927746293970507977)
                    ·
                      refine ⟨2055134945809720477880983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740179927746293970507977 2055134945809720477880983)
                      ·
                        rfl

theorem cell23_4002361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4002361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002361 prefixEnd_4002361 := by exact prefixLift 4002361
  have htrace : WordTrace (prefixWord ++ tailWord_4002361) baseStart_4002361 baseEnd_4002361 := by
    simpa [prefixWord, tailWord_4002361, baseEnd_4002361] using wordTrace_append hprefix tailTrace_4002361
  have hstable : (prefixWord ++ tailWord_4002361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002361).length < 2 ^ (prefixWord ++ tailWord_4002361).sum := by decide
  have hdescent : baseEnd_4002361 < baseStart_4002361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002364 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_4002364 : Nat := 118140960795 + 4002364 * 2 ^ 59
def prefixEnd_4002364 : Nat := 4983230072969 + 3 ^ 40 * 4002364 * 2
def baseEnd_4002364 : Nat := 2055136486251683966143469

theorem tailTrace_4002364 : CollatzResearch.WordTrace tailWord_4002364 prefixEnd_4002364 2055136486251683966143469 := by
  unfold tailWord_4002364
  simp only [CollatzResearch.WordTrace]
  refine ⟨72989103836063126098083073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97318805114750834797444097 72989103836063126098083073)
  ·
    refine ⟨54741827877047344573562305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72989103836063126098083073 54741827877047344573562305)
    ·
      refine ⟨41056370907785508430171729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54741827877047344573562305 41056370907785508430171729)
      ·
        refine ⟨30792278180839131322628797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41056370907785508430171729 30792278180839131322628797)
        ·
          refine ⟨11547104317814674245985799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30792278180839131322628797 11547104317814674245985799)
          ·
            refine ⟨17320656476722011368978699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547104317814674245985799 17320656476722011368978699)
            ·
              refine ⟨25980984715083017053468049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17320656476722011368978699 25980984715083017053468049)
              ·
                refine ⟨19485738536312262790101037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25980984715083017053468049 19485738536312262790101037)
                ·
                  refine ⟨7307151951117098546287889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19485738536312262790101037 7307151951117098546287889)
                  ·
                    refine ⟨5480363963337823909715917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7307151951117098546287889 5480363963337823909715917)
                    ·
                      refine ⟨2055136486251683966143469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5480363963337823909715917 2055136486251683966143469)
                      ·
                        rfl

theorem cell23_4002364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_4002364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002364 prefixEnd_4002364 := by exact prefixLift 4002364
  have htrace : WordTrace (prefixWord ++ tailWord_4002364) baseStart_4002364 baseEnd_4002364 := by
    simpa [prefixWord, tailWord_4002364, baseEnd_4002364] using wordTrace_append hprefix tailTrace_4002364
  have hstable : (prefixWord ++ tailWord_4002364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002364).length < 2 ^ (prefixWord ++ tailWord_4002364).sum := by decide
  have hdescent : baseEnd_4002364 < baseStart_4002364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002381 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4002381 : Nat := 118140960795 + 4002381 * 2 ^ 59
def prefixEnd_4002381 : Nat := 4983230072969 + 3 ^ 40 * 4002381 * 2
def baseEnd_4002381 : Nat := 2055145215422810399630891

theorem tailTrace_4002381 : CollatzResearch.WordTrace tailWord_4002381 prefixEnd_4002381 2055145215422810399630891 := by
  unfold tailWord_4002381
  simp only [CollatzResearch.WordTrace]
  refine ⟨145978827713064664099534997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97319218475376442733023331 145978827713064664099534997)
  ·
    refine ⟨6842757549049906129665703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145978827713064664099534997 6842757549049906129665703)
    ·
      refine ⟨10264136323574859194498555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6842757549049906129665703 10264136323574859194498555)
      ·
        refine ⟨15396204485362288791747833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264136323574859194498555 15396204485362288791747833)
        ·
          refine ⟨11547153364021716593810875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15396204485362288791747833 11547153364021716593810875)
          ·
            refine ⟨17320730046032574890716313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547153364021716593810875 17320730046032574890716313)
            ·
              refine ⟨12990547534524431168037235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17320730046032574890716313 12990547534524431168037235)
              ·
                refine ⟨19485821301786646752055853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12990547534524431168037235 19485821301786646752055853)
                ·
                  refine ⟨7307182988169992532020945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19485821301786646752055853 7307182988169992532020945)
                  ·
                    refine ⟨5480387241127494399015709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7307182988169992532020945 5480387241127494399015709)
                    ·
                      refine ⟨2055145215422810399630891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5480387241127494399015709 2055145215422810399630891)
                      ·
                        rfl

theorem cell23_4002381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4002381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002381 prefixEnd_4002381 := by exact prefixLift 4002381
  have htrace : WordTrace (prefixWord ++ tailWord_4002381) baseStart_4002381 baseEnd_4002381 := by
    simpa [prefixWord, tailWord_4002381, baseEnd_4002381] using wordTrace_append hprefix tailTrace_4002381
  have hstable : (prefixWord ++ tailWord_4002381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002381).length < 2 ^ (prefixWord ++ tailWord_4002381).sum := by decide
  have hdescent : baseEnd_4002381 < baseStart_4002381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002468 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_4002468 : Nat := 118140960795 + 4002468 * 2 ^ 59
def prefixEnd_4002468 : Nat := 4983230072969 + 3 ^ 40 * 4002468 * 2
def baseEnd_4002468 : Nat := 2055189888239751559242991

theorem tailTrace_4002468 : CollatzResearch.WordTrace tailWord_4002468 prefixEnd_4002468 2055189888239751559242991 := by
  unfold tailWord_4002468
  simp only [CollatzResearch.WordTrace]
  refine ⟨72991000431874738978976029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97321333909166318638634705 72991000431874738978976029)
  ·
    refine ⟨27371625161953027117116011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72991000431874738978976029 27371625161953027117116011)
    ·
      refine ⟨41057437742929540675674017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27371625161953027117116011 41057437742929540675674017)
      ·
        refine ⟨30793078307197155506755513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41057437742929540675674017 30793078307197155506755513)
        ·
          refine ⟨23094808730397866630066635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30793078307197155506755513 23094808730397866630066635)
          ·
            refine ⟨34642213095596799945099953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23094808730397866630066635 34642213095596799945099953)
            ·
              refine ⟨25981659821697599958824965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34642213095596799945099953 25981659821697599958824965)
              ·
                refine ⟨4871561216568299992279681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25981659821697599958824965 4871561216568299992279681)
                ·
                  refine ⟨3653670912426224994209761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871561216568299992279681 3653670912426224994209761)
                  ·
                    refine ⟨2740253184319668745657321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3653670912426224994209761 2740253184319668745657321)
                    ·
                      refine ⟨2055189888239751559242991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740253184319668745657321 2055189888239751559242991)
                      ·
                        rfl

theorem cell23_4002468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_4002468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002468 prefixEnd_4002468 := by exact prefixLift 4002468
  have htrace : WordTrace (prefixWord ++ tailWord_4002468) baseStart_4002468 baseEnd_4002468 := by
    simpa [prefixWord, tailWord_4002468, baseEnd_4002468] using wordTrace_append hprefix tailTrace_4002468
  have hstable : (prefixWord ++ tailWord_4002468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002468).length < 2 ^ (prefixWord ++ tailWord_4002468).sum := by decide
  have hdescent : baseEnd_4002468 < baseStart_4002468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002485 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4002485 : Nat := 118140960795 + 4002485 * 2 ^ 59
def prefixEnd_4002485 : Nat := 4983230072969 + 3 ^ 40 * 4002485 * 2
def baseEnd_4002485 : Nat := 2055198617410877992730413

theorem tailTrace_4002485 : CollatzResearch.WordTrace tailWord_4002485 prefixEnd_4002485 2055198617410877992730413 := by
  unfold tailWord_4002485
  simp only [CollatzResearch.WordTrace]
  refine ⟨145982620904687889861320909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97321747269791926574213939 145982620904687889861320909)
  ·
    refine ⟨54743482839257958697995341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145982620904687889861320909 54743482839257958697995341)
    ·
      refine ⟨20528806064721734511748253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54743482839257958697995341 20528806064721734511748253)
      ·
        refine ⟨7698302274270650441905595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20528806064721734511748253 7698302274270650441905595)
        ·
          refine ⟨11547453411405975662858393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7698302274270650441905595 11547453411405975662858393)
          ·
            refine ⟨8660590058554481747143795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11547453411405975662858393 8660590058554481747143795)
            ·
              refine ⟨12990885087831722620715693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660590058554481747143795 12990885087831722620715693)
              ·
                refine ⟨4871581907936895982768385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12990885087831722620715693 4871581907936895982768385)
                ·
                  refine ⟨3653686430952671987076289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871581907936895982768385 3653686430952671987076289)
                  ·
                    refine ⟨2740264823214503990307217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3653686430952671987076289 2740264823214503990307217)
                    ·
                      refine ⟨2055198617410877992730413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740264823214503990307217 2055198617410877992730413)
                      ·
                        rfl

theorem cell23_4002485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4002485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002485 prefixEnd_4002485 := by exact prefixLift 4002485
  have htrace : WordTrace (prefixWord ++ tailWord_4002485) baseStart_4002485 baseEnd_4002485 := by
    simpa [prefixWord, tailWord_4002485, baseEnd_4002485] using wordTrace_append hprefix tailTrace_4002485
  have hstable : (prefixWord ++ tailWord_4002485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002485).length < 2 ^ (prefixWord ++ tailWord_4002485).sum := by decide
  have hdescent : baseEnd_4002485 < baseStart_4002485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002502 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4002502 : Nat := 118140960795 + 4002502 * 2 ^ 59
def prefixEnd_4002502 : Nat := 4983230072969 + 3 ^ 40 * 4002502 * 2
def baseEnd_4002502 : Nat := 2055207346582004426217835

theorem tailTrace_4002502 : CollatzResearch.WordTrace tailWord_4002502 prefixEnd_4002502 2055207346582004426217835 := by
  unfold tailWord_4002502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561976279550821930146555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97322160630417534509793173 4561976279550821930146555)
  ·
    refine ⟨6842964419326232895219833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561976279550821930146555 6842964419326232895219833)
    ·
      refine ⟨5132223314494674671414875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6842964419326232895219833 5132223314494674671414875)
      ·
        refine ⟨7698334971742012007122313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132223314494674671414875 7698334971742012007122313)
        ·
          refine ⟨5773751228806509005341735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7698334971742012007122313 5773751228806509005341735)
          ·
            refine ⟨8660626843209763508012603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773751228806509005341735 8660626843209763508012603)
            ·
              refine ⟨12990940264814645262018905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660626843209763508012603 12990940264814645262018905)
              ·
                refine ⟨9743205198610983946514179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12990940264814645262018905 9743205198610983946514179)
                ·
                  refine ⟨14614807797916475919771269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9743205198610983946514179 14614807797916475919771269)
                  ·
                    refine ⟨2740276462109339234957113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14614807797916475919771269 2740276462109339234957113)
                    ·
                      refine ⟨2055207346582004426217835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740276462109339234957113 2055207346582004426217835)
                      ·
                        rfl

theorem cell23_4002502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4002502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002502 prefixEnd_4002502 := by exact prefixLift 4002502
  have htrace : WordTrace (prefixWord ++ tailWord_4002502) baseStart_4002502 baseEnd_4002502 := by
    simpa [prefixWord, tailWord_4002502, baseEnd_4002502] using wordTrace_append hprefix tailTrace_4002502
  have hstable : (prefixWord ++ tailWord_4002502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002502).length < 2 ^ (prefixWord ++ tailWord_4002502).sum := by decide
  have hdescent : baseEnd_4002502 < baseStart_4002502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002504 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 2, 5]
def baseStart_4002504 : Nat := 118140960795 + 4002504 * 2 ^ 59
def prefixEnd_4002504 : Nat := 4983230072969 + 3 ^ 40 * 4002504 * 2
def baseEnd_4002504 : Nat := 685069457847771139464275

theorem tailTrace_4002504 : CollatzResearch.WordTrace tailWord_4002504 prefixEnd_4002504 685069457847771139464275 := by
  unfold tailWord_4002504
  simp only [CollatzResearch.WordTrace]
  refine ⟨72991656945809528053131283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97322209261079370737508377 72991656945809528053131283)
  ·
    refine ⟨109487485418714292079696925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72991656945809528053131283 109487485418714292079696925)
    ·
      refine ⟨41057807032017859529886347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109487485418714292079696925 41057807032017859529886347)
      ·
        refine ⟨61586710548026789294829521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41057807032017859529886347 61586710548026789294829521)
        ·
          refine ⟨46190032911020091971122141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61586710548026789294829521 46190032911020091971122141)
          ·
            refine ⟨17321262341632534489170803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46190032911020091971122141 17321262341632534489170803)
            ·
              refine ⟨25981893512448801733756205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17321262341632534489170803 25981893512448801733756205)
              ·
                refine ⟨9743210067168300650158577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25981893512448801733756205 9743210067168300650158577)
                ·
                  refine ⟨7307407550376225487618933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9743210067168300650158577 7307407550376225487618933)
                  ·
                    refine ⟨685069457847771139464275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7307407550376225487618933 685069457847771139464275)
                    ·
                      rfl

theorem cell23_4002504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_4002504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002504 prefixEnd_4002504 := by exact prefixLift 4002504
  have htrace : WordTrace (prefixWord ++ tailWord_4002504) baseStart_4002504 baseEnd_4002504 := by
    simpa [prefixWord, tailWord_4002504, baseEnd_4002504] using wordTrace_append hprefix tailTrace_4002504
  have hstable : (prefixWord ++ tailWord_4002504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002504).length < 2 ^ (prefixWord ++ tailWord_4002504).sum := by decide
  have hdescent : baseEnd_4002504 < baseStart_4002504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002544 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3]
def baseStart_4002544 : Nat := 118140960795 + 4002544 * 2 ^ 59
def prefixEnd_4002544 : Nat := 4983230072969 + 3 ^ 40 * 4002544 * 2
def baseEnd_4002544 : Nat := 2055228912769493261892641

theorem tailTrace_4002544 : CollatzResearch.WordTrace tailWord_4002544 prefixEnd_4002544 2055228912769493261892641 := by
  unfold tailWord_4002544
  simp only [CollatzResearch.WordTrace]
  refine ⟨72992386405737071468859343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97323181874316095291812457 72992386405737071468859343)
  ·
    refine ⟨109488579608605607203289015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72992386405737071468859343 109488579608605607203289015)
    ·
      refine ⟨164232869412908410804933523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109488579608605607203289015 164232869412908410804933523)
      ·
        refine ⟨246349304119362616207400285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164232869412908410804933523 246349304119362616207400285)
        ·
          refine ⟨92380989044760981077775107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246349304119362616207400285 92380989044760981077775107)
          ·
            refine ⟨138571483567141471616662661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92380989044760981077775107 138571483567141471616662661)
            ·
              refine ⟨25982153168839025928124249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138571483567141471616662661 25982153168839025928124249)
              ·
                refine ⟨19486614876629269446093187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25982153168839025928124249 19486614876629269446093187)
                ·
                  refine ⟨29229922314943904169139781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19486614876629269446093187 29229922314943904169139781)
                  ·
                    refine ⟨5480610434051982031713709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29229922314943904169139781 5480610434051982031713709)
                    ·
                      refine ⟨2055228912769493261892641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5480610434051982031713709 2055228912769493261892641)
                      ·
                        rfl

theorem cell23_4002544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_4002544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002544 prefixEnd_4002544 := by exact prefixLift 4002544
  have htrace : WordTrace (prefixWord ++ tailWord_4002544) baseStart_4002544 baseEnd_4002544 := by
    simpa [prefixWord, tailWord_4002544, baseEnd_4002544] using wordTrace_append hprefix tailTrace_4002544
  have hstable : (prefixWord ++ tailWord_4002544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002544).length < 2 ^ (prefixWord ++ tailWord_4002544).sum := by decide
  have hdescent : baseEnd_4002544 < baseStart_4002544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002547 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 10]
def baseStart_4002547 : Nat := 118140960795 + 4002547 * 2 ^ 59
def prefixEnd_4002547 : Nat := 4983230072969 + 3 ^ 40 * 4002547 * 2
def baseEnd_4002547 : Nat := 228358939245717416683903

theorem tailTrace_4002547 : CollatzResearch.WordTrace tailWord_4002547 prefixEnd_4002547 228358939245717416683903 := by
  unfold tailWord_4002547
  simp only [CollatzResearch.WordTrace]
  refine ⟨145984882230463274450077895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97323254820308849633385263 145984882230463274450077895)
  ·
    refine ⟨218977323345694911675116843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145984882230463274450077895 218977323345694911675116843)
    ·
      refine ⟨328465985018542367512675265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218977323345694911675116843 328465985018542367512675265)
      ·
        refine ⟨246349488763906775634506449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328465985018542367512675265 246349488763906775634506449)
        ·
          refine ⟨184762116572930081725879837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246349488763906775634506449 184762116572930081725879837)
          ·
            refine ⟨69285793714848780647204939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184762116572930081725879837 69285793714848780647204939)
            ·
              refine ⟨103928690572273170970807409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69285793714848780647204939 103928690572273170970807409)
              ·
                refine ⟨77946517929204878228105557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103928690572273170970807409 77946517929204878228105557)
                ·
                  refine ⟨228358939245717416683903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 77946517929204878228105557 228358939245717416683903)
                  ·
                    rfl

theorem cell23_4002547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 10].length) (baseStart_4002547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002547 prefixEnd_4002547 := by exact prefixLift 4002547
  have htrace : WordTrace (prefixWord ++ tailWord_4002547) baseStart_4002547 baseEnd_4002547 := by
    simpa [prefixWord, tailWord_4002547, baseEnd_4002547] using wordTrace_append hprefix tailTrace_4002547
  have hstable : (prefixWord ++ tailWord_4002547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002547).length < 2 ^ (prefixWord ++ tailWord_4002547).sum := by decide
  have hdescent : baseEnd_4002547 < baseStart_4002547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002558 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_4002558 : Nat := 118140960795 + 4002558 * 2 ^ 59
def prefixEnd_4002558 : Nat := 4983230072969 + 3 ^ 40 * 4002558 * 2
def baseEnd_4002558 : Nat := 2055236101498656207117577

theorem tailTrace_4002558 : CollatzResearch.WordTrace tailWord_4002558 prefixEnd_4002558 2055236101498656207117577 := by
  unfold tailWord_4002558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18248160429177927916091041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97323522288948948885818885 18248160429177927916091041)
  ·
    refine ⟨13686120321883445937068281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18248160429177927916091041 13686120321883445937068281)
    ·
      refine ⟨10264590241412584452801211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13686120321883445937068281 10264590241412584452801211)
      ·
        refine ⟨15396885362118876679201817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264590241412584452801211 15396885362118876679201817)
        ·
          refine ⟨11547664021589157509401363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15396885362118876679201817 11547664021589157509401363)
          ·
            refine ⟨17321496032383736264102045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547664021589157509401363 17321496032383736264102045)
            ·
              refine ⟨6495561012143901099038267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17321496032383736264102045 6495561012143901099038267)
              ·
                refine ⟨9743341518215851648557401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495561012143901099038267 9743341518215851648557401)
                ·
                  refine ⟨7307506138661888736418051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9743341518215851648557401 7307506138661888736418051)
                  ·
                    refine ⟨10961259207992833104627077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307506138661888736418051 10961259207992833104627077)
                    ·
                      refine ⟨2055236101498656207117577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10961259207992833104627077 2055236101498656207117577)
                      ·
                        rfl

theorem cell23_4002558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_4002558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002558 prefixEnd_4002558 := by exact prefixLift 4002558
  have htrace : WordTrace (prefixWord ++ tailWord_4002558) baseStart_4002558 baseEnd_4002558 := by
    simpa [prefixWord, tailWord_4002558, baseEnd_4002558] using wordTrace_append hprefix tailTrace_4002558
  have hstable : (prefixWord ++ tailWord_4002558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002558).length < 2 ^ (prefixWord ++ tailWord_4002558).sum := by decide
  have hdescent : baseEnd_4002558 < baseStart_4002558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002564 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 8]
def baseStart_4002564 : Nat := 118140960795 + 4002564 * 2 ^ 59
def prefixEnd_4002564 : Nat := 4983230072969 + 3 ^ 40 * 4002564 * 2
def baseEnd_4002564 : Nat := 228359909153620353738061

theorem tailTrace_4002564 : CollatzResearch.WordTrace tailWord_4002564 prefixEnd_4002564 228359909153620353738061 := by
  unfold tailWord_4002564
  simp only [CollatzResearch.WordTrace]
  refine ⟨72992751135700843176723373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97323668180934457568964497 72992751135700843176723373)
  ·
    refine ⟨27372281675887816191271265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72992751135700843176723373 27372281675887816191271265)
    ·
      refine ⟨20529211256915862143453449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27372281675887816191271265 20529211256915862143453449)
      ·
        refine ⟨15396908442686896607590087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20529211256915862143453449 15396908442686896607590087)
        ·
          refine ⟨23095362664030344911385131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15396908442686896607590087 23095362664030344911385131)
          ·
            refine ⟨34643043996045517367077697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23095362664030344911385131 34643043996045517367077697)
            ·
              refine ⟨25982282997034138025308273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34643043996045517367077697 25982282997034138025308273)
              ·
                refine ⟨19486712247775603518981205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25982282997034138025308273 19486712247775603518981205)
                ·
                  refine ⟨228359909153620353738061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19486712247775603518981205 228359909153620353738061)
                  ·
                    rfl

theorem cell23_4002564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_4002564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002564 prefixEnd_4002564 := by exact prefixLift 4002564
  have htrace : WordTrace (prefixWord ++ tailWord_4002564) baseStart_4002564 baseEnd_4002564 := by
    simpa [prefixWord, tailWord_4002564, baseEnd_4002564] using wordTrace_append hprefix tailTrace_4002564
  have hstable : (prefixWord ++ tailWord_4002564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002564).length < 2 ^ (prefixWord ++ tailWord_4002564).sum := by decide
  have hdescent : baseEnd_4002564 < baseStart_4002564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002568 : List Nat := [2, 1, 3, 2, 2, 2, 1, 5, 1, 4]
def baseStart_4002568 : Nat := 118140960795 + 4002568 * 2 ^ 59
def prefixEnd_4002568 : Nat := 4983230072969 + 3 ^ 40 * 4002568 * 2
def baseEnd_4002568 : Nat := 685080412101733722664177

theorem tailTrace_4002568 : CollatzResearch.WordTrace tailWord_4002568 prefixEnd_4002568 685080412101733722664177 := by
  unfold tailWord_4002568
  simp only [CollatzResearch.WordTrace]
  refine ⟨72992824081693597518296179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97323765442258130024394905 72992824081693597518296179)
  ·
    refine ⟨109489236122540396277444269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72992824081693597518296179 109489236122540396277444269)
    ·
      refine ⟨41058463545952648604041601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109489236122540396277444269 41058463545952648604041601)
      ·
        refine ⟨30793847659464486453031201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41058463545952648604041601 30793847659464486453031201)
        ·
          refine ⟨23095385744598364839773401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30793847659464486453031201 23095385744598364839773401)
          ·
            refine ⟨17321539308448773629830051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23095385744598364839773401 17321539308448773629830051)
            ·
              refine ⟨25982308962673160444745077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17321539308448773629830051 25982308962673160444745077)
              ·
                refine ⟨2435841465250608791694851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25982308962673160444745077 2435841465250608791694851)
                ·
                  refine ⟨3653762197875913187542277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435841465250608791694851 3653762197875913187542277)
                  ·
                    refine ⟨685080412101733722664177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3653762197875913187542277 685080412101733722664177)
                    ·
                      rfl

theorem cell23_4002568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_4002568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002568 prefixEnd_4002568 := by exact prefixLift 4002568
  have htrace : WordTrace (prefixWord ++ tailWord_4002568) baseStart_4002568 baseEnd_4002568 := by
    simpa [prefixWord, tailWord_4002568, baseEnd_4002568] using wordTrace_append hprefix tailTrace_4002568
  have hstable : (prefixWord ++ tailWord_4002568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002568).length < 2 ^ (prefixWord ++ tailWord_4002568).sum := by decide
  have hdescent : baseEnd_4002568 < baseStart_4002568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 4, 3, 2]
def baseStart_4002601 : Nat := 118140960795 + 4002601 * 2 ^ 59
def prefixEnd_4002601 : Nat := 4983230072969 + 3 ^ 40 * 4002601 * 2
def baseEnd_4002601 : Nat := 2055258181166799538879879

theorem tailTrace_4002601 : CollatzResearch.WordTrace tailWord_4002601 prefixEnd_4002601 2055258181166799538879879 := by
  unfold tailWord_4002601
  simp only [CollatzResearch.WordTrace]
  refine ⟨145986851772267641672543657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97324567848178427781695771 145986851772267641672543657)
  ·
    refine ⟨109490138829200731254407743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145986851772267641672543657 109490138829200731254407743)
    ·
      refine ⟨164235208243801096881611615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109490138829200731254407743 164235208243801096881611615)
      ·
        refine ⟨246352812365701645322417423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164235208243801096881611615 246352812365701645322417423)
        ·
          refine ⟨369529218548552467983626135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246352812365701645322417423 369529218548552467983626135)
          ·
            refine ⟨554293827822828701975439203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369529218548552467983626135 554293827822828701975439203)
            ·
              refine ⟨831440741734243052963158805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554293827822828701975439203 831440741734243052963158805)
              ·
                refine ⟨38973784768792643107648069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 831440741734243052963158805 38973784768792643107648069)
                ·
                  refine ⟨7307584644148620582684013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38973784768792643107648069 7307584644148620582684013)
                  ·
                    refine ⟨2740344241555732718506505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7307584644148620582684013 2740344241555732718506505)
                    ·
                      refine ⟨2055258181166799538879879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740344241555732718506505 2055258181166799538879879)
                      ·
                        rfl

theorem cell23_4002601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 3, 2].length) (baseStart_4002601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002601 prefixEnd_4002601 := by exact prefixLift 4002601
  have htrace : WordTrace (prefixWord ++ tailWord_4002601) baseStart_4002601 baseEnd_4002601 := by
    simpa [prefixWord, tailWord_4002601, baseEnd_4002601] using wordTrace_append hprefix tailTrace_4002601
  have hstable : (prefixWord ++ tailWord_4002601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002601).length < 2 ^ (prefixWord ++ tailWord_4002601).sum := by decide
  have hdescent : baseEnd_4002601 < baseStart_4002601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002611 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 1, 5]
def baseStart_4002611 : Nat := 118140960795 + 4002611 * 2 ^ 59
def prefixEnd_4002611 : Nat := 4983230072969 + 3 ^ 40 * 4002611 * 2
def baseEnd_4002611 : Nat := 685087771991114833251611

theorem tailTrace_4002611 : CollatzResearch.WordTrace tailWord_4002611 prefixEnd_4002611 685087771991114833251611 := by
  unfold tailWord_4002611
  simp only [CollatzResearch.WordTrace]
  refine ⟨145987216502231413380407687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97324811001487608920271791 145987216502231413380407687)
  ·
    refine ⟨218980824753347120070611531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145987216502231413380407687 218980824753347120070611531)
    ·
      refine ⟨328471237130020680105917297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218980824753347120070611531 328471237130020680105917297)
      ·
        refine ⟨246353427847515510079437973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328471237130020680105917297 246353427847515510079437973)
        ·
          refine ⟨11547816930352289534973655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246353427847515510079437973 11547816930352289534973655)
          ·
            refine ⟨17321725395528434302460483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547816930352289534973655 17321725395528434302460483)
            ·
              refine ⟨25982588093292651453690725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17321725395528434302460483 25982588093292651453690725)
              ·
                refine ⟨4871735267492372147567011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25982588093292651453690725 4871735267492372147567011)
                ·
                  refine ⟨7307602901238558221350517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871735267492372147567011 7307602901238558221350517)
                  ·
                    refine ⟨685087771991114833251611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7307602901238558221350517 685087771991114833251611)
                    ·
                      rfl

theorem cell23_4002611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 5].length) (baseStart_4002611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002611 prefixEnd_4002611 := by exact prefixLift 4002611
  have htrace : WordTrace (prefixWord ++ tailWord_4002611) baseStart_4002611 baseEnd_4002611 := by
    simpa [prefixWord, tailWord_4002611, baseEnd_4002611] using wordTrace_append hprefix tailTrace_4002611
  have hstable : (prefixWord ++ tailWord_4002611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002611).length < 2 ^ (prefixWord ++ tailWord_4002611).sum := by decide
  have hdescent : baseEnd_4002611 < baseStart_4002611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002624 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 1, 6]
def baseStart_4002624 : Nat := 118140960795 + 4002624 * 2 ^ 59
def prefixEnd_4002624 : Nat := 4983230072969 + 3 ^ 40 * 4002624 * 2
def baseEnd_4002624 : Nat := 685089997073950982964091

theorem tailTrace_4002624 : CollatzResearch.WordTrace tailWord_4002624 prefixEnd_4002624 685089997073950982964091 := by
  unfold tailWord_4002624
  simp only [CollatzResearch.WordTrace]
  refine ⟨72993845325592158300315463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97325127100789544400420617 72993845325592158300315463)
  ·
    refine ⟨109490767988388237450473195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72993845325592158300315463 109490767988388237450473195)
    ·
      refine ⟨164236151982582356175709793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109490767988388237450473195 164236151982582356175709793)
      ·
        refine ⟨123177113986936767131782345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164236151982582356175709793 123177113986936767131782345)
        ·
          refine ⟨92382835490202575348836759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123177113986936767131782345 92382835490202575348836759)
          ·
            refine ⟨138574253235303863023255139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92382835490202575348836759 138574253235303863023255139)
            ·
              refine ⟨207861379852955794534882709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138574253235303863023255139 207861379852955794534882709)
              ·
                refine ⟨9743502180607302868822627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207861379852955794534882709 9743502180607302868822627)
                ·
                  refine ⟨14615253270910954303233941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9743502180607302868822627 14615253270910954303233941)
                  ·
                    refine ⟨685089997073950982964091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14615253270910954303233941 685089997073950982964091)
                    ·
                      rfl

theorem cell23_4002624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_4002624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002624 prefixEnd_4002624 := by exact prefixLift 4002624
  have htrace : WordTrace (prefixWord ++ tailWord_4002624) baseStart_4002624 baseEnd_4002624 := by
    simpa [prefixWord, tailWord_4002624, baseEnd_4002624] using wordTrace_append hprefix tailTrace_4002624
  have hstable : (prefixWord ++ tailWord_4002624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002624).length < 2 ^ (prefixWord ++ tailWord_4002624).sum := by decide
  have hdescent : baseEnd_4002624 < baseStart_4002624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002642 : List Nat := [3, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_4002642 : Nat := 118140960795 + 4002642 * 2 ^ 59
def prefixEnd_4002642 : Nat := 4983230072969 + 3 ^ 40 * 4002642 * 2
def baseEnd_4002642 : Nat := 2055279233873633878467191

theorem tailTrace_4002642 : CollatzResearch.WordTrace tailWord_4002642 prefixEnd_4002642 2055279233873633878467191 := by
  unfold tailWord_4002642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36497086791279776418696545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97325564776746070449857453 36497086791279776418696545)
  ·
    refine ⟨27372815093459832314022409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36497086791279776418696545 27372815093459832314022409)
    ·
      refine ⟨20529611320094874235516807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27372815093459832314022409 20529611320094874235516807)
      ·
        refine ⟨30794416980142311353275211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20529611320094874235516807 30794416980142311353275211)
        ·
          refine ⟨46191625470213467029912817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30794416980142311353275211 46191625470213467029912817)
          ·
            refine ⟨34643719102660100272434613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46191625470213467029912817 34643719102660100272434613)
            ·
              refine ⟨3247848665874384400540745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34643719102660100272434613 3247848665874384400540745)
              ·
                refine ⟨2435886499405788300405559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3247848665874384400540745 2435886499405788300405559)
                ·
                  refine ⟨3653829749108682450608339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435886499405788300405559 3653829749108682450608339)
                  ·
                    refine ⟨5480744623663023675912509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3653829749108682450608339 5480744623663023675912509)
                    ·
                      refine ⟨2055279233873633878467191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5480744623663023675912509 2055279233873633878467191)
                      ·
                        rfl

theorem cell23_4002642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_4002642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002642 prefixEnd_4002642 := by exact prefixLift 4002642
  have htrace : WordTrace (prefixWord ++ tailWord_4002642) baseStart_4002642 baseEnd_4002642 := by
    simpa [prefixWord, tailWord_4002642, baseEnd_4002642] using wordTrace_append hprefix tailTrace_4002642
  have hstable : (prefixWord ++ tailWord_4002642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002642).length < 2 ^ (prefixWord ++ tailWord_4002642).sum := by decide
  have hdescent : baseEnd_4002642 < baseStart_4002642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002678 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4002678 : Nat := 118140960795 + 4002678 * 2 ^ 59
def prefixEnd_4002678 : Nat := 4983230072969 + 3 ^ 40 * 4002678 * 2
def baseEnd_4002678 : Nat := 2055297719177195737617025

theorem tailTrace_4002678 : CollatzResearch.WordTrace tailWord_4002678 prefixEnd_4002678 2055297719177195737617025 := by
  unfold tailWord_4002678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124353762061792738943543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97326440128659122548731125 9124353762061792738943543)
  ·
    refine ⟨13686530643092689108415315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9124353762061792738943543 13686530643092689108415315)
    ·
      refine ⟨20529795964639033662622973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13686530643092689108415315 20529795964639033662622973)
      ·
        refine ⟨7698673486739637623483615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20529795964639033662622973 7698673486739637623483615)
        ·
          refine ⟨11548010230109456435225423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7698673486739637623483615 11548010230109456435225423)
          ·
            refine ⟨17322015345164184652838135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548010230109456435225423 17322015345164184652838135)
            ·
              refine ⟨25983023017746276979257203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17322015345164184652838135 25983023017746276979257203)
              ·
                refine ⟨38974534526619415468885805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25983023017746276979257203 38974534526619415468885805)
                ·
                  refine ⟨14615450447482280800832177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38974534526619415468885805 14615450447482280800832177)
                  ·
                    refine ⟨10961587835611710600624133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14615450447482280800832177 10961587835611710600624133)
                    ·
                      refine ⟨2055297719177195737617025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10961587835611710600624133 2055297719177195737617025)
                      ·
                        rfl

theorem cell23_4002678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4002678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002678 prefixEnd_4002678 := by exact prefixLift 4002678
  have htrace : WordTrace (prefixWord ++ tailWord_4002678) baseStart_4002678 baseEnd_4002678 := by
    simpa [prefixWord, tailWord_4002678, baseEnd_4002678] using wordTrace_append hprefix tailTrace_4002678
  have hstable : (prefixWord ++ tailWord_4002678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002678).length < 2 ^ (prefixWord ++ tailWord_4002678).sum := by decide
  have hdescent : baseEnd_4002678 < baseStart_4002678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002681 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 3]
def baseStart_4002681 : Nat := 118140960795 + 4002681 * 2 ^ 59
def prefixEnd_4002681 : Nat := 4983230072969 + 3 ^ 40 * 4002681 * 2
def baseEnd_4002681 : Nat := 2055299259619159225879511

theorem tailTrace_4002681 : CollatzResearch.WordTrace tailWord_4002681 prefixEnd_4002681 2055299259619159225879511 := by
  unfold tailWord_4002681
  simp only [CollatzResearch.WordTrace]
  refine ⟨145989769611977815335455897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97326513074651876890303931 145989769611977815335455897)
  ·
    refine ⟨109492327208983361501591923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145989769611977815335455897 109492327208983361501591923)
    ·
      refine ⟨164238490813475042252387885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109492327208983361501591923 164238490813475042252387885)
      ·
        refine ⟨61589434055053140844645457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164238490813475042252387885 61589434055053140844645457)
        ·
          refine ⟨46192075541289855633484093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61589434055053140844645457 46192075541289855633484093)
          ·
            refine ⟨17322028327983695862556535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46192075541289855633484093 17322028327983695862556535)
            ·
              refine ⟨25983042491975543793834803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17322028327983695862556535 25983042491975543793834803)
              ·
                refine ⟨38974563737963315690752205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25983042491975543793834803 38974563737963315690752205)
                ·
                  refine ⟨14615461401736243384032077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38974563737963315690752205 14615461401736243384032077)
                  ·
                    refine ⟨5480798025651091269012029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14615461401736243384032077 5480798025651091269012029)
                    ·
                      refine ⟨2055299259619159225879511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5480798025651091269012029 2055299259619159225879511)
                      ·
                        rfl

theorem cell23_4002681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_4002681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002681 prefixEnd_4002681 := by exact prefixLift 4002681
  have htrace : WordTrace (prefixWord ++ tailWord_4002681) baseStart_4002681 baseEnd_4002681 := by
    simpa [prefixWord, tailWord_4002681, baseEnd_4002681] using wordTrace_append hprefix tailTrace_4002681
  have hstable : (prefixWord ++ tailWord_4002681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002681).length < 2 ^ (prefixWord ++ tailWord_4002681).sum := by decide
  have hdescent : baseEnd_4002681 < baseStart_4002681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002684 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_4002684 : Nat := 118140960795 + 4002684 * 2 ^ 59
def prefixEnd_4002684 : Nat := 4983230072969 + 3 ^ 40 * 4002684 * 2
def baseEnd_4002684 : Nat := 685100266687040904713999

theorem tailTrace_4002684 : CollatzResearch.WordTrace tailWord_4002684 prefixEnd_4002684 685100266687040904713999 := by
  unfold tailWord_4002684
  simp only [CollatzResearch.WordTrace]
  refine ⟨72994939515483473423907553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97326586020644631231876737 72994939515483473423907553)
  ·
    refine ⟨54746204636612605067930665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72994939515483473423907553 54746204636612605067930665)
    ·
      refine ⟨41059653477459453800947999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54746204636612605067930665 41059653477459453800947999)
      ·
        refine ⟨61589480216189180701421999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41059653477459453800947999 61589480216189180701421999)
        ·
          refine ⟨92384220324283771052132999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61589480216189180701421999 92384220324283771052132999)
          ·
            refine ⟨138576330486425656578199499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92384220324283771052132999 138576330486425656578199499)
            ·
              refine ⟨207864495729638484867299249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138576330486425656578199499 207864495729638484867299249)
              ·
                refine ⟨155898371797228863650474437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207864495729638484867299249 155898371797228863650474437)
                ·
                  refine ⟨29230944711980411934463957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155898371797228863650474437 29230944711980411934463957)
                  ·
                    refine ⟨685100266687040904713999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29230944711980411934463957 685100266687040904713999)
                    ·
                      rfl

theorem cell23_4002684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_4002684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002684 prefixEnd_4002684 := by exact prefixLift 4002684
  have htrace : WordTrace (prefixWord ++ tailWord_4002684) baseStart_4002684 baseEnd_4002684 := by
    simpa [prefixWord, tailWord_4002684, baseEnd_4002684] using wordTrace_append hprefix tailTrace_4002684
  have hstable : (prefixWord ++ tailWord_4002684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002684).length < 2 ^ (prefixWord ++ tailWord_4002684).sum := by decide
  have hdescent : baseEnd_4002684 < baseStart_4002684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002741 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4002741 : Nat := 118140960795 + 4002741 * 2 ^ 59
def prefixEnd_4002741 : Nat := 4983230072969 + 3 ^ 40 * 4002741 * 2
def baseEnd_4002741 : Nat := 2055330068458428991129235

theorem tailTrace_4002741 : CollatzResearch.WordTrace tailWord_4002741 prefixEnd_4002741 2055330068458428991129235 := by
  unfold tailWord_4002741
  simp only [CollatzResearch.WordTrace]
  refine ⟨145991957991760445582640077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97327971994506963721760051 145991957991760445582640077)
  ·
    refine ⟨54746984246910167093490029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145991957991760445582640077 54746984246910167093490029)
    ·
      refine ⟨20530119092591312660058761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54746984246910167093490029 20530119092591312660058761)
      ·
        refine ⟨15397589319443484495044071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20530119092591312660058761 15397589319443484495044071)
        ·
          refine ⟨23096383979165226742566107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15397589319443484495044071 23096383979165226742566107)
          ·
            refine ⟨34644575968747840113849161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23096383979165226742566107 34644575968747840113849161)
            ·
              refine ⟨25983431976560880085386871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34644575968747840113849161 25983431976560880085386871)
              ·
                refine ⟨38975147964841320128080307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25983431976560880085386871 38975147964841320128080307)
                ·
                  refine ⟨58462721947261980192120461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38975147964841320128080307 58462721947261980192120461)
                  ·
                    refine ⟨21923520730223242572045173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58462721947261980192120461 21923520730223242572045173)
                    ·
                      refine ⟨2055330068458428991129235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21923520730223242572045173 2055330068458428991129235)
                      ·
                        rfl

theorem cell23_4002741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4002741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002741 prefixEnd_4002741 := by exact prefixLift 4002741
  have htrace : WordTrace (prefixWord ++ tailWord_4002741) baseStart_4002741 baseEnd_4002741 := by
    simpa [prefixWord, tailWord_4002741, baseEnd_4002741] using wordTrace_append hprefix tailTrace_4002741
  have hstable : (prefixWord ++ tailWord_4002741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002741).length < 2 ^ (prefixWord ++ tailWord_4002741).sum := by decide
  have hdescent : baseEnd_4002741 < baseStart_4002741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002749 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_4002749 : Nat := 118140960795 + 4002749 * 2 ^ 59
def prefixEnd_4002749 : Nat := 4983230072969 + 3 ^ 40 * 4002749 * 2
def baseEnd_4002749 : Nat := 2055334176303664959829199

theorem tailTrace_4002749 : CollatzResearch.WordTrace tailWord_4002749 prefixEnd_4002749 2055334176303664959829199 := by
  unfold tailWord_4002749
  simp only [CollatzResearch.WordTrace]
  refine ⟨145992249775731462948931301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97328166517154308632620867 145992249775731462948931301)
  ·
    refine ⟨27373546832949649302924619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145992249775731462948931301 27373546832949649302924619)
    ·
      refine ⟨41060320249424473954386929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27373546832949649302924619 41060320249424473954386929)
      ·
        refine ⟨30795240187068355465790197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41060320249424473954386929 30795240187068355465790197)
        ·
          refine ⟨2887053767537658324917831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30795240187068355465790197 2887053767537658324917831)
          ·
            refine ⟨4330580651306487487376747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887053767537658324917831 4330580651306487487376747)
            ·
              refine ⟨6495870976959731231065121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330580651306487487376747 6495870976959731231065121)
              ·
                refine ⟨4871903232719798423298841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6495870976959731231065121 4871903232719798423298841)
                ·
                  refine ⟨3653927424539848817474131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871903232719798423298841 3653927424539848817474131)
                  ·
                    refine ⟨5480891136809773226211197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3653927424539848817474131 5480891136809773226211197)
                    ·
                      refine ⟨2055334176303664959829199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5480891136809773226211197 2055334176303664959829199)
                      ·
                        rfl

theorem cell23_4002749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_4002749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002749 prefixEnd_4002749 := by exact prefixLift 4002749
  have htrace : WordTrace (prefixWord ++ tailWord_4002749) baseStart_4002749 baseEnd_4002749 := by
    simpa [prefixWord, tailWord_4002749, baseEnd_4002749] using wordTrace_append hprefix tailTrace_4002749
  have hstable : (prefixWord ++ tailWord_4002749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002749).length < 2 ^ (prefixWord ++ tailWord_4002749).sum := by decide
  have hdescent : baseEnd_4002749 < baseStart_4002749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002772 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4002772 : Nat := 118140960795 + 4002772 * 2 ^ 59
def prefixEnd_4002772 : Nat := 4983230072969 + 3 ^ 40 * 4002772 * 2
def baseEnd_4002772 : Nat := 2055345986358718369841593

theorem tailTrace_4002772 : CollatzResearch.WordTrace tailWord_4002772 prefixEnd_4002772 2055345986358718369841593 := by
  unfold tailWord_4002772
  simp only [CollatzResearch.WordTrace]
  refine ⟨72996544327324068938509285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97328725769765425251345713 72996544327324068938509285)
  ·
    refine ⟨13686852061373262925970491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72996544327324068938509285 13686852061373262925970491)
    ·
      refine ⟨20530278092059894388955737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13686852061373262925970491 20530278092059894388955737)
      ·
        refine ⟨15397708569044920791716803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20530278092059894388955737 15397708569044920791716803)
        ·
          refine ⟨23096562853567381187575205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15397708569044920791716803 23096562853567381187575205)
          ·
            refine ⟨4330605535043883972670351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23096562853567381187575205 4330605535043883972670351)
            ·
              refine ⟨6495908302565825959005527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330605535043883972670351 6495908302565825959005527)
              ·
                refine ⟨9743862453848738938508291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495908302565825959005527 9743862453848738938508291)
                ·
                  refine ⟨14615793680773108407762437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9743862453848738938508291 14615793680773108407762437)
                  ·
                    refine ⟨2740461315144957826455457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14615793680773108407762437 2740461315144957826455457)
                    ·
                      refine ⟨2055345986358718369841593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740461315144957826455457 2055345986358718369841593)
                      ·
                        rfl

theorem cell23_4002772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4002772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002772 prefixEnd_4002772 := by exact prefixLift 4002772
  have htrace : WordTrace (prefixWord ++ tailWord_4002772) baseStart_4002772 baseEnd_4002772 := by
    simpa [prefixWord, tailWord_4002772, baseEnd_4002772] using wordTrace_append hprefix tailTrace_4002772
  have hstable : (prefixWord ++ tailWord_4002772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002772).length < 2 ^ (prefixWord ++ tailWord_4002772).sum := by decide
  have hdescent : baseEnd_4002772 < baseStart_4002772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002841 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_4002841 : Nat := 118140960795 + 4002841 * 2 ^ 59
def prefixEnd_4002841 : Nat := 4983230072969 + 3 ^ 40 * 4002841 * 2
def baseEnd_4002841 : Nat := 2055381416523878599878775

theorem tailTrace_4002841 : CollatzResearch.WordTrace tailWord_4002841 prefixEnd_4002841 2055381416523878599878775 := by
  unfold tailWord_4002841
  simp only [CollatzResearch.WordTrace]
  refine ⟨145995605291398162661280377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97330403527598775107520251 145995605291398162661280377)
  ·
    refine ⟨109496703968548621995960283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145995605291398162661280377 109496703968548621995960283)
    ·
      refine ⟨164245055952822932993940425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109496703968548621995960283 164245055952822932993940425)
      ·
        refine ⟨123183791964617199745455319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164245055952822932993940425 123183791964617199745455319)
        ·
          refine ⟨184775687946925799618182979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123183791964617199745455319 184775687946925799618182979)
          ·
            refine ⟨277163531920388699427274469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184775687946925799618182979 277163531920388699427274469)
            ·
              refine ⟨51968162235072881142613963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277163531920388699427274469 51968162235072881142613963)
              ·
                refine ⟨77952243352609321713920945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51968162235072881142613963 77952243352609321713920945)
                ·
                  refine ⟨58464182514456991285440709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77952243352609321713920945 58464182514456991285440709)
                  ·
                    refine ⟨10962034221460685866020133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58464182514456991285440709 10962034221460685866020133)
                    ·
                      refine ⟨2055381416523878599878775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10962034221460685866020133 2055381416523878599878775)
                      ·
                        rfl

theorem cell23_4002841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_4002841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002841 prefixEnd_4002841 := by exact prefixLift 4002841
  have htrace : WordTrace (prefixWord ++ tailWord_4002841) baseStart_4002841 baseEnd_4002841 := by
    simpa [prefixWord, tailWord_4002841, baseEnd_4002841] using wordTrace_append hprefix tailTrace_4002841
  have hstable : (prefixWord ++ tailWord_4002841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002841).length < 2 ^ (prefixWord ++ tailWord_4002841).sum := by decide
  have hdescent : baseEnd_4002841 < baseStart_4002841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002871 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_4002871 : Nat := 118140960795 + 4002871 * 2 ^ 59
def prefixEnd_4002871 : Nat := 4983230072969 + 3 ^ 40 * 4002871 * 2
def baseEnd_4002871 : Nat := 2055396820943513482503637

theorem tailTrace_4002871 : CollatzResearch.WordTrace tailWord_4002871 prefixEnd_4002871 2055396820943513482503637 := by
  unfold tailWord_4002871
  simp only [CollatzResearch.WordTrace]
  refine ⟨145996699481289477784872467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97331132987526318523248311 145996699481289477784872467)
  ·
    refine ⟨218995049221934216677308701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145996699481289477784872467 218995049221934216677308701)
    ·
      refine ⟨82123143458225331253990763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218995049221934216677308701 82123143458225331253990763)
      ·
        refine ⟨123184715187337996880986145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82123143458225331253990763 123184715187337996880986145)
        ·
          refine ⟨92388536390503497660739609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123184715187337996880986145 92388536390503497660739609)
          ·
            refine ⟨69291402292877623245554707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92388536390503497660739609 69291402292877623245554707)
            ·
              refine ⟨103937103439316434868332061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69291402292877623245554707 103937103439316434868332061)
              ·
                refine ⟨38976413789743663075624523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103937103439316434868332061 38976413789743663075624523)
                ·
                  refine ⟨58464620684615494613436785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38976413789743663075624523 58464620684615494613436785)
                  ·
                    refine ⟨43848465513461620960077589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58464620684615494613436785 43848465513461620960077589)
                    ·
                      refine ⟨2055396820943513482503637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43848465513461620960077589 2055396820943513482503637)
                      ·
                        rfl

theorem cell23_4002871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_4002871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002871 prefixEnd_4002871 := by exact prefixLift 4002871
  have htrace : WordTrace (prefixWord ++ tailWord_4002871) baseStart_4002871 baseEnd_4002871 := by
    simpa [prefixWord, tailWord_4002871, baseEnd_4002871] using wordTrace_append hprefix tailTrace_4002871
  have hstable : (prefixWord ++ tailWord_4002871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002871).length < 2 ^ (prefixWord ++ tailWord_4002871).sum := by decide
  have hdescent : baseEnd_4002871 < baseStart_4002871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002872 : List Nat := [2, 1, 2, 1, 5, 2, 1, 4, 1, 4]
def baseStart_4002872 : Nat := 118140960795 + 4002872 * 2 ^ 59
def prefixEnd_4002872 : Nat := 4983230072969 + 3 ^ 40 * 4002872 * 2
def baseEnd_4002872 : Nat := 685132444808055992863711

theorem tailTrace_4002872 : CollatzResearch.WordTrace tailWord_4002872 prefixEnd_4002872 685132444808055992863711 := by
  unfold tailWord_4002872
  simp only [CollatzResearch.WordTrace]
  refine ⟨72998367977142927477829435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97331157302857236637105913 72998367977142927477829435)
  ·
    refine ⟨109497551965714391216744153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72998367977142927477829435 109497551965714391216744153)
    ·
      refine ⟨82123163974285793412558115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109497551965714391216744153 82123163974285793412558115)
      ·
        refine ⟨123184745961428690118837173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82123163974285793412558115 123184745961428690118837173)
        ·
          refine ⟨11548569933883939698640985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123184745961428690118837173 11548569933883939698640985)
          ·
            refine ⟨8661427450412954773980739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11548569933883939698640985 8661427450412954773980739)
            ·
              refine ⟨12992141175619432160971109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8661427450412954773980739 12992141175619432160971109)
              ·
                refine ⟨2436026470428643530182083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12992141175619432160971109 2436026470428643530182083)
                ·
                  refine ⟨3654039705642965295273125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436026470428643530182083 3654039705642965295273125)
                  ·
                    refine ⟨685132444808055992863711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654039705642965295273125 685132444808055992863711)
                    ·
                      rfl

theorem cell23_4002872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_4002872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002872 prefixEnd_4002872 := by exact prefixLift 4002872
  have htrace : WordTrace (prefixWord ++ tailWord_4002872) baseStart_4002872 baseEnd_4002872 := by
    simpa [prefixWord, tailWord_4002872, baseEnd_4002872] using wordTrace_append hprefix tailTrace_4002872
  have hstable : (prefixWord ++ tailWord_4002872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002872).length < 2 ^ (prefixWord ++ tailWord_4002872).sum := by decide
  have hdescent : baseEnd_4002872 < baseStart_4002872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002905 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 2, 3, 2]
def baseStart_4002905 : Nat := 118140960795 + 4002905 * 2 ^ 59
def prefixEnd_4002905 : Nat := 4983230072969 + 3 ^ 40 * 4002905 * 2
def baseEnd_4002905 : Nat := 2055414279285766349478481

theorem tailTrace_4002905 : CollatzResearch.WordTrace tailWord_4002905 prefixEnd_4002905 2055414279285766349478481 := by
  unfold tailWord_4002905
  simp only [CollatzResearch.WordTrace]
  refine ⟨145997939563166301591610169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97331959708777534394406779 145997939563166301591610169)
  ·
    refine ⟨109498454672374726193707627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145997939563166301591610169 109498454672374726193707627)
    ·
      refine ⟨164247682008562089290561441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109498454672374726193707627 164247682008562089290561441)
      ·
        refine ⟨123185761506421566967921081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164247682008562089290561441 123185761506421566967921081)
        ·
          refine ⟨92389321129816175225940811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123185761506421566967921081 92389321129816175225940811)
          ·
            refine ⟨138583981694724262838911217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92389321129816175225940811 138583981694724262838911217)
            ·
              refine ⟨103937986271043197129183413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138583981694724262838911217 103937986271043197129183413)
              ·
                refine ⟨9744186212910299730860945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103937986271043197129183413 9744186212910299730860945)
                ·
                  refine ⟨7308139659682724798145709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9744186212910299730860945 7308139659682724798145709)
                  ·
                    refine ⟨2740552372381021799304641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7308139659682724798145709 2740552372381021799304641)
                    ·
                      refine ⟨2055414279285766349478481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740552372381021799304641 2055414279285766349478481)
                      ·
                        rfl

theorem cell23_4002905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_4002905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002905 prefixEnd_4002905 := by exact prefixLift 4002905
  have htrace : WordTrace (prefixWord ++ tailWord_4002905) baseStart_4002905 baseEnd_4002905 := by
    simpa [prefixWord, tailWord_4002905, baseEnd_4002905] using wordTrace_append hprefix tailTrace_4002905
  have hstable : (prefixWord ++ tailWord_4002905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002905).length < 2 ^ (prefixWord ++ tailWord_4002905).sum := by decide
  have hdescent : baseEnd_4002905 < baseStart_4002905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002945 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 1, 6]
def baseStart_4002945 : Nat := 118140960795 + 4002945 * 2 ^ 59
def prefixEnd_4002945 : Nat := 4983230072969 + 3 ^ 40 * 4002945 * 2
def baseEnd_4002945 : Nat := 685144939503982064326099

theorem tailTrace_4002945 : CollatzResearch.WordTrace tailWord_4002945 prefixEnd_4002945 685144939503982064326099 := by
  unfold tailWord_4002945
  simp only [CollatzResearch.WordTrace]
  refine ⟨145999398483021388423066289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97332932322014258948710859 145999398483021388423066289)
  ·
    refine ⟨109499548862266041317299717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145999398483021388423066289 109499548862266041317299717)
    ·
      refine ⟨20531165411674882746993697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109499548862266041317299717 20531165411674882746993697)
      ·
        refine ⟨15398374058756162060245273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20531165411674882746993697 15398374058756162060245273)
        ·
          refine ⟨11548780544067121545183955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15398374058756162060245273 11548780544067121545183955)
          ·
            refine ⟨17323170816100682317775933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548780544067121545183955 17323170816100682317775933)
            ·
              refine ⟨6496189056037755869165975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17323170816100682317775933 6496189056037755869165975)
              ·
                refine ⟨9744283584056633803748963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496189056037755869165975 9744283584056633803748963)
                ·
                  refine ⟨14616425376084950705623445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9744283584056633803748963 14616425376084950705623445)
                  ·
                    refine ⟨685144939503982064326099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14616425376084950705623445 685144939503982064326099)
                    ·
                      rfl

theorem cell23_4002945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_4002945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002945 prefixEnd_4002945 := by exact prefixLift 4002945
  have htrace : WordTrace (prefixWord ++ tailWord_4002945) baseStart_4002945 baseEnd_4002945 := by
    simpa [prefixWord, tailWord_4002945, baseEnd_4002945] using wordTrace_append hprefix tailTrace_4002945
  have hstable : (prefixWord ++ tailWord_4002945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002945).length < 2 ^ (prefixWord ++ tailWord_4002945).sum := by decide
  have hdescent : baseEnd_4002945 < baseStart_4002945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002972 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_4002972 : Nat := 118140960795 + 4002972 * 2 ^ 59
def prefixEnd_4002972 : Nat := 4983230072969 + 3 ^ 40 * 4002972 * 2
def baseEnd_4002972 : Nat := 2055448682489617587340673

theorem tailTrace_4002972 : CollatzResearch.WordTrace tailWord_4002972 prefixEnd_4002972 2055448682489617587340673 := by
  unfold tailWord_4002972
  simp only [CollatzResearch.WordTrace]
  refine ⟨73000191626961786017149585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97333588835949048022866113 73000191626961786017149585)
  ·
    refine ⟨54750143720221339512862189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73000191626961786017149585 54750143720221339512862189)
    ·
      refine ⟨20531303895083002317323321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54750143720221339512862189 20531303895083002317323321)
      ·
        refine ⟨15398477921312251737992491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20531303895083002317323321 15398477921312251737992491)
        ·
          refine ⟨23097716881968377606988737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15398477921312251737992491 23097716881968377606988737)
          ·
            refine ⟨17323287661476283205241553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23097716881968377606988737 17323287661476283205241553)
            ·
              refine ⟨12992465746107212403931165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17323287661476283205241553 12992465746107212403931165)
              ·
                refine ⟨4872174654790204651474187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12992465746107212403931165 4872174654790204651474187)
                ·
                  refine ⟨7308261982185306977211281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872174654790204651474187 7308261982185306977211281)
                  ·
                    refine ⟨5481196486638980232908461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7308261982185306977211281 5481196486638980232908461)
                    ·
                      refine ⟨2055448682489617587340673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5481196486638980232908461 2055448682489617587340673)
                      ·
                        rfl

theorem cell23_4002972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_4002972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002972 prefixEnd_4002972 := by exact prefixLift 4002972
  have htrace : WordTrace (prefixWord ++ tailWord_4002972) baseStart_4002972 baseEnd_4002972 := by
    simpa [prefixWord, tailWord_4002972, baseEnd_4002972] using wordTrace_append hprefix tailTrace_4002972
  have hstable : (prefixWord ++ tailWord_4002972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002972).length < 2 ^ (prefixWord ++ tailWord_4002972).sum := by decide
  have hdescent : baseEnd_4002972 < baseStart_4002972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002975 : List Nat := [1, 1, 2, 6, 2, 2, 9]
def baseStart_4002975 : Nat := 118140960795 + 4002975 * 2 ^ 59
def prefixEnd_4002975 : Nat := 4983230072969 + 3 ^ 40 * 4002975 * 2
def baseEnd_4002975 : Nat := 25375928678167667600039

theorem tailTrace_4002975 : CollatzResearch.WordTrace tailWord_4002975 prefixEnd_4002975 25375928678167667600039 := by
  unfold tailWord_4002975
  simp only [CollatzResearch.WordTrace]
  refine ⟨146000492672912703546658379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97333661781941802364438919 146000492672912703546658379)
  ·
    refine ⟨219000739009369055319987569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146000492672912703546658379 219000739009369055319987569)
    ·
      refine ⟨164250554257026791489990677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219000739009369055319987569 164250554257026791489990677)
      ·
        refine ⟨7699244730798130851093313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164250554257026791489990677 7699244730798130851093313)
        ·
          refine ⟨5774433548098598138319985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7699244730798130851093313 5774433548098598138319985)
          ·
            refine ⟨4330825161073948603739989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5774433548098598138319985 4330825161073948603739989)
            ·
              refine ⟨25375928678167667600039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4330825161073948603739989 25375928678167667600039)
              ·
                rfl

theorem cell23_4002975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 9].length) (baseStart_4002975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002975 prefixEnd_4002975 := by exact prefixLift 4002975
  have htrace : WordTrace (prefixWord ++ tailWord_4002975) baseStart_4002975 baseEnd_4002975 := by
    simpa [prefixWord, tailWord_4002975, baseEnd_4002975] using wordTrace_append hprefix tailTrace_4002975
  have hstable : (prefixWord ++ tailWord_4002975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002975).length < 2 ^ (prefixWord ++ tailWord_4002975).sum := by decide
  have hdescent : baseEnd_4002975 < baseStart_4002975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4002986 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4002986 : Nat := 118140960795 + 4002986 * 2 ^ 59
def prefixEnd_4002986 : Nat := 4983230072969 + 3 ^ 40 * 4002986 * 2
def baseEnd_4002986 : Nat := 2055455871218780532565609

theorem tailTrace_4002986 : CollatzResearch.WordTrace tailWord_4002986 prefixEnd_4002986 2055455871218780532565609 := by
  unfold tailWord_4002986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36500223468968213106327203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97333929250581901616872541 36500223468968213106327203)
  ·
    refine ⟨54750335203452319659490805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36500223468968213106327203 54750335203452319659490805)
    ·
      refine ⟨5132843925323654968077263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54750335203452319659490805 5132843925323654968077263)
      ·
        refine ⟨7699265887985482452115895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132843925323654968077263 7699265887985482452115895)
        ·
          refine ⟨11548898831978223678173843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7699265887985482452115895 11548898831978223678173843)
          ·
            refine ⟨17323348247967335517260765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548898831978223678173843 17323348247967335517260765)
            ·
              refine ⟨6496255592987750818972787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17323348247967335517260765 6496255592987750818972787)
              ·
                refine ⟨9744383389481626228459181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496255592987750818972787 9744383389481626228459181)
                ·
                  refine ⟨3654143771055609835672193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9744383389481626228459181 3654143771055609835672193)
                  ·
                    refine ⟨2740607828291707376754145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3654143771055609835672193 2740607828291707376754145)
                    ·
                      refine ⟨2055455871218780532565609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740607828291707376754145 2055455871218780532565609)
                      ·
                        rfl

theorem cell23_4002986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4002986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4002986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4002986 prefixEnd_4002986 := by exact prefixLift 4002986
  have htrace : WordTrace (prefixWord ++ tailWord_4002986) baseStart_4002986 baseEnd_4002986 := by
    simpa [prefixWord, tailWord_4002986, baseEnd_4002986] using wordTrace_append hprefix tailTrace_4002986
  have hstable : (prefixWord ++ tailWord_4002986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4002986).length < 2 ^ (prefixWord ++ tailWord_4002986).sum := by decide
  have hdescent : baseEnd_4002986 < baseStart_4002986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4002986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003037 : List Nat := [1, 4, 3, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_4003037 : Nat := 118140960795 + 4003037 * 2 ^ 59
def prefixEnd_4003037 : Nat := 4983230072969 + 3 ^ 40 * 4003037 * 2
def baseEnd_4003037 : Nat := 2055482058732159833027875

theorem tailTrace_4003037 : CollatzResearch.WordTrace tailWord_4003037 prefixEnd_4003037 2055482058732159833027875 := by
  unfold tailWord_4003037
  simp only [CollatzResearch.WordTrace]
  refine ⟨146002753998688088135415365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97335169332458725423610243 146002753998688088135415365)
  ·
    refine ⟨27375516374754016525390381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146002753998688088135415365 27375516374754016525390381)
    ·
      refine ⟨10265818640532756197021393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27375516374754016525390381 10265818640532756197021393)
      ·
        refine ⟨7699363980399567147766045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10265818640532756197021393 7699363980399567147766045)
        ·
          refine ⟨2887261492649837680412267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7699363980399567147766045 2887261492649837680412267)
          ·
            refine ⟨4330892238974756520618401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887261492649837680412267 4330892238974756520618401)
            ·
              refine ⟨3248169179231067390463801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330892238974756520618401 3248169179231067390463801)
              ·
                refine ⟨2436126884423300542847851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3248169179231067390463801 2436126884423300542847851)
                ·
                  refine ⟨3654190326634950814271777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436126884423300542847851 3654190326634950814271777)
                  ·
                    refine ⟨2740642744976213110703833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3654190326634950814271777 2740642744976213110703833)
                    ·
                      refine ⟨2055482058732159833027875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740642744976213110703833 2055482058732159833027875)
                      ·
                        rfl

theorem cell23_4003037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_4003037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003037 prefixEnd_4003037 := by exact prefixLift 4003037
  have htrace : WordTrace (prefixWord ++ tailWord_4003037) baseStart_4003037 baseEnd_4003037 := by
    simpa [prefixWord, tailWord_4003037, baseEnd_4003037] using wordTrace_append hprefix tailTrace_4003037
  have hstable : (prefixWord ++ tailWord_4003037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003037).length < 2 ^ (prefixWord ++ tailWord_4003037).sum := by decide
  have hdescent : baseEnd_4003037 < baseStart_4003037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003059 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 2, 2, 2]
def baseStart_4003059 : Nat := 118140960795 + 4003059 * 2 ^ 59
def prefixEnd_4003059 : Nat := 4983230072969 + 3 ^ 40 * 4003059 * 2
def baseEnd_4003059 : Nat := 2055493355306558746952773

theorem tailTrace_4003059 : CollatzResearch.WordTrace tailWord_4003059 prefixEnd_4003059 2055493355306558746952773 := by
  unfold tailWord_4003059
  simp only [CollatzResearch.WordTrace]
  refine ⟨146003556404608385892716231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97335704269738923928477487 146003556404608385892716231)
  ·
    refine ⟨219005334606912578839074347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146003556404608385892716231 219005334606912578839074347)
    ·
      refine ⟨328508001910368868258611521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219005334606912578839074347 328508001910368868258611521)
      ·
        refine ⟨246381001432776651193958641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328508001910368868258611521 246381001432776651193958641)
        ·
          refine ⟨184785751074582488395468981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246381001432776651193958641 184785751074582488395468981)
          ·
            refine ⟨17323664163242108287075217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184785751074582488395468981 17323664163242108287075217)
            ·
              refine ⟨12992748122431581215306413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17323664163242108287075217 12992748122431581215306413)
              ·
                refine ⟨4872280545911842955739905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12992748122431581215306413 4872280545911842955739905)
                ·
                  refine ⟨3654210409433882216804929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872280545911842955739905 3654210409433882216804929)
                  ·
                    refine ⟨2740657807075411662603697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3654210409433882216804929 2740657807075411662603697)
                    ·
                      refine ⟨2055493355306558746952773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740657807075411662603697 2055493355306558746952773)
                      ·
                        rfl

theorem cell23_4003059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 2, 2].length) (baseStart_4003059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003059 prefixEnd_4003059 := by exact prefixLift 4003059
  have htrace : WordTrace (prefixWord ++ tailWord_4003059) baseStart_4003059 baseEnd_4003059 := by
    simpa [prefixWord, tailWord_4003059, baseEnd_4003059] using wordTrace_append hprefix tailTrace_4003059
  have hstable : (prefixWord ++ tailWord_4003059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003059).length < 2 ^ (prefixWord ++ tailWord_4003059).sum := by decide
  have hdescent : baseEnd_4003059 < baseStart_4003059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003095 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 4, 5]
def baseStart_4003095 : Nat := 118140960795 + 4003095 * 2 ^ 59
def prefixEnd_4003095 : Nat := 4983230072969 + 3 ^ 40 * 4003095 * 2
def baseEnd_4003095 : Nat := 685170613536706868700869

theorem tailTrace_4003095 : CollatzResearch.WordTrace tailWord_4003095 prefixEnd_4003095 685170613536706868700869 := by
  unfold tailWord_4003095
  simp only [CollatzResearch.WordTrace]
  refine ⟨146004869432477964041026739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97336579621651976027351159 146004869432477964041026739)
  ·
    refine ⟨219007304148716946061540109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146004869432477964041026739 219007304148716946061540109)
    ·
      refine ⟨82127739055768854773077541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219007304148716946061540109 82127739055768854773077541)
      ·
        refine ⟨15398951072956660269952039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82127739055768854773077541 15398951072956660269952039)
        ·
          refine ⟨23098426609434990404928059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15398951072956660269952039 23098426609434990404928059)
          ·
            refine ⟨34647639914152485607392089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23098426609434990404928059 34647639914152485607392089)
            ·
              refine ⟨25985729935614364205544067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34647639914152485607392089 25985729935614364205544067)
              ·
                refine ⟨38978594903421546308316101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25985729935614364205544067 38978594903421546308316101)
                ·
                  refine ⟨7308486544391539932809269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38978594903421546308316101 7308486544391539932809269)
                  ·
                    refine ⟨685170613536706868700869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7308486544391539932809269 685170613536706868700869)
                    ·
                      rfl

theorem cell23_4003095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_4003095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003095 prefixEnd_4003095 := by exact prefixLift 4003095
  have htrace : WordTrace (prefixWord ++ tailWord_4003095) baseStart_4003095 baseEnd_4003095 := by
    simpa [prefixWord, tailWord_4003095, baseEnd_4003095] using wordTrace_append hprefix tailTrace_4003095
  have hstable : (prefixWord ++ tailWord_4003095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003095).length < 2 ^ (prefixWord ++ tailWord_4003095).sum := by decide
  have hdescent : baseEnd_4003095 < baseStart_4003095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003133 : List Nat := [1, 4, 1, 5, 2, 1, 1, 3, 5]
def baseStart_4003133 : Nat := 118140960795 + 4003133 * 2 ^ 59
def prefixEnd_4003133 : Nat := 4983230072969 + 3 ^ 40 * 4003133 * 2
def baseEnd_4003133 : Nat := 228392372541665717491937

theorem tailTrace_4003133 : CollatzResearch.WordTrace tailWord_4003133 prefixEnd_4003133 228392372541665717491937 := by
  unfold tailWord_4003133
  simp only [CollatzResearch.WordTrace]
  refine ⟨146006255406340296530910053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97337503604226864353940035 146006255406340296530910053)
  ·
    refine ⟨27376172888688805599545635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146006255406340296530910053 27376172888688805599545635)
    ·
      refine ⟨41064259333033208399318453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27376172888688805599545635 41064259333033208399318453)
      ·
        refine ⟨3849774312471863287436105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41064259333033208399318453 3849774312471863287436105)
        ·
          refine ⟨2887330734353897465577079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849774312471863287436105 2887330734353897465577079)
          ·
            refine ⟨4330996101530846198365619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887330734353897465577079 4330996101530846198365619)
            ·
              refine ⟨6496494152296269297548429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330996101530846198365619 6496494152296269297548429)
              ·
                refine ⟨2436185307111100986580661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6496494152296269297548429 2436185307111100986580661)
                ·
                  refine ⟨228392372541665717491937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2436185307111100986580661 228392372541665717491937)
                  ·
                    rfl

theorem cell23_4003133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_4003133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003133 prefixEnd_4003133 := by exact prefixLift 4003133
  have htrace : WordTrace (prefixWord ++ tailWord_4003133) baseStart_4003133 baseEnd_4003133 := by
    simpa [prefixWord, tailWord_4003133, baseEnd_4003133] using wordTrace_append hprefix tailTrace_4003133
  have hstable : (prefixWord ++ tailWord_4003133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003133).length < 2 ^ (prefixWord ++ tailWord_4003133).sum := by decide
  have hdescent : baseEnd_4003133 < baseStart_4003133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003152 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3]
def baseStart_4003152 : Nat := 118140960795 + 4003152 * 2 ^ 59
def prefixEnd_4003152 : Nat := 4983230072969 + 3 ^ 40 * 4003152 * 2
def baseEnd_4003152 : Nat := 2055541109007426883089845

theorem tailTrace_4003152 : CollatzResearch.WordTrace tailWord_4003152 prefixEnd_4003152 2055541109007426883089845 := by
  unfold tailWord_4003152
  simp only [CollatzResearch.WordTrace]
  refine ⟨73003474196635731387925855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97337965595514308517234473 73003474196635731387925855)
  ·
    refine ⟨109505211294953597081888783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73003474196635731387925855 109505211294953597081888783)
    ·
      refine ⟨164257816942430395622833175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109505211294953597081888783 164257816942430395622833175)
      ·
        refine ⟨246386725413645593434249763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164257816942430395622833175 246386725413645593434249763)
        ·
          refine ⟨369580088120468390151374645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246386725413645593434249763 369580088120468390151374645)
          ·
            refine ⟨34648133261293911576691373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369580088120468390151374645 34648133261293911576691373)
            ·
              refine ⟨12993049972985216841259265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34648133261293911576691373 12993049972985216841259265)
              ·
                refine ⟨9744787479738912630944449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12993049972985216841259265 9744787479738912630944449)
                ·
                  refine ⟨7308590609804184473208337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9744787479738912630944449 7308590609804184473208337)
                  ·
                    refine ⟨5481442957353138354906253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7308590609804184473208337 5481442957353138354906253)
                    ·
                      refine ⟨2055541109007426883089845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5481442957353138354906253 2055541109007426883089845)
                      ·
                        rfl

theorem cell23_4003152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_4003152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003152 prefixEnd_4003152 := by exact prefixLift 4003152
  have htrace : WordTrace (prefixWord ++ tailWord_4003152) baseStart_4003152 baseEnd_4003152 := by
    simpa [prefixWord, tailWord_4003152, baseEnd_4003152] using wordTrace_append hprefix tailTrace_4003152
  have hstable : (prefixWord ++ tailWord_4003152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003152).length < 2 ^ (prefixWord ++ tailWord_4003152).sum := by decide
  have hdescent : baseEnd_4003152 < baseStart_4003152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003155 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 6]
def baseStart_4003155 : Nat := 118140960795 + 4003155 * 2 ^ 59
def prefixEnd_4003155 : Nat := 4983230072969 + 3 ^ 40 * 4003155 * 2
def baseEnd_4003155 : Nat := 228393627716598930150259

theorem tailTrace_4003155 : CollatzResearch.WordTrace tailWord_4003155 prefixEnd_4003155 228393627716598930150259 := by
  unfold tailWord_4003155
  simp only [CollatzResearch.WordTrace]
  refine ⟨146007057812260594288210919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97338038541507062858807279 146007057812260594288210919)
  ·
    refine ⟨219010586718390891432316379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146007057812260594288210919 219010586718390891432316379)
    ·
      refine ⟨328515880077586337148474569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219010586718390891432316379 328515880077586337148474569)
      ·
        refine ⟨246386910058189752861355927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328515880077586337148474569 246386910058189752861355927)
        ·
          refine ⟨369580365087284629292033891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246386910058189752861355927 369580365087284629292033891)
          ·
            refine ⟨554370547630926943938050837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369580365087284629292033891 554370547630926943938050837)
            ·
              refine ⟨25986119420199700497096133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 554370547630926943938050837 25986119420199700497096133)
              ·
                refine ⟨4872397391287443843205525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25986119420199700497096133 4872397391287443843205525)
                ·
                  refine ⟨228393627716598930150259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4872397391287443843205525 228393627716598930150259)
                  ·
                    rfl

theorem cell23_4003155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 6].length) (baseStart_4003155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003155 prefixEnd_4003155 := by exact prefixLift 4003155
  have htrace : WordTrace (prefixWord ++ tailWord_4003155) baseStart_4003155 baseEnd_4003155 := by
    simpa [prefixWord, tailWord_4003155, baseEnd_4003155] using wordTrace_append hprefix tailTrace_4003155
  have hstable : (prefixWord ++ tailWord_4003155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003155).length < 2 ^ (prefixWord ++ tailWord_4003155).sum := by decide
  have hdescent : baseEnd_4003155 < baseStart_4003155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003159 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 3, 4]
def baseStart_4003159 : Nat := 118140960795 + 4003159 * 2 ^ 59
def prefixEnd_4003159 : Nat := 4983230072969 + 3 ^ 40 * 4003159 * 2
def baseEnd_4003159 : Nat := 685181567790669451900771

theorem tailTrace_4003159 : CollatzResearch.WordTrace tailWord_4003159 prefixEnd_4003159 685181567790669451900771 := by
  unfold tailWord_4003159
  simp only [CollatzResearch.WordTrace]
  refine ⟨146007203704246102971356531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97338135802830735314237687 146007203704246102971356531)
  ·
    refine ⟨219010805556369154457034797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146007203704246102971356531 219010805556369154457034797)
    ·
      refine ⟨82129052083638432921388049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219010805556369154457034797 82129052083638432921388049)
      ·
        refine ⟨61596789062728824691041037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82129052083638432921388049 61596789062728824691041037)
        ·
          refine ⟨23098795898523309259140389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61596789062728824691041037 23098795898523309259140389)
          ·
            refine ⟨4331024230973120486088823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23098795898523309259140389 4331024230973120486088823)
            ·
              refine ⟨6496536346459680729133235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331024230973120486088823 6496536346459680729133235)
              ·
                refine ⟨9744804519689521093699853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496536346459680729133235 9744804519689521093699853)
                ·
                  refine ⟨3654301694883570410137445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9744804519689521093699853 3654301694883570410137445)
                  ·
                    refine ⟨685181567790669451900771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654301694883570410137445 685181567790669451900771)
                    ·
                      rfl

theorem cell23_4003159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_4003159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003159 prefixEnd_4003159 := by exact prefixLift 4003159
  have htrace : WordTrace (prefixWord ++ tailWord_4003159) baseStart_4003159 baseEnd_4003159 := by
    simpa [prefixWord, tailWord_4003159, baseEnd_4003159] using wordTrace_append hprefix tailTrace_4003159
  have hstable : (prefixWord ++ tailWord_4003159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003159).length < 2 ^ (prefixWord ++ tailWord_4003159).sum := by decide
  have hdescent : baseEnd_4003159 < baseStart_4003159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003172 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 6]
def baseStart_4003172 : Nat := 118140960795 + 4003172 * 2 ^ 59
def prefixEnd_4003172 : Nat := 4983230072969 + 3 ^ 40 * 4003172 * 2
def baseEnd_4003172 : Nat := 228394597624501867204417

theorem tailTrace_4003172 : CollatzResearch.WordTrace tailWord_4003172 prefixEnd_4003172 228394597624501867204417 := by
  unfold tailWord_4003172
  simp only [CollatzResearch.WordTrace]
  refine ⟨73003838926599503095789885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97338451902132670794386513 73003838926599503095789885)
  ·
    refine ⟨27376439597474813660921207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73003838926599503095789885 27376439597474813660921207)
    ·
      refine ⟨41064659396212220491381811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27376439597474813660921207 41064659396212220491381811)
      ·
        refine ⟨61596989094318330737072717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41064659396212220491381811 61596989094318330737072717)
        ·
          refine ⟨23098870910369374026402269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61596989094318330737072717 23098870910369374026402269)
          ·
            refine ⟨8662076591388515259900851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23098870910369374026402269 8662076591388515259900851)
            ·
              refine ⟨12993114887082772889851277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8662076591388515259900851 12993114887082772889851277)
              ·
                refine ⟨4872418082656039833694229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12993114887082772889851277 4872418082656039833694229)
                ·
                  refine ⟨228394597624501867204417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4872418082656039833694229 228394597624501867204417)
                  ·
                    rfl

theorem cell23_4003172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_4003172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003172 prefixEnd_4003172 := by exact prefixLift 4003172
  have htrace : WordTrace (prefixWord ++ tailWord_4003172) baseStart_4003172 baseEnd_4003172 := by
    simpa [prefixWord, tailWord_4003172, baseEnd_4003172] using wordTrace_append hprefix tailTrace_4003172
  have hstable : (prefixWord ++ tailWord_4003172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003172).length < 2 ^ (prefixWord ++ tailWord_4003172).sum := by decide
  have hdescent : baseEnd_4003172 < baseStart_4003172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003232 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 1, 6]
def baseStart_4003232 : Nat := 118140960795 + 4003232 * 2 ^ 59
def prefixEnd_4003232 : Nat := 4983230072969 + 3 ^ 40 * 4003232 * 2
def baseEnd_4003232 : Nat := 685194062486595523363159

theorem tailTrace_4003232 : CollatzResearch.WordTrace tailWord_4003232 prefixEnd_4003232 685194062486595523363159 := by
  unfold tailWord_4003232
  simp only [CollatzResearch.WordTrace]
  refine ⟨73004933116490818219381975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97339910821987757625842633 73004933116490818219381975)
  ·
    refine ⟨109507399674736227329072963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73004933116490818219381975 109507399674736227329072963)
    ·
      refine ⟨164261099512104340993609445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109507399674736227329072963 164261099512104340993609445)
      ·
        refine ⟨30798956158519563936301771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164261099512104340993609445 30798956158519563936301771)
        ·
          refine ⟨46198434237779345904452657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30798956158519563936301771 46198434237779345904452657)
          ·
            refine ⟨34648825678334509428339493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46198434237779345904452657 34648825678334509428339493)
            ·
              refine ⟨6496654814687720517813655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34648825678334509428339493 6496654814687720517813655)
              ·
                refine ⟨9744982222031580776720483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496654814687720517813655 9744982222031580776720483)
                ·
                  refine ⟨14617473333047371165080725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9744982222031580776720483 14617473333047371165080725)
                  ·
                    refine ⟨685194062486595523363159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14617473333047371165080725 685194062486595523363159)
                    ·
                      rfl

theorem cell23_4003232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_4003232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003232 prefixEnd_4003232 := by exact prefixLift 4003232
  have htrace : WordTrace (prefixWord ++ tailWord_4003232) baseStart_4003232 baseEnd_4003232 := by
    simpa [prefixWord, tailWord_4003232, baseEnd_4003232] using wordTrace_append hprefix tailTrace_4003232
  have hstable : (prefixWord ++ tailWord_4003232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003232).length < 2 ^ (prefixWord ++ tailWord_4003232).sum := by decide
  have hdescent : baseEnd_4003232 < baseStart_4003232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003239 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_4003239 : Nat := 118140960795 + 4003239 * 2 ^ 59
def prefixEnd_4003239 : Nat := 4983230072969 + 3 ^ 40 * 4003239 * 2
def baseEnd_4003239 : Nat := 2055585781824368042701945

theorem tailTrace_4003239 : CollatzResearch.WordTrace tailWord_4003239 prefixEnd_4003239 2055585781824368042701945 := by
  unfold tailWord_4003239
  simp only [CollatzResearch.WordTrace]
  refine ⟨146010121543956276634268771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97340081029304184422845847 146010121543956276634268771)
  ·
    refine ⟨219015182315934414951403157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146010121543956276634268771 219015182315934414951403157)
    ·
      refine ⟨10266336671059425700847023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219015182315934414951403157 10266336671059425700847023)
      ·
        refine ⟨15399505006589138551270535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10266336671059425700847023 15399505006589138551270535)
        ·
          refine ⟨23099257509883707826905803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15399505006589138551270535 23099257509883707826905803)
          ·
            refine ⟨34648886264825561740358705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23099257509883707826905803 34648886264825561740358705)
            ·
              refine ⟨25986664698619171305269029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34648886264825561740358705 25986664698619171305269029)
              ·
                refine ⟨4872499630991094619737943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25986664698619171305269029 4872499630991094619737943)
                ·
                  refine ⟨7308749446486641929606915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872499630991094619737943 7308749446486641929606915)
                  ·
                    refine ⟨10963124169729962894410373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7308749446486641929606915 10963124169729962894410373)
                    ·
                      refine ⟨2055585781824368042701945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10963124169729962894410373 2055585781824368042701945)
                      ·
                        rfl

theorem cell23_4003239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_4003239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003239 prefixEnd_4003239 := by exact prefixLift 4003239
  have htrace : WordTrace (prefixWord ++ tailWord_4003239) baseStart_4003239 baseEnd_4003239 := by
    simpa [prefixWord, tailWord_4003239, baseEnd_4003239] using wordTrace_append hprefix tailTrace_4003239
  have hstable : (prefixWord ++ tailWord_4003239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003239).length < 2 ^ (prefixWord ++ tailWord_4003239).sum := by decide
  have hdescent : baseEnd_4003239 < baseStart_4003239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003275 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 9]
def baseStart_4003275 : Nat := 118140960795 + 4003275 * 2 ^ 59
def prefixEnd_4003275 : Nat := 4983230072969 + 3 ^ 40 * 4003275 * 2
def baseEnd_4003275 : Nat := 685201422375976633950593

theorem tailTrace_4003275 : CollatzResearch.WordTrace tailWord_4003275 prefixEnd_4003275 685201422375976633950593 := by
  unfold tailWord_4003275
  simp only [CollatzResearch.WordTrace]
  refine ⟨146011434571825854782579279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97340956381217236521719519 146011434571825854782579279)
  ·
    refine ⟨219017151857738782173868919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146011434571825854782579279 219017151857738782173868919)
    ·
      refine ⟨328525727786608173260803379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219017151857738782173868919 328525727786608173260803379)
      ·
        refine ⟨492788591679912259891205069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328525727786608173260803379 492788591679912259891205069)
        ·
          refine ⟨184795721879967097459201901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492788591679912259891205069 184795721879967097459201901)
          ·
            refine ⟨69298395704987661547200713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184795721879967097459201901 69298395704987661547200713)
            ·
              refine ⟨51973796778740746160400535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69298395704987661547200713 51973796778740746160400535)
              ·
                refine ⟨77960695168111119240600803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51973796778740746160400535 77960695168111119240600803)
                ·
                  refine ⟨116941042752166678860901205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77960695168111119240600803 116941042752166678860901205)
                  ·
                    refine ⟨685201422375976633950593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116941042752166678860901205 685201422375976633950593)
                    ·
                      rfl

theorem cell23_4003275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_4003275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003275 prefixEnd_4003275 := by exact prefixLift 4003275
  have htrace : WordTrace (prefixWord ++ tailWord_4003275) baseStart_4003275 baseEnd_4003275 := by
    simpa [prefixWord, tailWord_4003275, baseEnd_4003275] using wordTrace_append hprefix tailTrace_4003275
  have hstable : (prefixWord ++ tailWord_4003275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003275).length < 2 ^ (prefixWord ++ tailWord_4003275).sum := by decide
  have hdescent : baseEnd_4003275 < baseStart_4003275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003286 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_4003286 : Nat := 118140960795 + 4003286 * 2 ^ 59
def prefixEnd_4003286 : Nat := 4983230072969 + 3 ^ 40 * 4003286 * 2
def baseEnd_4003286 : Nat := 2055609915415129358814229

theorem tailTrace_4003286 : CollatzResearch.WordTrace tailWord_4003286 prefixEnd_4003286 2055609915415129358814229 := by
  unfold tailWord_4003286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9125739735924125228826857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97341223849857335774153141 9125739735924125228826857)
  ·
    refine ⟨6844304801943093921620143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9125739735924125228826857 6844304801943093921620143)
    ·
      refine ⟨10266457202914640882430215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6844304801943093921620143 10266457202914640882430215)
      ·
        refine ⟨15399685804371961323645323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10266457202914640882430215 15399685804371961323645323)
        ·
          refine ⟨23099528706557941985467985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15399685804371961323645323 23099528706557941985467985)
          ·
            refine ⟨17324646529918456489100989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23099528706557941985467985 17324646529918456489100989)
            ·
              refine ⟨6496742448719421183412871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17324646529918456489100989 6496742448719421183412871)
              ·
                refine ⟨9745113673079131775119307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496742448719421183412871 9745113673079131775119307)
                ·
                  refine ⟨14617670509618697662678961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745113673079131775119307 14617670509618697662678961)
                  ·
                    refine ⟨10963252882214023247009221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14617670509618697662678961 10963252882214023247009221)
                    ·
                      refine ⟨2055609915415129358814229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10963252882214023247009221 2055609915415129358814229)
                      ·
                        rfl

theorem cell23_4003286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_4003286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003286 prefixEnd_4003286 := by exact prefixLift 4003286
  have htrace : WordTrace (prefixWord ++ tailWord_4003286) baseStart_4003286 baseEnd_4003286 := by
    simpa [prefixWord, tailWord_4003286, baseEnd_4003286] using wordTrace_append hprefix tailTrace_4003286
  have hstable : (prefixWord ++ tailWord_4003286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003286).length < 2 ^ (prefixWord ++ tailWord_4003286).sum := by decide
  have hdescent : baseEnd_4003286 < baseStart_4003286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003289 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 3]
def baseStart_4003289 : Nat := 118140960795 + 4003289 * 2 ^ 59
def prefixEnd_4003289 : Nat := 4983230072969 + 3 ^ 40 * 4003289 * 2
def baseEnd_4003289 : Nat := 2055611455857092847076715

theorem tailTrace_4003289 : CollatzResearch.WordTrace tailWord_4003289 prefixEnd_4003289 2055611455857092847076715 := by
  unfold tailWord_4003289
  simp only [CollatzResearch.WordTrace]
  refine ⟨146011945193775135173588921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97341296795850090115725947 146011945193775135173588921)
  ·
    refine ⟨109508958895331351380191691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146011945193775135173588921 109508958895331351380191691)
    ·
      refine ⟨164263438342997027070287537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109508958895331351380191691 164263438342997027070287537)
      ·
        refine ⟨123197578757247770302715653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164263438342997027070287537 123197578757247770302715653)
        ·
          refine ⟨23099546016983956931759185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123197578757247770302715653 23099546016983956931759185)
          ·
            refine ⟨17324659512737967698819389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23099546016983956931759185 17324659512737967698819389)
            ·
              refine ⟨6496747317276737887057271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17324659512737967698819389 6496747317276737887057271)
              ·
                refine ⟨9745120975915106830585907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496747317276737887057271 9745120975915106830585907)
                ·
                  refine ⟨14617681463872660245878861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745120975915106830585907 14617681463872660245878861)
                  ·
                    refine ⟨5481630548952247592204573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14617681463872660245878861 5481630548952247592204573)
                    ·
                      refine ⟨2055611455857092847076715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5481630548952247592204573 2055611455857092847076715)
                      ·
                        rfl

theorem cell23_4003289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_4003289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003289 prefixEnd_4003289 := by exact prefixLift 4003289
  have htrace : WordTrace (prefixWord ++ tailWord_4003289) baseStart_4003289 baseEnd_4003289 := by
    simpa [prefixWord, tailWord_4003289, baseEnd_4003289] using wordTrace_append hprefix tailTrace_4003289
  have hstable : (prefixWord ++ tailWord_4003289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003289).length < 2 ^ (prefixWord ++ tailWord_4003289).sum := by decide
  have hdescent : baseEnd_4003289 < baseStart_4003289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003334 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4003334 : Nat := 118140960795 + 4003334 * 2 ^ 59
def prefixEnd_4003334 : Nat := 4983230072969 + 3 ^ 40 * 4003334 * 2
def baseEnd_4003334 : Nat := 685211520828848390338003

theorem tailTrace_4003334 : CollatzResearch.WordTrace tailWord_4003334 prefixEnd_4003334 685211520828848390338003 := by
  unfold tailWord_4003334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562924577456628370593033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97342390985741405239318037 4562924577456628370593033)
  ·
    refine ⟨3422193433092471277944775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4562924577456628370593033 3422193433092471277944775)
    ·
      refine ⟨5133290149638706916917163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422193433092471277944775 5133290149638706916917163)
      ·
        refine ⟨7699935224458060375375745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133290149638706916917163 7699935224458060375375745)
        ·
          refine ⟨5774951418343545281531809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7699935224458060375375745 5774951418343545281531809)
          ·
            refine ⟨4331213563757658961148857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5774951418343545281531809 4331213563757658961148857)
            ·
              refine ⟨3248410172818244220861643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4331213563757658961148857 3248410172818244220861643)
              ·
                refine ⟨4872615259227366331292465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248410172818244220861643 4872615259227366331292465)
                ·
                  refine ⟨3654461444420524748469349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872615259227366331292465 3654461444420524748469349)
                  ·
                    refine ⟨685211520828848390338003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654461444420524748469349 685211520828848390338003)
                    ·
                      rfl

theorem cell23_4003334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4003334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003334 prefixEnd_4003334 := by exact prefixLift 4003334
  have htrace : WordTrace (prefixWord ++ tailWord_4003334) baseStart_4003334 baseEnd_4003334 := by
    simpa [prefixWord, tailWord_4003334, baseEnd_4003334] using wordTrace_append hprefix tailTrace_4003334
  have hstable : (prefixWord ++ tailWord_4003334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003334).length < 2 ^ (prefixWord ++ tailWord_4003334).sum := by decide
  have hdescent : baseEnd_4003334 < baseStart_4003334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003340 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 2, 1, 3]
def baseStart_4003340 : Nat := 118140960795 + 4003340 * 2 ^ 59
def prefixEnd_4003340 : Nat := 4983230072969 + 3 ^ 40 * 4003340 * 2
def baseEnd_4003340 : Nat := 2055637643370472147538981

theorem tailTrace_4003340 : CollatzResearch.WordTrace tailWord_4003340 prefixEnd_4003340 2055637643370472147538981 := by
  unfold tailWord_4003340
  simp only [CollatzResearch.WordTrace]
  refine ⟨73006902658295185441847737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97342536877726913922463649 73006902658295185441847737)
  ·
    refine ⟨54755176993721389081385803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73006902658295185441847737 54755176993721389081385803)
    ·
      refine ⟨82132765490582083622078705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54755176993721389081385803 82132765490582083622078705)
      ·
        refine ⟨61599574117936562716559029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82132765490582083622078705 61599574117936562716559029)
        ·
          refine ⟨5774960073556552754677409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61599574117936562716559029 5774960073556552754677409)
          ·
            refine ⟨4331220055167414566008057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5774960073556552754677409 4331220055167414566008057)
            ·
              refine ⟨3248415041375560924506043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4331220055167414566008057 3248415041375560924506043)
              ·
                refine ⟨4872622562063341386759065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248415041375560924506043 4872622562063341386759065)
                ·
                  refine ⟨3654466921547506040069299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872622562063341386759065 3654466921547506040069299)
                  ·
                    refine ⟨5481700382321259060103949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3654466921547506040069299 5481700382321259060103949)
                    ·
                      refine ⟨2055637643370472147538981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5481700382321259060103949 2055637643370472147538981)
                      ·
                        rfl

theorem cell23_4003340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_4003340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003340 prefixEnd_4003340 := by exact prefixLift 4003340
  have htrace : WordTrace (prefixWord ++ tailWord_4003340) baseStart_4003340 baseEnd_4003340 := by
    simpa [prefixWord, tailWord_4003340, baseEnd_4003340] using wordTrace_append hprefix tailTrace_4003340
  have hstable : (prefixWord ++ tailWord_4003340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003340).length < 2 ^ (prefixWord ++ tailWord_4003340).sum := by decide
  have hdescent : baseEnd_4003340 < baseStart_4003340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003439 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 3]
def baseStart_4003439 : Nat := 118140960795 + 4003439 * 2 ^ 59
def prefixEnd_4003439 : Nat := 4983230072969 + 3 ^ 40 * 4003439 * 2
def baseEnd_4003439 : Nat := 2055688477955267260201025

theorem tailTrace_4003439 : CollatzResearch.WordTrace tailWord_4003439 prefixEnd_4003439 2055688477955267260201025 := by
  unfold tailWord_4003439
  simp only [CollatzResearch.WordTrace]
  refine ⟨146017416143231710791549371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97344944095487807194366247 146017416143231710791549371)
  ·
    refine ⟨219026124214847566187324057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146017416143231710791549371 219026124214847566187324057)
    ·
      refine ⟨164269593161135674640493043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219026124214847566187324057 164269593161135674640493043)
      ·
        refine ⟨246404389741703511960739565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164269593161135674640493043 246404389741703511960739565)
        ·
          refine ⟨92401646153138816985277337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246404389741703511960739565 92401646153138816985277337)
          ·
            refine ⟨69301234614854112738958003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92401646153138816985277337 69301234614854112738958003)
            ·
              refine ⟨103951851922281169108437005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69301234614854112738958003 103951851922281169108437005)
              ·
                refine ⟨38981944470855438415663877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103951851922281169108437005 38981944470855438415663877)
                ·
                  refine ⟨7309114588285394702936977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38981944470855438415663877 7309114588285394702936977)
                  ·
                    refine ⟨5481835941214046027202733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7309114588285394702936977 5481835941214046027202733)
                    ·
                      refine ⟨2055688477955267260201025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5481835941214046027202733 2055688477955267260201025)
                      ·
                        rfl

theorem cell23_4003439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_4003439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003439 prefixEnd_4003439 := by exact prefixLift 4003439
  have htrace : WordTrace (prefixWord ++ tailWord_4003439) baseStart_4003439 baseEnd_4003439 := by
    simpa [prefixWord, tailWord_4003439, baseEnd_4003439] using wordTrace_append hprefix tailTrace_4003439
  have hstable : (prefixWord ++ tailWord_4003439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003439).length < 2 ^ (prefixWord ++ tailWord_4003439).sum := by decide
  have hdescent : baseEnd_4003439 < baseStart_4003439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003472 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 9]
def baseStart_4003472 : Nat := 118140960795 + 4003472 * 2 ^ 59
def prefixEnd_4003472 : Nat := 4983230072969 + 3 ^ 40 * 4003472 * 2
def baseEnd_4003472 : Nat := 685235140938955210362791

theorem tailTrace_4003472 : CollatzResearch.WordTrace tailWord_4003472 prefixEnd_4003472 685235140938955210362791 := by
  unfold tailWord_4003472
  simp only [CollatzResearch.WordTrace]
  refine ⟨73009309876056078713750335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97345746501408104951667113 73009309876056078713750335)
  ·
    refine ⟨109513964814084118070625503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73009309876056078713750335 109513964814084118070625503)
    ·
      refine ⟨164270947221126177105938255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109513964814084118070625503 164270947221126177105938255)
      ·
        refine ⟨246406420831689265658907383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164270947221126177105938255 246406420831689265658907383)
        ·
          refine ⟨369609631247533898488361075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246406420831689265658907383 369609631247533898488361075)
          ·
            refine ⟨554414446871300847732541613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369609631247533898488361075 554414446871300847732541613)
            ·
              refine ⟨207905417576737817899703105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554414446871300847732541613 207905417576737817899703105)
              ·
                refine ⟨155929063182553363424777329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207905417576737817899703105 155929063182553363424777329)
                ·
                  refine ⟨116946797386915022568582997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155929063182553363424777329 116946797386915022568582997)
                  ·
                    refine ⟨685235140938955210362791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116946797386915022568582997 685235140938955210362791)
                    ·
                      rfl

theorem cell23_4003472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_4003472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003472 prefixEnd_4003472 := by exact prefixLift 4003472
  have htrace : WordTrace (prefixWord ++ tailWord_4003472) baseStart_4003472 baseEnd_4003472 := by
    simpa [prefixWord, tailWord_4003472, baseEnd_4003472] using wordTrace_append hprefix tailTrace_4003472
  have hstable : (prefixWord ++ tailWord_4003472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003472).length < 2 ^ (prefixWord ++ tailWord_4003472).sum := by decide
  have hdescent : baseEnd_4003472 < baseStart_4003472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003480 : List Nat := [2, 1, 2, 4, 1, 4, 1, 3, 1, 4]
def baseStart_4003480 : Nat := 118140960795 + 4003480 * 2 ^ 59
def prefixEnd_4003480 : Nat := 4983230072969 + 3 ^ 40 * 4003480 * 2
def baseEnd_4003480 : Nat := 685236510220700533262779

theorem tailTrace_4003480 : CollatzResearch.WordTrace tailWord_4003480 prefixEnd_4003480 685236510220700533262779 := by
  unfold tailWord_4003480
  simp only [CollatzResearch.WordTrace]
  refine ⟨73009455768041587396895947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97345941024055449862527929 73009455768041587396895947)
  ·
    refine ⟨109514183652062381095343921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73009455768041587396895947 109514183652062381095343921)
    ·
      refine ⟨82135637739046785821507941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109514183652062381095343921 82135637739046785821507941)
      ·
        refine ⟨15400432076071272341532739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82135637739046785821507941 15400432076071272341532739)
        ·
          refine ⟨23100648114106908512299109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15400432076071272341532739 23100648114106908512299109)
          ·
            refine ⟨4331371521395045346056083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23100648114106908512299109 4331371521395045346056083)
            ·
              refine ⟨6497057282092568019084125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331371521395045346056083 6497057282092568019084125)
              ·
                refine ⟨2436396480784713007156547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6497057282092568019084125 2436396480784713007156547)
                ·
                  refine ⟨3654594721177069510734821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436396480784713007156547 3654594721177069510734821)
                  ·
                    refine ⟨685236510220700533262779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654594721177069510734821 685236510220700533262779)
                    ·
                      rfl

theorem cell23_4003480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_4003480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003480 prefixEnd_4003480 := by exact prefixLift 4003480
  have htrace : WordTrace (prefixWord ++ tailWord_4003480) baseStart_4003480 baseEnd_4003480 := by
    simpa [prefixWord, tailWord_4003480, baseEnd_4003480] using wordTrace_append hprefix tailTrace_4003480
  have hstable : (prefixWord ++ tailWord_4003480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003480).length < 2 ^ (prefixWord ++ tailWord_4003480).sum := by decide
  have hdescent : baseEnd_4003480 < baseStart_4003480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003490 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4003490 : Nat := 118140960795 + 4003490 * 2 ^ 59
def prefixEnd_4003490 : Nat := 4983230072969 + 3 ^ 40 * 4003490 * 2
def baseEnd_4003490 : Nat := 2055714665468646560663291

theorem tailTrace_4003490 : CollatzResearch.WordTrace tailWord_4003490 prefixEnd_4003490 2055714665468646560663291 := by
  unfold tailWord_4003490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36504819066511736625413981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97346184177364631001103949 36504819066511736625413981)
  ·
    refine ⟨13689307149941901234530243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36504819066511736625413981 13689307149941901234530243)
    ·
      refine ⟨20533960724912851851795365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13689307149941901234530243 20533960724912851851795365)
      ·
        refine ⟨3850117635921159722211631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20533960724912851851795365 3850117635921159722211631)
        ·
          refine ⟨5775176453881739583317447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850117635921159722211631 5775176453881739583317447)
          ·
            refine ⟨8662764680822609374976171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775176453881739583317447 8662764680822609374976171)
            ·
              refine ⟨12994147021233914062464257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8662764680822609374976171 12994147021233914062464257)
              ·
                refine ⟨9745610265925435546848193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12994147021233914062464257 9745610265925435546848193)
                ·
                  refine ⟨7309207699444076660136145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9745610265925435546848193 7309207699444076660136145)
                  ·
                    refine ⟨5481905774583057495102109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7309207699444076660136145 5481905774583057495102109)
                    ·
                      refine ⟨2055714665468646560663291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5481905774583057495102109 2055714665468646560663291)
                      ·
                        rfl

theorem cell23_4003490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4003490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003490 prefixEnd_4003490 := by exact prefixLift 4003490
  have htrace : WordTrace (prefixWord ++ tailWord_4003490) baseStart_4003490 baseEnd_4003490 := by
    simpa [prefixWord, tailWord_4003490, baseEnd_4003490] using wordTrace_append hprefix tailTrace_4003490
  have hstable : (prefixWord ++ tailWord_4003490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003490).length < 2 ^ (prefixWord ++ tailWord_4003490).sum := by decide
  have hdescent : baseEnd_4003490 < baseStart_4003490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003510 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_4003510 : Nat := 118140960795 + 4003510 * 2 ^ 59
def prefixEnd_4003510 : Nat := 4983230072969 + 3 ^ 40 * 4003510 * 2
def baseEnd_4003510 : Nat := 228413881675748498045911

theorem tailTrace_4003510 : CollatzResearch.WordTrace tailWord_4003510 prefixEnd_4003510 228413881675748498045911 := by
  unfold tailWord_4003510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126250357873405619836499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97346670483982993278255989 9126250357873405619836499)
  ·
    refine ⟨13689375536810108429754749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9126250357873405619836499 13689375536810108429754749)
    ·
      refine ⟨5133515826303790661158031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13689375536810108429754749 5133515826303790661158031)
      ·
        refine ⟨7700273739455685991737047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133515826303790661158031 7700273739455685991737047)
        ·
          refine ⟨11550410609183528987605571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700273739455685991737047 11550410609183528987605571)
          ·
            refine ⟨17325615913775293481408357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550410609183528987605571 17325615913775293481408357)
            ·
              refine ⟨3248552983832867527764067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17325615913775293481408357 3248552983832867527764067)
              ·
                refine ⟨4872829475749301291646101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248552983832867527764067 4872829475749301291646101)
                ·
                  refine ⟨228413881675748498045911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4872829475749301291646101 228413881675748498045911)
                  ·
                    rfl

theorem cell23_4003510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_4003510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003510 prefixEnd_4003510 := by exact prefixLift 4003510
  have htrace : WordTrace (prefixWord ++ tailWord_4003510) baseStart_4003510 baseEnd_4003510 := by
    simpa [prefixWord, tailWord_4003510, baseEnd_4003510] using wordTrace_append hprefix tailTrace_4003510
  have hstable : (prefixWord ++ tailWord_4003510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003510).length < 2 ^ (prefixWord ++ tailWord_4003510).sum := by decide
  have hdescent : baseEnd_4003510 < baseStart_4003510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003519 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 1, 6]
def baseStart_4003519 : Nat := 118140960795 + 4003519 * 2 ^ 59
def prefixEnd_4003519 : Nat := 4983230072969 + 3 ^ 40 * 4003519 * 2
def baseEnd_4003519 : Nat := 685243185469208982400219

theorem tailTrace_4003519 : CollatzResearch.WordTrace tailWord_4003519 prefixEnd_4003519 685243185469208982400219 := by
  unfold tailWord_4003519
  simp only [CollatzResearch.WordTrace]
  refine ⟨146020333982941884454461611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97346889321961256302974407 146020333982941884454461611)
  ·
    refine ⟨219030500974412826681692417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146020333982941884454461611 219030500974412826681692417)
    ·
      refine ⟨164272875730809620011269313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219030500974412826681692417 164272875730809620011269313)
      ·
        refine ⟨123204656798107215008451985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164272875730809620011269313 123204656798107215008451985)
        ·
          refine ⟨92403492598580411256338989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123204656798107215008451985 92403492598580411256338989)
          ·
            refine ⟨34651309724467654221127121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92403492598580411256338989 34651309724467654221127121)
            ·
              refine ⟨25988482293350740665845341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34651309724467654221127121 25988482293350740665845341)
              ·
                refine ⟨9745680860006527749692003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25988482293350740665845341 9745680860006527749692003)
                ·
                  refine ⟨14618521290009791624538005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745680860006527749692003 14618521290009791624538005)
                  ·
                    refine ⟨685243185469208982400219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14618521290009791624538005 685243185469208982400219)
                    ·
                      rfl

theorem cell23_4003519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_4003519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003519 prefixEnd_4003519 := by exact prefixLift 4003519
  have htrace : WordTrace (prefixWord ++ tailWord_4003519) baseStart_4003519 baseEnd_4003519 := by
    simpa [prefixWord, tailWord_4003519, baseEnd_4003519] using wordTrace_append hprefix tailTrace_4003519
  have hstable : (prefixWord ++ tailWord_4003519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003519).length < 2 ^ (prefixWord ++ tailWord_4003519).sum := by decide
  have hdescent : baseEnd_4003519 < baseStart_4003519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003530 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_4003530 : Nat := 118140960795 + 4003530 * 2 ^ 59
def prefixEnd_4003530 : Nat := 4983230072969 + 3 ^ 40 * 4003530 * 2
def baseEnd_4003530 : Nat := 2055735204694826404163107

theorem tailTrace_4003530 : CollatzResearch.WordTrace tailWord_4003530 prefixEnd_4003530 2055735204694826404163107 := by
  unfold tailWord_4003530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36505183796475508333278011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97347156790601355555408029 36505183796475508333278011)
  ·
    refine ⟨54757775694713262499917017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36505183796475508333278011 54757775694713262499917017)
    ·
      refine ⟨41068331771034946874937763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54757775694713262499917017 41068331771034946874937763)
      ·
        refine ⟨61602497656552420312406645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41068331771034946874937763 61602497656552420312406645)
        ·
          refine ⟨5775234155301789404288123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61602497656552420312406645 5775234155301789404288123)
          ·
            refine ⟨8662851232952684106432185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775234155301789404288123 8662851232952684106432185)
            ·
              refine ⟨6497138424714513079824139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8662851232952684106432185 6497138424714513079824139)
              ·
                refine ⟨9745707637071769619736209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497138424714513079824139 9745707637071769619736209)
                ·
                  refine ⟨7309280727803827214802157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9745707637071769619736209 7309280727803827214802157)
                  ·
                    refine ⟨2740980272926435205550809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7309280727803827214802157 2740980272926435205550809)
                    ·
                      refine ⟨2055735204694826404163107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2740980272926435205550809 2055735204694826404163107)
                      ·
                        rfl

theorem cell23_4003530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_4003530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003530 prefixEnd_4003530 := by exact prefixLift 4003530
  have htrace : WordTrace (prefixWord ++ tailWord_4003530) baseStart_4003530 baseEnd_4003530 := by
    simpa [prefixWord, tailWord_4003530, baseEnd_4003530] using wordTrace_append hprefix tailTrace_4003530
  have hstable : (prefixWord ++ tailWord_4003530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003530).length < 2 ^ (prefixWord ++ tailWord_4003530).sum := by decide
  have hdescent : baseEnd_4003530 < baseStart_4003530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003540 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_4003540 : Nat := 118140960795 + 4003540 * 2 ^ 59
def prefixEnd_4003540 : Nat := 4983230072969 + 3 ^ 40 * 4003540 * 2
def baseEnd_4003540 : Nat := 685246779833790455012687

theorem tailTrace_4003540 : CollatzResearch.WordTrace tailWord_4003540 prefixEnd_4003540 685246779833790455012687 := by
  unfold tailWord_4003540
  simp only [CollatzResearch.WordTrace]
  refine ⟨73010549957932902520488037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97347399943910536693984049 73010549957932902520488037)
  ·
    refine ⟨13689478117112419222591507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73010549957932902520488037 13689478117112419222591507)
    ·
      refine ⟨20534217175668628833887261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13689478117112419222591507 20534217175668628833887261)
      ·
        refine ⟨7700331440875735812707723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20534217175668628833887261 7700331440875735812707723)
        ·
          refine ⟨11550497161313603719061585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700331440875735812707723 11550497161313603719061585)
          ·
            refine ⟨8662872870985202789296189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11550497161313603719061585 8662872870985202789296189)
            ·
              refine ⟨3248577326619451045986071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8662872870985202789296189 3248577326619451045986071)
              ·
                refine ⟨4872865989929176568979107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248577326619451045986071 4872865989929176568979107)
                ·
                  refine ⟨7309298984893764853468661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872865989929176568979107 7309298984893764853468661)
                  ·
                    refine ⟨685246779833790455012687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7309298984893764853468661 685246779833790455012687)
                    ·
                      rfl

theorem cell23_4003540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_4003540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003540 prefixEnd_4003540 := by exact prefixLift 4003540
  have htrace : WordTrace (prefixWord ++ tailWord_4003540) baseStart_4003540 baseEnd_4003540 := by
    simpa [prefixWord, tailWord_4003540, baseEnd_4003540] using wordTrace_append hprefix tailTrace_4003540
  have hstable : (prefixWord ++ tailWord_4003540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003540).length < 2 ^ (prefixWord ++ tailWord_4003540).sum := by decide
  have hdescent : baseEnd_4003540 < baseStart_4003540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003543 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 1, 1, 4]
def baseStart_4003543 : Nat := 118140960795 + 4003543 * 2 ^ 59
def prefixEnd_4003543 : Nat := 4983230072969 + 3 ^ 40 * 4003543 * 2
def baseEnd_4003543 : Nat := 2055741879943334853300547

theorem tailTrace_4003543 : CollatzResearch.WordTrace tailWord_4003543 prefixEnd_4003543 2055741879943334853300547 := by
  unfold tailWord_4003543
  simp only [CollatzResearch.WordTrace]
  refine ⟨146021209334854936553335283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97347472889903291035556855 146021209334854936553335283)
  ·
    refine ⟨219031814002282404830002925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146021209334854936553335283 219031814002282404830002925)
    ·
      refine ⟨82136930250855901811251097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219031814002282404830002925 82136930250855901811251097)
      ·
        refine ⟨61602697688141926358438323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82136930250855901811251097 61602697688141926358438323)
        ·
          refine ⟨92404046532212889537657485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61602697688141926358438323 92404046532212889537657485)
          ·
            refine ⟨34651517449579833576621557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92404046532212889537657485 34651517449579833576621557)
            ·
              refine ⟨3248579760898109397808271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34651517449579833576621557 3248579760898109397808271)
              ·
                refine ⟨4872869641347164096712407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248579760898109397808271 4872869641347164096712407)
                ·
                  refine ⟨7309304462020746145068611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872869641347164096712407 7309304462020746145068611)
                  ·
                    refine ⟨10963956693031119217602917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7309304462020746145068611 10963956693031119217602917)
                    ·
                      refine ⟨2055741879943334853300547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10963956693031119217602917 2055741879943334853300547)
                      ·
                        rfl

theorem cell23_4003543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_4003543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003543 prefixEnd_4003543 := by exact prefixLift 4003543
  have htrace : WordTrace (prefixWord ++ tailWord_4003543) baseStart_4003543 baseEnd_4003543 := by
    simpa [prefixWord, tailWord_4003543, baseEnd_4003543] using wordTrace_append hprefix tailTrace_4003543
  have hstable : (prefixWord ++ tailWord_4003543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003543).length < 2 ^ (prefixWord ++ tailWord_4003543).sum := by decide
  have hdescent : baseEnd_4003543 < baseStart_4003543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003546 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_4003546 : Nat := 118140960795 + 4003546 * 2 ^ 59
def prefixEnd_4003546 : Nat := 4983230072969 + 3 ^ 40 * 4003546 * 2
def baseEnd_4003546 : Nat := 2055743420385298341563033

theorem tailTrace_4003546 : CollatzResearch.WordTrace tailWord_4003546 prefixEnd_4003546 2055743420385298341563033 := by
  unfold tailWord_4003546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36505329688461017016423623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97347545835896045377129661 36505329688461017016423623)
  ·
    refine ⟨54757994532691525524635435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36505329688461017016423623 54757994532691525524635435)
    ·
      refine ⟨82136991799037288286953153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54757994532691525524635435 82136991799037288286953153)
      ·
        refine ⟨61602743849277966215214865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82136991799037288286953153 61602743849277966215214865)
        ·
          refine ⟨46202057886958474661411149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61602743849277966215214865 46202057886958474661411149)
          ·
            refine ⟨17325771707609427998029181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46202057886958474661411149 17325771707609427998029181)
            ·
              refine ⟨6497164390353535499260943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17325771707609427998029181 6497164390353535499260943)
              ·
                refine ⟨9745746585530303248891415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497164390353535499260943 9745746585530303248891415)
                ·
                  refine ⟨14618619878295454873337123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745746585530303248891415 14618619878295454873337123)
                  ·
                    refine ⟨21927929817443182310005685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14618619878295454873337123 21927929817443182310005685)
                    ·
                      refine ⟨2055743420385298341563033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21927929817443182310005685 2055743420385298341563033)
                      ·
                        rfl

theorem cell23_4003546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_4003546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003546 prefixEnd_4003546 := by exact prefixLift 4003546
  have htrace : WordTrace (prefixWord ++ tailWord_4003546) baseStart_4003546 baseEnd_4003546 := by
    simpa [prefixWord, tailWord_4003546, baseEnd_4003546] using wordTrace_append hprefix tailTrace_4003546
  have hstable : (prefixWord ++ tailWord_4003546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003546).length < 2 ^ (prefixWord ++ tailWord_4003546).sum := by decide
  have hdescent : baseEnd_4003546 < baseStart_4003546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
