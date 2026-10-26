import V185TrunkScan19Chunk027

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_280070 : List Nat := [6, 2, 1, 1, 2, 1, 3, 3]
def baseStart_280070 : Nat := 118140960795 + 280070 * 2 ^ 59
def prefixEnd_280070 : Nat := 4983230072969 + 3 ^ 40 * 280070 * 2
def baseEnd_280070 : Nat := 85221052980636716170067

theorem tailTrace_280070 : CollatzResearch.WordTrace tailWord_280070 prefixEnd_280070 85221052980636716170067 := by
  unfold tailWord_280070
  simp only [CollatzResearch.WordTrace]
  refine ⟨319218502980053031031177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6809994730241131328665109 319218502980053031031177)
  ·
    refine ⟨239413877235039773273383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 319218502980053031031177 239413877235039773273383)
    ·
      refine ⟨359120815852559659910075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239413877235039773273383 359120815852559659910075)
      ·
        refine ⟨538681223778839489865113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359120815852559659910075 538681223778839489865113)
        ·
          refine ⟨404010917834129617398835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538681223778839489865113 404010917834129617398835)
          ·
            refine ⟨606016376751194426098253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404010917834129617398835 606016376751194426098253)
            ·
              refine ⟨227256141281697909786845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606016376751194426098253 227256141281697909786845)
              ·
                refine ⟨85221052980636716170067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227256141281697909786845 85221052980636716170067)
                ·
                  rfl

theorem cell19_280070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_280070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280070 prefixEnd_280070 := by exact prefixLift 280070
  have htrace : WordTrace (prefixWord ++ tailWord_280070) baseStart_280070 baseEnd_280070 := by
    simpa [prefixWord, tailWord_280070, baseEnd_280070] using wordTrace_append hprefix tailTrace_280070
  have hstable : (prefixWord ++ tailWord_280070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280070).length < 2 ^ (prefixWord ++ tailWord_280070).sum := by decide
  have hdescent : baseEnd_280070 < baseStart_280070 := by decide
  rcases family_descends (prefixWord ++ tailWord_280070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280076 : List Nat := [2, 2, 1, 2, 5, 1, 3, 3]
def baseStart_280076 : Nat := 118140960795 + 280076 * 2 ^ 59
def prefixEnd_280076 : Nat := 4983230072969 + 3 ^ 40 * 280076 * 2
def baseEnd_280076 : Nat := 85222878689630480036717

theorem tailTrace_280076 : CollatzResearch.WordTrace tailWord_280076 prefixEnd_280076 85222878689630480036717 := by
  unfold tailWord_280076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5107605466669980008858041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6810140622226640011810721 5107605466669980008858041)
  ·
    refine ⟨3830704100002485006643531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5107605466669980008858041 3830704100002485006643531)
    ·
      refine ⟨5746056150003727509965297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830704100002485006643531 5746056150003727509965297)
      ·
        refine ⟨4309542112502795632473973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5746056150003727509965297 4309542112502795632473973)
        ·
          refine ⟨404019573047137090544435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4309542112502795632473973 404019573047137090544435)
          ·
            refine ⟨606029359570705635816653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404019573047137090544435 606029359570705635816653)
            ·
              refine ⟨227261009839014613431245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606029359570705635816653 227261009839014613431245)
              ·
                refine ⟨85222878689630480036717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227261009839014613431245 85222878689630480036717)
                ·
                  rfl

theorem cell19_280076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_280076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280076 prefixEnd_280076 := by exact prefixLift 280076
  have htrace : WordTrace (prefixWord ++ tailWord_280076) baseStart_280076 baseEnd_280076 := by
    simpa [prefixWord, tailWord_280076, baseEnd_280076] using wordTrace_append hprefix tailTrace_280076
  have hstable : (prefixWord ++ tailWord_280076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280076).length < 2 ^ (prefixWord ++ tailWord_280076).sum := by decide
  have hdescent : baseEnd_280076 < baseStart_280076 := by decide
  rcases family_descends (prefixWord ++ tailWord_280076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280135 : List Nat := [1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_280135 : Nat := 118140960795 + 280135 * 2 ^ 59
def prefixEnd_280135 : Nat := 4983230072969 + 3 ^ 40 * 280135 * 2
def baseEnd_280135 : Nat := 85240831494735824725445

theorem tailTrace_280135 : CollatzResearch.WordTrace tailWord_280135 prefixEnd_280135 85240831494735824725445 := by
  unfold tailWord_280135
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217362840126213094113859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6811575226750808729409239 10217362840126213094113859)
  ·
    refine ⟨15326044260189319641170789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10217362840126213094113859 15326044260189319641170789)
    ·
      refine ⟨2873633298785497432719523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15326044260189319641170789 2873633298785497432719523)
      ·
        refine ⟨4310449948178246149079285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2873633298785497432719523 4310449948178246149079285)
        ·
          refine ⟨404104682641710576476183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4310449948178246149079285 404104682641710576476183)
          ·
            refine ⟨606157023962565864714275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404104682641710576476183 606157023962565864714275)
            ·
              refine ⟨909235535943848797071413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606157023962565864714275 909235535943848797071413)
              ·
                refine ⟨85240831494735824725445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 909235535943848797071413 85240831494735824725445)
                ·
                  rfl

theorem cell19_280135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_280135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280135 prefixEnd_280135 := by exact prefixLift 280135
  have htrace : WordTrace (prefixWord ++ tailWord_280135) baseStart_280135 baseEnd_280135 := by
    simpa [prefixWord, tailWord_280135, baseEnd_280135] using wordTrace_append hprefix tailTrace_280135
  have hstable : (prefixWord ++ tailWord_280135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280135).length < 2 ^ (prefixWord ++ tailWord_280135).sum := by decide
  have hdescent : baseEnd_280135 < baseStart_280135 := by decide
  rcases family_descends (prefixWord ++ tailWord_280135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280226 : List Nat := [3, 3, 1, 4, 1, 2, 1, 4]
def baseStart_280226 : Nat := 118140960795 + 280226 * 2 ^ 59
def prefixEnd_280226 : Nat := 4983230072969 + 3 ^ 40 * 280226 * 2
def baseEnd_280226 : Nat := 85268521414474576702975

theorem tailTrace_280226 : CollatzResearch.WordTrace tailWord_280226 prefixEnd_280226 85268521414474576702975 := by
  unfold tailWord_280226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555170470699133908919133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6813787921864357090451021 2555170470699133908919133)
  ·
    refine ⟨958188926512175215844675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2555170470699133908919133 958188926512175215844675)
    ·
      refine ⟨1437283389768262823767013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 958188926512175215844675 1437283389768262823767013)
      ·
        refine ⟨269490635581549279456315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1437283389768262823767013 269490635581549279456315)
        ·
          refine ⟨404235953372323919184473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269490635581549279456315 404235953372323919184473)
          ·
            refine ⟨303176965029242939388355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404235953372323919184473 303176965029242939388355)
            ·
              refine ⟨454765447543864409082533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303176965029242939388355 454765447543864409082533)
              ·
                refine ⟨85268521414474576702975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454765447543864409082533 85268521414474576702975)
                ·
                  rfl

theorem cell19_280226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_280226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280226 prefixEnd_280226 := by exact prefixLift 280226
  have htrace : WordTrace (prefixWord ++ tailWord_280226) baseStart_280226 baseEnd_280226 := by
    simpa [prefixWord, tailWord_280226, baseEnd_280226] using wordTrace_append hprefix tailTrace_280226
  have hstable : (prefixWord ++ tailWord_280226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280226).length < 2 ^ (prefixWord ++ tailWord_280226).sum := by decide
  have hdescent : baseEnd_280226 < baseStart_280226 := by decide
  rcases family_descends (prefixWord ++ tailWord_280226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280268 : List Nat := [2, 2, 1, 5, 2, 1, 6]
def baseStart_280268 : Nat := 118140960795 + 280268 * 2 ^ 59
def prefixEnd_280268 : Nat := 4983230072969 + 3 ^ 40 * 280268 * 2
def baseEnd_280268 : Nat := 28427100459143641256509

theorem tailTrace_280268 : CollatzResearch.WordTrace tailWord_280268 prefixEnd_280268 28427100459143641256509 := by
  unfold tailWord_280268
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111106874322188404352729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6814809165762917872470305 5111106874322188404352729)
  ·
    refine ⟨3833330155741641303264547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5111106874322188404352729 3833330155741641303264547)
    ·
      refine ⟨5749995233612461954896821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3833330155741641303264547 5749995233612461954896821)
      ·
        refine ⟨539062053151168308271577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5749995233612461954896821 539062053151168308271577)
        ·
          refine ⟨404296539863376231203683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539062053151168308271577 404296539863376231203683)
          ·
            refine ⟨606444809795064346805525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404296539863376231203683 606444809795064346805525)
            ·
              refine ⟨28427100459143641256509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 606444809795064346805525 28427100459143641256509)
              ·
                rfl

theorem cell19_280268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_280268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280268 prefixEnd_280268 := by exact prefixLift 280268
  have htrace : WordTrace (prefixWord ++ tailWord_280268) baseStart_280268 baseEnd_280268 := by
    simpa [prefixWord, tailWord_280268, baseEnd_280268] using wordTrace_append hprefix tailTrace_280268
  have hstable : (prefixWord ++ tailWord_280268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280268).length < 2 ^ (prefixWord ++ tailWord_280268).sum := by decide
  have hdescent : baseEnd_280268 < baseStart_280268 := by decide
  rcases family_descends (prefixWord ++ tailWord_280268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280270 : List Nat := [4, 1, 1, 1, 3, 1, 8]
def baseStart_280270 : Nat := 118140960795 + 280270 * 2 ^ 59
def prefixEnd_280270 : Nat := 4983230072969 + 3 ^ 40 * 280270 * 2
def baseEnd_280270 : Nat := 28427303315698503908359

theorem tailTrace_280270 : CollatzResearch.WordTrace tailWord_280270 prefixEnd_280270 28427303315698503908359 := by
  unfold tailWord_280270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1277785836829641393784783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6814857796424754100185509 1277785836829641393784783)
  ·
    refine ⟨1916678755244462090677175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1277785836829641393784783 1916678755244462090677175)
    ·
      refine ⟨2875018132866693136015763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916678755244462090677175 2875018132866693136015763)
      ·
        refine ⟨4312527199300039704023645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875018132866693136015763 4312527199300039704023645)
        ·
          refine ⟨1617197699737514889008867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4312527199300039704023645 1617197699737514889008867)
          ·
            refine ⟨2425796549606272333513301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617197699737514889008867 2425796549606272333513301)
            ·
              refine ⟨28427303315698503908359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2425796549606272333513301 28427303315698503908359)
              ·
                rfl

theorem cell19_280270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_280270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280270 prefixEnd_280270 := by exact prefixLift 280270
  have htrace : WordTrace (prefixWord ++ tailWord_280270) baseStart_280270 baseEnd_280270 := by
    simpa [prefixWord, tailWord_280270, baseEnd_280270] using wordTrace_append hprefix tailTrace_280270
  have hstable : (prefixWord ++ tailWord_280270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280270).length < 2 ^ (prefixWord ++ tailWord_280270).sum := by decide
  have hdescent : baseEnd_280270 < baseStart_280270 := by decide
  rcases family_descends (prefixWord ++ tailWord_280270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280346 : List Nat := [3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_280346 : Nat := 118140960795 + 280346 * 2 ^ 59
def prefixEnd_280346 : Nat := 4983230072969 + 3 ^ 40 * 280346 * 2
def baseEnd_280346 : Nat := 85305035594349854035981

theorem tailTrace_280346 : CollatzResearch.WordTrace tailWord_280346 prefixEnd_280346 85305035594349854035981 := by
  unfold tailWord_280346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556264660590449032511223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6816705761574530753363261 2556264660590449032511223)
  ·
    refine ⟨3834396990885673548766835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2556264660590449032511223 3834396990885673548766835)
    ·
      refine ⟨5751595486328510323150253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3834396990885673548766835 5751595486328510323150253)
      ·
        refine ⟨2156848307373191371181345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5751595486328510323150253 2156848307373191371181345)
        ·
          refine ⟨1617636230529893528386009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2156848307373191371181345 1617636230529893528386009)
          ·
            refine ⟨1213227172897420146289507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1617636230529893528386009 1213227172897420146289507)
            ·
              refine ⟨1819840759346130219434261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213227172897420146289507 1819840759346130219434261)
              ·
                refine ⟨85305035594349854035981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1819840759346130219434261 85305035594349854035981)
                ·
                  rfl

theorem cell19_280346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_280346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280346 prefixEnd_280346 := by exact prefixLift 280346
  have htrace : WordTrace (prefixWord ++ tailWord_280346) baseStart_280346 baseEnd_280346 := by
    simpa [prefixWord, tailWord_280346, baseEnd_280346] using wordTrace_append hprefix tailTrace_280346
  have hstable : (prefixWord ++ tailWord_280346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280346).length < 2 ^ (prefixWord ++ tailWord_280346).sum := by decide
  have hdescent : baseEnd_280346 < baseStart_280346 := by decide
  rcases family_descends (prefixWord ++ tailWord_280346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280401 : List Nat := [1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_280401 : Nat := 118140960795 + 280401 * 2 ^ 59
def prefixEnd_280401 : Nat := 4983230072969 + 3 ^ 40 * 280401 * 2
def baseEnd_280401 : Nat := 85321771260126022813609

theorem tailTrace_280401 : CollatzResearch.WordTrace tailWord_280401 prefixEnd_280401 85321771260126022813609 := by
  unfold tailWord_280401
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227064657162540523297057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6818043104775027015531371 10227064657162540523297057)
  ·
    refine ⟨7670298492871905392472793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10227064657162540523297057 7670298492871905392472793)
    ·
      refine ⟨5752723869653929044354595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7670298492871905392472793 5752723869653929044354595)
      ·
        refine ⟨8629085804480893566531893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5752723869653929044354595 8629085804480893566531893)
        ·
          refine ⟨808976794170083771862365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8629085804480893566531893 808976794170083771862365)
          ·
            refine ⟨303366297813781414448387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 808976794170083771862365 303366297813781414448387)
            ·
              refine ⟨455049446720672121672581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303366297813781414448387 455049446720672121672581)
              ·
                refine ⟨85321771260126022813609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455049446720672121672581 85321771260126022813609)
                ·
                  rfl

theorem cell19_280401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_280401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280401 prefixEnd_280401 := by exact prefixLift 280401
  have htrace : WordTrace (prefixWord ++ tailWord_280401) baseStart_280401 baseEnd_280401 := by
    simpa [prefixWord, tailWord_280401, baseEnd_280401] using wordTrace_append hprefix tailTrace_280401
  have hstable : (prefixWord ++ tailWord_280401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280401).length < 2 ^ (prefixWord ++ tailWord_280401).sum := by decide
  have hdescent : baseEnd_280401 < baseStart_280401 := by decide
  rcases family_descends (prefixWord ++ tailWord_280401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280418 : List Nat := [3, 3, 2, 1, 2, 2, 3, 3]
def baseStart_280418 : Nat := 118140960795 + 280418 * 2 ^ 59
def prefixEnd_280418 : Nat := 4983230072969 + 3 ^ 40 * 280418 * 2
def baseEnd_280418 : Nat := 85326944102275020435785

theorem tailTrace_280418 : CollatzResearch.WordTrace tailWord_280418 prefixEnd_280418 85326944102275020435785 := by
  unfold tailWord_280418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556921174525238106666477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6818456465400634951110605 2556921174525238106666477)
  ·
    refine ⟨958845440446964289999929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2556921174525238106666477 958845440446964289999929)
    ·
      refine ⟨719134080335223217499947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 958845440446964289999929 719134080335223217499947)
      ·
        refine ⟨1078701120502834826249921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719134080335223217499947 1078701120502834826249921)
        ·
          refine ⟨809025840377126119687441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1078701120502834826249921 809025840377126119687441)
          ·
            refine ⟨606769380282844589765581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809025840377126119687441 606769380282844589765581)
            ·
              refine ⟨227538517606066721162093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606769380282844589765581 227538517606066721162093)
              ·
                refine ⟨85326944102275020435785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227538517606066721162093 85326944102275020435785)
                ·
                  rfl

theorem cell19_280418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_280418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280418 prefixEnd_280418 := by exact prefixLift 280418
  have htrace : WordTrace (prefixWord ++ tailWord_280418) baseStart_280418 baseEnd_280418 := by
    simpa [prefixWord, tailWord_280418, baseEnd_280418] using wordTrace_append hprefix tailTrace_280418
  have hstable : (prefixWord ++ tailWord_280418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280418).length < 2 ^ (prefixWord ++ tailWord_280418).sum := by decide
  have hdescent : baseEnd_280418 < baseStart_280418 := by decide
  rcases family_descends (prefixWord ++ tailWord_280418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280477 : List Nat := [1, 4, 2, 1, 2, 2, 4, 3]
def baseStart_280477 : Nat := 118140960795 + 280477 * 2 ^ 59
def prefixEnd_280477 : Nat := 4983230072969 + 3 ^ 40 * 280477 * 2
def baseEnd_280477 : Nat := 85344896907380365124513

theorem tailTrace_280477 : CollatzResearch.WordTrace tailWord_280477 prefixEnd_280477 85344896907380365124513 := by
  unfold tailWord_280477
  simp only [CollatzResearch.WordTrace]
  refine ⟨10229836604887205503063685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6819891069924803668709123 10229836604887205503063685)
  ·
    refine ⟨1918094363416351031824441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10229836604887205503063685 1918094363416351031824441)
    ·
      refine ⟨1438570772562263273868331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1918094363416351031824441 1438570772562263273868331)
      ·
        refine ⟨2157856158843394910802497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438570772562263273868331 2157856158843394910802497)
        ·
          refine ⟨1618392119132546183101873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157856158843394910802497 1618392119132546183101873)
          ·
            refine ⟨1213794089349409637326405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618392119132546183101873 1213794089349409637326405)
            ·
              refine ⟨227586391753014306998701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1213794089349409637326405 227586391753014306998701)
              ·
                refine ⟨85344896907380365124513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227586391753014306998701 85344896907380365124513)
                ·
                  rfl

theorem cell19_280477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_280477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280477 prefixEnd_280477 := by exact prefixLift 280477
  have htrace : WordTrace (prefixWord ++ tailWord_280477) baseStart_280477 baseEnd_280477 := by
    simpa [prefixWord, tailWord_280477, baseEnd_280477] using wordTrace_append hprefix tailTrace_280477
  have hstable : (prefixWord ++ tailWord_280477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280477).length < 2 ^ (prefixWord ++ tailWord_280477).sum := by decide
  have hdescent : baseEnd_280477 < baseStart_280477 := by decide
  rcases family_descends (prefixWord ++ tailWord_280477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280576 : List Nat := [2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_280576 : Nat := 118140960795 + 280576 * 2 ^ 59
def prefixEnd_280576 : Nat := 4983230072969 + 3 ^ 40 * 280576 * 2
def baseEnd_280576 : Nat := 85375021105777468924243

theorem tailTrace_280576 : CollatzResearch.WordTrace tailWord_280576 prefixEnd_280576 85375021105777468924243 := by
  unfold tailWord_280576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5116723715764272705458791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6822298287685696940611721 5116723715764272705458791)
  ·
    refine ⟨7675085573646409058188187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5116723715764272705458791 7675085573646409058188187)
    ·
      refine ⟨11512628360469613587282281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7675085573646409058188187 11512628360469613587282281)
      ·
        refine ⟨8634471270352210190461711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11512628360469613587282281 8634471270352210190461711)
        ·
          refine ⟨12951706905528315285692567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8634471270352210190461711 12951706905528315285692567)
          ·
            refine ⟨19427560358292472928538851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12951706905528315285692567 19427560358292472928538851)
            ·
              refine ⟨29141340537438709392808277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19427560358292472928538851 29141340537438709392808277)
              ·
                refine ⟨85375021105777468924243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29141340537438709392808277 85375021105777468924243)
                ·
                  rfl

theorem cell19_280576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_280576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280576 prefixEnd_280576 := by exact prefixLift 280576
  have htrace : WordTrace (prefixWord ++ tailWord_280576) baseStart_280576 baseEnd_280576 := by
    simpa [prefixWord, tailWord_280576, baseEnd_280576] using wordTrace_append hprefix tailTrace_280576
  have hstable : (prefixWord ++ tailWord_280576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280576).length < 2 ^ (prefixWord ++ tailWord_280576).sum := by decide
  have hdescent : baseEnd_280576 < baseStart_280576 := by decide
  rcases family_descends (prefixWord ++ tailWord_280576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280595 : List Nat := [1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_280595 : Nat := 118140960795 + 280595 * 2 ^ 59
def prefixEnd_280595 : Nat := 4983230072969 + 3 ^ 40 * 280595 * 2
def baseEnd_280595 : Nat := 85380802517591054501969

theorem tailTrace_280595 : CollatzResearch.WordTrace tailWord_280595 prefixEnd_280595 85380802517591054501969 := by
  unfold tailWord_280595
  simp only [CollatzResearch.WordTrace]
  refine ⟨10234140418459711655859239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6822760278973141103906159 10234140418459711655859239)
  ·
    refine ⟨15351210627689567483788859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10234140418459711655859239 15351210627689567483788859)
    ·
      refine ⟨23026815941534351225683289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15351210627689567483788859 23026815941534351225683289)
      ·
        refine ⟨17270111956150763419262467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23026815941534351225683289 17270111956150763419262467)
        ·
          refine ⟨25905167934226145128893701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17270111956150763419262467 25905167934226145128893701)
          ·
            refine ⟨4857218987667402211667569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25905167934226145128893701 4857218987667402211667569)
            ·
              refine ⟨3642914240750551658750677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857218987667402211667569 3642914240750551658750677)
              ·
                refine ⟨85380802517591054501969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3642914240750551658750677 85380802517591054501969)
                ·
                  rfl

theorem cell19_280595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_280595 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280595 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280595 prefixEnd_280595 := by exact prefixLift 280595
  have htrace : WordTrace (prefixWord ++ tailWord_280595) baseStart_280595 baseEnd_280595 := by
    simpa [prefixWord, tailWord_280595, baseEnd_280595] using wordTrace_append hprefix tailTrace_280595
  have hstable : (prefixWord ++ tailWord_280595).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280595).length < 2 ^ (prefixWord ++ tailWord_280595).sum := by decide
  have hdescent : baseEnd_280595 < baseStart_280595 := by decide
  rcases family_descends (prefixWord ++ tailWord_280595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280688 : List Nat := [2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_280688 : Nat := 118140960795 + 280688 * 2 ^ 59
def prefixEnd_280688 : Nat := 4983230072969 + 3 ^ 40 * 280688 * 2
def baseEnd_280688 : Nat := 85409101006994394435049

theorem tailTrace_280688 : CollatzResearch.WordTrace tailWord_280688 prefixEnd_280688 85409101006994394435049 := by
  unfold tailWord_280688
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118766203561394269497359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6825021604748525692663145 5118766203561394269497359)
  ·
    refine ⟨7678149305342091404246039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5118766203561394269497359 7678149305342091404246039)
    ·
      refine ⟨11517223958013137106369059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7678149305342091404246039 11517223958013137106369059)
      ·
        refine ⟨17275835937019705659553589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11517223958013137106369059 17275835937019705659553589)
        ·
          refine ⟨1619609619095597405583149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17275835937019705659553589 1619609619095597405583149)
          ·
            refine ⟨607353607160849027093681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1619609619095597405583149 607353607160849027093681)
            ·
              refine ⟨455515205370636770320261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607353607160849027093681 455515205370636770320261)
              ·
                refine ⟨85409101006994394435049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455515205370636770320261 85409101006994394435049)
                ·
                  rfl

theorem cell19_280688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_280688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280688 prefixEnd_280688 := by exact prefixLift 280688
  have htrace : WordTrace (prefixWord ++ tailWord_280688) baseStart_280688 baseEnd_280688 := by
    simpa [prefixWord, tailWord_280688, baseEnd_280688] using wordTrace_append hprefix tailTrace_280688
  have hstable : (prefixWord ++ tailWord_280688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280688).length < 2 ^ (prefixWord ++ tailWord_280688).sum := by decide
  have hdescent : baseEnd_280688 < baseStart_280688 := by decide
  rcases family_descends (prefixWord ++ tailWord_280688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280724 : List Nat := [2, 4, 2, 3, 1, 7]
def baseStart_280724 : Nat := 118140960795 + 280724 * 2 ^ 59
def prefixEnd_280724 : Nat := 4983230072969 + 3 ^ 40 * 280724 * 2
def baseEnd_280724 : Nat := 9491117251217441959439

theorem tailTrace_280724 : CollatzResearch.WordTrace tailWord_280724 prefixEnd_280724 9491117251217441959439 := by
  unfold tailWord_280724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119422717496183343652613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6825896956661577791536817 5119422717496183343652613)
  ·
    refine ⟨959891759530534376934865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5119422717496183343652613 959891759530534376934865)
    ·
      refine ⟨719918819647900782701149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 959891759530534376934865 719918819647900782701149)
      ·
        refine ⟨269969557367962793512931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 719918819647900782701149 269969557367962793512931)
        ·
          refine ⟨404954336051944190269397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269969557367962793512931 404954336051944190269397)
          ·
            refine ⟨9491117251217441959439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 404954336051944190269397 9491117251217441959439)
            ·
              rfl

theorem cell19_280724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 7].length) (baseStart_280724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280724 prefixEnd_280724 := by exact prefixLift 280724
  have htrace : WordTrace (prefixWord ++ tailWord_280724) baseStart_280724 baseEnd_280724 := by
    simpa [prefixWord, tailWord_280724, baseEnd_280724] using wordTrace_append hprefix tailTrace_280724
  have hstable : (prefixWord ++ tailWord_280724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280724).length < 2 ^ (prefixWord ++ tailWord_280724).sum := by decide
  have hdescent : baseEnd_280724 < baseStart_280724 := by decide
  rcases family_descends (prefixWord ++ tailWord_280724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280728 : List Nat := [2, 1, 2, 4, 10]
def baseStart_280728 : Nat := 118140960795 + 280728 * 2 ^ 59
def prefixEnd_280728 : Nat := 4983230072969 + 3 ^ 40 * 280728 * 2
def baseEnd_280728 : Nat := 3163750829640227909113

theorem tailTrace_280728 : CollatzResearch.WordTrace tailWord_280728 prefixEnd_280728 3163750829640227909113 := by
  unfold tailWord_280728
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119495663488937685225419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6825994217985250246967225 5119495663488937685225419)
  ·
    refine ⟨7679243495233406527838129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5119495663488937685225419 7679243495233406527838129)
    ·
      refine ⟨5759432621425054895878597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7679243495233406527838129 5759432621425054895878597)
      ·
        refine ⟨1079893616517197792977237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5759432621425054895878597 1079893616517197792977237)
        ·
          refine ⟨3163750829640227909113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1079893616517197792977237 3163750829640227909113)
          ·
            rfl

theorem cell19_280728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 10].length) (baseStart_280728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280728 prefixEnd_280728 := by exact prefixLift 280728
  have htrace : WordTrace (prefixWord ++ tailWord_280728) baseStart_280728 baseEnd_280728 := by
    simpa [prefixWord, tailWord_280728, baseEnd_280728] using wordTrace_append hprefix tailTrace_280728
  have hstable : (prefixWord ++ tailWord_280728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280728).length < 2 ^ (prefixWord ++ tailWord_280728).sum := by decide
  have hdescent : baseEnd_280728 < baseStart_280728 := by decide
  rcases family_descends (prefixWord ++ tailWord_280728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280756 : List Nat := [2, 5, 3, 1, 1, 1, 3, 3]
def baseStart_280756 : Nat := 118140960795 + 280756 * 2 ^ 59
def prefixEnd_280756 : Nat := 4983230072969 + 3 ^ 40 * 280756 * 2
def baseEnd_280756 : Nat := 85429792375590384923753

theorem tailTrace_280756 : CollatzResearch.WordTrace tailWord_280756 prefixEnd_280756 85429792375590384923753 := by
  unfold tailWord_280756
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120006285438218076235061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6826675047250957434980081 5120006285438218076235061)
  ·
    refine ⟨480000589259832944647037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5120006285438218076235061 480000589259832944647037)
    ·
      refine ⟨180000220972437354242639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 480000589259832944647037 180000220972437354242639)
      ·
        refine ⟨270000331458656031363959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180000220972437354242639 270000331458656031363959)
        ·
          refine ⟨405000497187984047045939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270000331458656031363959 405000497187984047045939)
          ·
            refine ⟨607500745781976070568909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405000497187984047045939 607500745781976070568909)
            ·
              refine ⟨227812779668241026463341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607500745781976070568909 227812779668241026463341)
              ·
                refine ⟨85429792375590384923753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227812779668241026463341 85429792375590384923753)
                ·
                  rfl

theorem cell19_280756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_280756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280756 prefixEnd_280756 := by exact prefixLift 280756
  have htrace : WordTrace (prefixWord ++ tailWord_280756) baseStart_280756 baseEnd_280756 := by
    simpa [prefixWord, tailWord_280756, baseEnd_280756] using wordTrace_append hprefix tailTrace_280756
  have hstable : (prefixWord ++ tailWord_280756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280756).length < 2 ^ (prefixWord ++ tailWord_280756).sum := by decide
  have hdescent : baseEnd_280756 < baseStart_280756 := by decide
  rcases family_descends (prefixWord ++ tailWord_280756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280804 : List Nat := [2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_280804 : Nat := 118140960795 + 280804 * 2 ^ 59
def prefixEnd_280804 : Nat := 4983230072969 + 3 ^ 40 * 280804 * 2
def baseEnd_280804 : Nat := 85444398047540495856955

theorem tailTrace_280804 : CollatzResearch.WordTrace tailWord_280804 prefixEnd_280804 85444398047540495856955 := by
  unfold tailWord_280804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120881637351270175108733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6827842183135026900144977 5120881637351270175108733)
  ·
    refine ⟨1920330614006726315665775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5120881637351270175108733 1920330614006726315665775)
    ·
      refine ⟨2880495921010089473498663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920330614006726315665775 2880495921010089473498663)
      ·
        refine ⟨4320743881515134210247995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880495921010089473498663 4320743881515134210247995)
        ·
          refine ⟨6481115822272701315371993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320743881515134210247995 6481115822272701315371993)
          ·
            refine ⟨4860836866704525986528995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6481115822272701315371993 4860836866704525986528995)
            ·
              refine ⟨7291255300056788979793493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860836866704525986528995 7291255300056788979793493)
              ·
                refine ⟨85444398047540495856955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7291255300056788979793493 85444398047540495856955)
                ·
                  rfl

theorem cell19_280804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_280804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280804 prefixEnd_280804 := by exact prefixLift 280804
  have htrace : WordTrace (prefixWord ++ tailWord_280804) baseStart_280804 baseEnd_280804 := by
    simpa [prefixWord, tailWord_280804, baseEnd_280804] using wordTrace_append hprefix tailTrace_280804
  have hstable : (prefixWord ++ tailWord_280804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280804).length < 2 ^ (prefixWord ++ tailWord_280804).sum := by decide
  have hdescent : baseEnd_280804 < baseStart_280804 := by decide
  rcases family_descends (prefixWord ++ tailWord_280804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280840 : List Nat := [2, 1, 3, 2, 3, 3, 5]
def baseStart_280840 : Nat := 118140960795 + 280840 * 2 ^ 59
def prefixEnd_280840 : Nat := 4983230072969 + 3 ^ 40 * 280840 * 2
def baseEnd_280840 : Nat := 28485117433834359685619

theorem tailTrace_280840 : CollatzResearch.WordTrace tailWord_280840 prefixEnd_280840 28485117433834359685619 := by
  unfold tailWord_280840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121538151286059249263987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6828717535048078999018649 5121538151286059249263987)
  ·
    refine ⟨7682307226929088873895981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5121538151286059249263987 7682307226929088873895981)
    ·
      refine ⟨2880865210098408327710993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7682307226929088873895981 2880865210098408327710993)
      ·
        refine ⟨2160648907573806245783245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880865210098408327710993 2160648907573806245783245)
        ·
          refine ⟨810243340340177342168717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2160648907573806245783245 810243340340177342168717)
          ·
            refine ⟨303841252627566503313269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 810243340340177342168717 303841252627566503313269)
            ·
              refine ⟨28485117433834359685619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 303841252627566503313269 28485117433834359685619)
              ·
                rfl

theorem cell19_280840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_280840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280840 prefixEnd_280840 := by exact prefixLift 280840
  have htrace : WordTrace (prefixWord ++ tailWord_280840) baseStart_280840 baseEnd_280840 := by
    simpa [prefixWord, tailWord_280840, baseEnd_280840] using wordTrace_append hprefix tailTrace_280840
  have hstable : (prefixWord ++ tailWord_280840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280840).length < 2 ^ (prefixWord ++ tailWord_280840).sum := by decide
  have hdescent : baseEnd_280840 < baseStart_280840 := by decide
  rcases family_descends (prefixWord ++ tailWord_280840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280842 : List Nat := [3, 1, 2, 2, 1, 1, 9]
def baseStart_280842 : Nat := 118140960795 + 280842 * 2 ^ 59
def prefixEnd_280842 : Nat := 4983230072969 + 3 ^ 40 * 280842 * 2
def baseEnd_280842 : Nat := 28485320290389222337469

theorem tailTrace_280842 : CollatzResearch.WordTrace tailWord_280842 prefixEnd_280842 28485320290389222337469 := by
  unfold tailWord_280842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560787312141218210025195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6828766165709915226733853 2560787312141218210025195)
  ·
    refine ⟨3841180968211827315037793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560787312141218210025195 3841180968211827315037793)
    ·
      refine ⟨2880885726158870486278345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3841180968211827315037793 2880885726158870486278345)
      ·
        refine ⟨2160664294619152864708759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880885726158870486278345 2160664294619152864708759)
        ·
          refine ⟨3240996441928729297063139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160664294619152864708759 3240996441928729297063139)
          ·
            refine ⟨4861494662893093945594709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240996441928729297063139 4861494662893093945594709)
            ·
              refine ⟨28485320290389222337469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4861494662893093945594709 28485320290389222337469)
              ·
                rfl

theorem cell19_280842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_280842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280842 prefixEnd_280842 := by exact prefixLift 280842
  have htrace : WordTrace (prefixWord ++ tailWord_280842) baseStart_280842 baseEnd_280842 := by
    simpa [prefixWord, tailWord_280842, baseEnd_280842] using wordTrace_append hprefix tailTrace_280842
  have hstable : (prefixWord ++ tailWord_280842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280842).length < 2 ^ (prefixWord ++ tailWord_280842).sum := by decide
  have hdescent : baseEnd_280842 < baseStart_280842 := by decide
  rcases family_descends (prefixWord ++ tailWord_280842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280897 : List Nat := [1, 2, 5, 2, 2, 7]
def baseStart_280897 : Nat := 118140960795 + 280897 * 2 ^ 59
def prefixEnd_280897 : Nat := 4983230072969 + 3 ^ 40 * 280897 * 2
def baseEnd_280897 : Nat := 9496966281882648421115

theorem tailTrace_280897 : CollatzResearch.WordTrace tailWord_280897 prefixEnd_280897 9496966281882648421115 := by
  unfold tailWord_280897
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245155263365617233352945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6830103508910411488901963 10245155263365617233352945)
  ·
    refine ⟨7683866447524212925014709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10245155263365617233352945 7683866447524212925014709)
    ·
      refine ⟨720362479455394961720129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7683866447524212925014709 720362479455394961720129)
      ·
        refine ⟨540271859591546221290097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720362479455394961720129 540271859591546221290097)
        ·
          refine ⟨405203894693659665967573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540271859591546221290097 405203894693659665967573)
          ·
            refine ⟨9496966281882648421115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 405203894693659665967573 9496966281882648421115)
            ·
              rfl

theorem cell19_280897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_280897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280897 prefixEnd_280897 := by exact prefixLift 280897
  have htrace : WordTrace (prefixWord ++ tailWord_280897) baseStart_280897 baseEnd_280897 := by
    simpa [prefixWord, tailWord_280897, baseEnd_280897] using wordTrace_append hprefix tailTrace_280897
  have hstable : (prefixWord ++ tailWord_280897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280897).length < 2 ^ (prefixWord ++ tailWord_280897).sum := by decide
  have hdescent : baseEnd_280897 < baseStart_280897 := by decide
  rcases family_descends (prefixWord ++ tailWord_280897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280916 : List Nat := [2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_280916 : Nat := 118140960795 + 280916 * 2 ^ 59
def prefixEnd_280916 : Nat := 4983230072969 + 3 ^ 40 * 280916 * 2
def baseEnd_280916 : Nat := 85478477948757421367761

theorem tailTrace_280916 : CollatzResearch.WordTrace tailWord_280916 prefixEnd_280916 85478477948757421367761 := by
  unfold tailWord_280916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122924125148391739147301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6830565500197855652196401 5122924125148391739147301)
  ·
    refine ⟨960548273465323451090119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5122924125148391739147301 960548273465323451090119)
    ·
      refine ⟨1440822410197985176635179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960548273465323451090119 1440822410197985176635179)
      ·
        refine ⟨2161233615296977764952769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440822410197985176635179 2161233615296977764952769)
        ·
          refine ⟨1620925211472733323714577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161233615296977764952769 1620925211472733323714577)
          ·
            refine ⟨1215693908604549992785933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1620925211472733323714577 1215693908604549992785933)
            ·
              refine ⟨455885215726706247294725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1215693908604549992785933 455885215726706247294725)
              ·
                refine ⟨85478477948757421367761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455885215726706247294725 85478477948757421367761)
                ·
                  rfl

theorem cell19_280916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_280916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280916 prefixEnd_280916 := by exact prefixLift 280916
  have htrace : WordTrace (prefixWord ++ tailWord_280916) baseStart_280916 baseEnd_280916 := by
    simpa [prefixWord, tailWord_280916, baseEnd_280916] using wordTrace_append hprefix tailTrace_280916
  have hstable : (prefixWord ++ tailWord_280916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280916).length < 2 ^ (prefixWord ++ tailWord_280916).sum := by decide
  have hdescent : baseEnd_280916 < baseStart_280916 := by decide
  rcases family_descends (prefixWord ++ tailWord_280916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280982 : List Nat := [5, 3, 1, 2, 2, 1, 2, 3]
def baseStart_280982 : Nat := 118140960795 + 280982 * 2 ^ 59
def prefixEnd_280982 : Nat := 4983230072969 + 3 ^ 40 * 280982 * 2
def baseEnd_280982 : Nat := 85498560747688823900915

theorem tailTrace_280982 : CollatzResearch.WordTrace tailWord_280982 prefixEnd_280982 85498560747688823900915 := by
  unfold tailWord_280982
  simp only [CollatzResearch.WordTrace]
  refine ⟨640515966753604796887325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6832170312038451166798133 640515966753604796887325)
  ·
    refine ⟨240193487532601798832747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 640515966753604796887325 240193487532601798832747)
    ·
      refine ⟨360290231298902698249121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240193487532601798832747 360290231298902698249121)
      ·
        refine ⟨270217673474177023686841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360290231298902698249121 270217673474177023686841)
        ·
          refine ⟨202663255105632767765131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270217673474177023686841 202663255105632767765131)
          ·
            refine ⟨303994882658449151647697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202663255105632767765131 303994882658449151647697)
            ·
              refine ⟨227996161993836863735773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303994882658449151647697 227996161993836863735773)
              ·
                refine ⟨85498560747688823900915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227996161993836863735773 85498560747688823900915)
                ·
                  rfl

theorem cell19_280982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_280982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280982 prefixEnd_280982 := by exact prefixLift 280982
  have htrace : WordTrace (prefixWord ++ tailWord_280982) baseStart_280982 baseEnd_280982 := by
    simpa [prefixWord, tailWord_280982, baseEnd_280982] using wordTrace_append hprefix tailTrace_280982
  have hstable : (prefixWord ++ tailWord_280982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280982).length < 2 ^ (prefixWord ++ tailWord_280982).sum := by decide
  have hdescent : baseEnd_280982 < baseStart_280982 := by decide
  rcases family_descends (prefixWord ++ tailWord_280982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280990 : List Nat := [4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_280990 : Nat := 118140960795 + 280990 * 2 ^ 59
def prefixEnd_280990 : Nat := 4983230072969 + 3 ^ 40 * 280990 * 2
def baseEnd_280990 : Nat := 85500995026347175723115

theorem tailTrace_280990 : CollatzResearch.WordTrace tailWord_280990 prefixEnd_280990 85500995026347175723115 := by
  unfold tailWord_280990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281068406503586764561053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6832364834685796077658949 1281068406503586764561053)
  ·
    refine ⟨480400652438845036710395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1281068406503586764561053 480400652438845036710395)
    ·
      refine ⟨720600978658267555065593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480400652438845036710395 720600978658267555065593)
      ·
        refine ⟨540450733993700666299195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720600978658267555065593 540450733993700666299195)
        ·
          refine ⟨810676100990550999448793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540450733993700666299195 810676100990550999448793)
          ·
            refine ⟨608007075742913249586595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810676100990550999448793 608007075742913249586595)
            ·
              refine ⟨912010613614369874379893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608007075742913249586595 912010613614369874379893)
              ·
                refine ⟨85500995026347175723115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 912010613614369874379893 85500995026347175723115)
                ·
                  rfl

theorem cell19_280990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_280990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280990 prefixEnd_280990 := by exact prefixLift 280990
  have htrace : WordTrace (prefixWord ++ tailWord_280990) baseStart_280990 baseEnd_280990 := by
    simpa [prefixWord, tailWord_280990, baseEnd_280990] using wordTrace_append hprefix tailTrace_280990
  have hstable : (prefixWord ++ tailWord_280990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280990).length < 2 ^ (prefixWord ++ tailWord_280990).sum := by decide
  have hdescent : baseEnd_280990 < baseStart_280990 := by decide
  rcases family_descends (prefixWord ++ tailWord_280990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280992 : List Nat := [2, 1, 1, 4, 1, 3, 4, 3]
def baseStart_280992 : Nat := 118140960795 + 280992 * 2 ^ 59
def prefixEnd_280992 : Nat := 4983230072969 + 3 ^ 40 * 280992 * 2
def baseEnd_280992 : Nat := 85501603596011763678665

theorem tailTrace_280992 : CollatzResearch.WordTrace tailWord_280992 prefixEnd_280992 85501603596011763678665 := by
  unfold tailWord_280992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5124310099010724229030615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6832413465347632305374153 5124310099010724229030615)
  ·
    refine ⟨7686465148516086343545923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5124310099010724229030615 7686465148516086343545923)
    ·
      refine ⟨11529697722774129515318885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7686465148516086343545923 11529697722774129515318885)
      ·
        refine ⟨2161818323020149284122291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11529697722774129515318885 2161818323020149284122291)
        ·
          refine ⟨3242727484530223926183437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161818323020149284122291 3242727484530223926183437)
          ·
            refine ⟨1216022806698833972318789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3242727484530223926183437 1216022806698833972318789)
            ·
              refine ⟨228004276256031369809773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1216022806698833972318789 228004276256031369809773)
              ·
                refine ⟨85501603596011763678665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228004276256031369809773 85501603596011763678665)
                ·
                  rfl

theorem cell19_280992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_280992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_280992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_280992 prefixEnd_280992 := by exact prefixLift 280992
  have htrace : WordTrace (prefixWord ++ tailWord_280992) baseStart_280992 baseEnd_280992 := by
    simpa [prefixWord, tailWord_280992, baseEnd_280992] using wordTrace_append hprefix tailTrace_280992
  have hstable : (prefixWord ++ tailWord_280992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280992).length < 2 ^ (prefixWord ++ tailWord_280992).sum := by decide
  have hdescent : baseEnd_280992 < baseStart_280992 := by decide
  rcases family_descends (prefixWord ++ tailWord_280992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281028 : List Nat := [2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_281028 : Nat := 118140960795 + 281028 * 2 ^ 59
def prefixEnd_281028 : Nat := 4983230072969 + 3 ^ 40 * 281028 * 2
def baseEnd_281028 : Nat := 85512557849974346878567

theorem tailTrace_281028 : CollatzResearch.WordTrace tailWord_281028 prefixEnd_281028 85512557849974346878567 := by
  unfold tailWord_281028
  simp only [CollatzResearch.WordTrace]
  refine ⟨5124966612945513303185869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6833288817260684404247825 5124966612945513303185869)
  ·
    refine ⟨1921862479854567488694701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5124966612945513303185869 1921862479854567488694701)
    ·
      refine ⟨720698429945462808260513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1921862479854567488694701 720698429945462808260513)
      ·
        refine ⟨540523822459097106195385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720698429945462808260513 540523822459097106195385)
        ·
          refine ⟨405392866844322829646539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540523822459097106195385 405392866844322829646539)
          ·
            refine ⟨608089300266484244469809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405392866844322829646539 608089300266484244469809)
            ·
              refine ⟨456066975199863183352357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608089300266484244469809 456066975199863183352357)
              ·
                refine ⟨85512557849974346878567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456066975199863183352357 85512557849974346878567)
                ·
                  rfl

theorem cell19_281028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_281028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281028 prefixEnd_281028 := by exact prefixLift 281028
  have htrace : WordTrace (prefixWord ++ tailWord_281028) baseStart_281028 baseEnd_281028 := by
    simpa [prefixWord, tailWord_281028, baseEnd_281028] using wordTrace_append hprefix tailTrace_281028
  have hstable : (prefixWord ++ tailWord_281028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281028).length < 2 ^ (prefixWord ++ tailWord_281028).sum := by decide
  have hdescent : baseEnd_281028 < baseStart_281028 := by decide
  rcases family_descends (prefixWord ++ tailWord_281028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281032 : List Nat := [2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_281032 : Nat := 118140960795 + 281032 * 2 ^ 59
def prefixEnd_281032 : Nat := 4983230072969 + 3 ^ 40 * 281032 * 2
def baseEnd_281032 : Nat := 85513774989303522789667

theorem tailTrace_281032 : CollatzResearch.WordTrace tailWord_281032 prefixEnd_281032 85513774989303522789667 := by
  unfold tailWord_281032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5125039558938267644758675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6833386078584356859678233 5125039558938267644758675)
  ·
    refine ⟨7687559338407401467138013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5125039558938267644758675 7687559338407401467138013)
    ·
      refine ⟨2882834751902775550176755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7687559338407401467138013 2882834751902775550176755)
      ·
        refine ⟨4324252127854163325265133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882834751902775550176755 4324252127854163325265133)
        ·
          refine ⟨1621594547945311246974425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4324252127854163325265133 1621594547945311246974425)
          ·
            refine ⟨1216195910958983435230819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621594547945311246974425 1216195910958983435230819)
            ·
              refine ⟨1824293866438475152846229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216195910958983435230819 1824293866438475152846229)
              ·
                refine ⟨85513774989303522789667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1824293866438475152846229 85513774989303522789667)
                ·
                  rfl

theorem cell19_281032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_281032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281032 prefixEnd_281032 := by exact prefixLift 281032
  have htrace : WordTrace (prefixWord ++ tailWord_281032) baseStart_281032 baseEnd_281032 := by
    simpa [prefixWord, tailWord_281032, baseEnd_281032] using wordTrace_append hprefix tailTrace_281032
  have hstable : (prefixWord ++ tailWord_281032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281032).length < 2 ^ (prefixWord ++ tailWord_281032).sum := by decide
  have hdescent : baseEnd_281032 < baseStart_281032 := by decide
  rcases family_descends (prefixWord ++ tailWord_281032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281070 : List Nat := [4, 1, 2, 1, 2, 9]
def baseStart_281070 : Nat := 118140960795 + 281070 * 2 ^ 59
def prefixEnd_281070 : Nat := 4983230072969 + 3 ^ 40 * 281070 * 2
def baseEnd_281070 : Nat := 9502815312547854882791

theorem tailTrace_281070 : CollatzResearch.WordTrace tailWord_281070 prefixEnd_281070 9502815312547854882791 := by
  unfold tailWord_281070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281433136467358472425083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6834310061159245186267109 1281433136467358472425083)
  ·
    refine ⟨1922149704701037708637625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1281433136467358472425083 1922149704701037708637625)
    ·
      refine ⟨1441612278525778281478219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1922149704701037708637625 1441612278525778281478219)
      ·
        refine ⟨2162418417788667422217329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441612278525778281478219 2162418417788667422217329)
        ·
          refine ⟨1621813813341500566662997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2162418417788667422217329 1621813813341500566662997)
          ·
            refine ⟨9502815312547854882791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1621813813341500566662997 9502815312547854882791)
            ·
              rfl

theorem cell19_281070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_281070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281070 prefixEnd_281070 := by exact prefixLift 281070
  have htrace : WordTrace (prefixWord ++ tailWord_281070) baseStart_281070 baseEnd_281070 := by
    simpa [prefixWord, tailWord_281070, baseEnd_281070] using wordTrace_append hprefix tailTrace_281070
  have hstable : (prefixWord ++ tailWord_281070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281070).length < 2 ^ (prefixWord ++ tailWord_281070).sum := by decide
  have hdescent : baseEnd_281070 < baseStart_281070 := by decide
  rcases family_descends (prefixWord ++ tailWord_281070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281180 : List Nat := [2, 2, 4, 1, 4, 1, 5]
def baseStart_281180 : Nat := 118140960795 + 281180 * 2 ^ 59
def prefixEnd_281180 : Nat := 4983230072969 + 3 ^ 40 * 281180 * 2
def baseEnd_281180 : Nat := 28519603048161010500125

theorem tailTrace_281180 : CollatzResearch.WordTrace tailWord_281180 prefixEnd_281180 28519603048161010500125 := by
  unfold tailWord_281180
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127738560670178282952497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6836984747560237710603329 5127738560670178282952497)
  ·
    refine ⟨3845803920502633712214373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5127738560670178282952497 3845803920502633712214373)
    ·
      refine ⟨721088235094243821040195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3845803920502633712214373 721088235094243821040195)
      ·
        refine ⟨1081632352641365731560293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721088235094243821040195 1081632352641365731560293)
        ·
          refine ⟨202806066120256074667555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1081632352641365731560293 202806066120256074667555)
          ·
            refine ⟨304209099180384112001333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202806066120256074667555 304209099180384112001333)
            ·
              refine ⟨28519603048161010500125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 304209099180384112001333 28519603048161010500125)
              ·
                rfl

theorem cell19_281180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_281180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281180 prefixEnd_281180 := by exact prefixLift 281180
  have htrace : WordTrace (prefixWord ++ tailWord_281180) baseStart_281180 baseEnd_281180 := by
    simpa [prefixWord, tailWord_281180, baseEnd_281180] using wordTrace_append hprefix tailTrace_281180
  have hstable : (prefixWord ++ tailWord_281180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281180).length < 2 ^ (prefixWord ++ tailWord_281180).sum := by decide
  have hdescent : baseEnd_281180 < baseStart_281180 := by decide
  rcases family_descends (prefixWord ++ tailWord_281180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281277 : List Nat := [1, 4, 1, 2, 1, 4, 3, 3]
def baseStart_281277 : Nat := 118140960795 + 281277 * 2 ^ 59
def prefixEnd_281277 : Nat := 4983230072969 + 3 ^ 40 * 281277 * 2
def baseEnd_281277 : Nat := 85588324773215547344555

theorem tailTrace_281277 : CollatzResearch.WordTrace tailWord_281277 prefixEnd_281277 85588324773215547344555 := by
  unfold tailWord_281277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10259015001988942132186085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6839343334659294754790723 10259015001988942132186085)
  ·
    refine ⟨1923565312872926649784891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10259015001988942132186085 1923565312872926649784891)
    ·
      refine ⟨2885347969309389974677337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923565312872926649784891 2885347969309389974677337)
      ·
        refine ⟨2164010976982042481008003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2885347969309389974677337 2164010976982042481008003)
        ·
          refine ⟨3246016465473063721512005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164010976982042481008003 3246016465473063721512005)
          ·
            refine ⟨608628087276199447783501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3246016465473063721512005 608628087276199447783501)
            ·
              refine ⟨228235532728574792918813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 608628087276199447783501 228235532728574792918813)
              ·
                refine ⟨85588324773215547344555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228235532728574792918813 85588324773215547344555)
                ·
                  rfl

theorem cell19_281277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_281277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281277 prefixEnd_281277 := by exact prefixLift 281277
  have htrace : WordTrace (prefixWord ++ tailWord_281277) baseStart_281277 baseEnd_281277 := by
    simpa [prefixWord, tailWord_281277, baseEnd_281277] using wordTrace_append hprefix tailTrace_281277
  have hstable : (prefixWord ++ tailWord_281277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281277).length < 2 ^ (prefixWord ++ tailWord_281277).sum := by decide
  have hdescent : baseEnd_281277 < baseStart_281277 := by decide
  rcases family_descends (prefixWord ++ tailWord_281277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281431 : List Nat := [1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_281431 : Nat := 118140960795 + 281431 * 2 ^ 59
def prefixEnd_281431 : Nat := 4983230072969 + 3 ^ 40 * 281431 * 2
def baseEnd_281431 : Nat := 85635184637388819921913

theorem tailTrace_281431 : CollatzResearch.WordTrace tailWord_281431 prefixEnd_281431 85635184637388819921913 := by
  unfold tailWord_281431
  simp only [CollatzResearch.WordTrace]
  refine ⟨10264631843431026433292147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6843087895620684288861431 10264631843431026433292147)
  ·
    refine ⟨15396947765146539649938221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10264631843431026433292147 15396947765146539649938221)
    ·
      refine ⟨5773855411929952368726833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15396947765146539649938221 5773855411929952368726833)
      ·
        refine ⟨4330391558947464276545125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5773855411929952368726833 4330391558947464276545125)
        ·
          refine ⟨811948417302649551852211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4330391558947464276545125 811948417302649551852211)
          ·
            refine ⟨1217922625953974327778317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811948417302649551852211 1217922625953974327778317)
            ·
              refine ⟨456720984732740372916869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1217922625953974327778317 456720984732740372916869)
              ·
                refine ⟨85635184637388819921913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456720984732740372916869 85635184637388819921913)
                ·
                  rfl

theorem cell19_281431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_281431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281431 prefixEnd_281431 := by exact prefixLift 281431
  have htrace : WordTrace (prefixWord ++ tailWord_281431) baseStart_281431 baseEnd_281431 := by
    simpa [prefixWord, tailWord_281431, baseEnd_281431] using wordTrace_append hprefix tailTrace_281431
  have hstable : (prefixWord ++ tailWord_281431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281431).length < 2 ^ (prefixWord ++ tailWord_281431).sum := by decide
  have hdescent : baseEnd_281431 < baseStart_281431 := by decide
  rcases family_descends (prefixWord ++ tailWord_281431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281448 : List Nat := [2, 1, 4, 2, 1, 3, 3, 3]
def baseStart_281448 : Nat := 118140960795 + 281448 * 2 ^ 59
def prefixEnd_281448 : Nat := 4983230072969 + 3 ^ 40 * 281448 * 2
def baseEnd_281448 : Nat := 85640357479537817544089

theorem tailTrace_281448 : CollatzResearch.WordTrace tailWord_281448 prefixEnd_281448 85640357479537817544089 := by
  unfold tailWord_281448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132625942184719168330499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6843501256246292224440665 5132625942184719168330499)
  ·
    refine ⟨7698938913277078752495749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5132625942184719168330499 7698938913277078752495749)
    ·
      refine ⟨1443551046239452266092953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7698938913277078752495749 1443551046239452266092953)
      ·
        refine ⟨1082663284679589199569715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1443551046239452266092953 1082663284679589199569715)
        ·
          refine ⟨1623994927019383799354573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082663284679589199569715 1623994927019383799354573)
          ·
            refine ⟨608998097632268924757965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1623994927019383799354573 608998097632268924757965)
            ·
              refine ⟨228374286612100846784237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 608998097632268924757965 228374286612100846784237)
              ·
                refine ⟨85640357479537817544089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228374286612100846784237 85640357479537817544089)
                ·
                  rfl

theorem cell19_281448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_281448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281448 prefixEnd_281448 := by exact prefixLift 281448
  have htrace : WordTrace (prefixWord ++ tailWord_281448) baseStart_281448 baseEnd_281448 := by
    simpa [prefixWord, tailWord_281448, baseEnd_281448] using wordTrace_append hprefix tailTrace_281448
  have hstable : (prefixWord ++ tailWord_281448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281448).length < 2 ^ (prefixWord ++ tailWord_281448).sum := by decide
  have hdescent : baseEnd_281448 < baseStart_281448 := by decide
  rcases family_descends (prefixWord ++ tailWord_281448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281505 : List Nat := [1, 2, 3, 4, 1, 1, 4, 3]
def baseStart_281505 : Nat := 118140960795 + 281505 * 2 ^ 59
def prefixEnd_281505 : Nat := 4983230072969 + 3 ^ 40 * 281505 * 2
def baseEnd_281505 : Nat := 85657701714978574277267

theorem tailTrace_281505 : CollatzResearch.WordTrace tailWord_281505 prefixEnd_281505 85657701714978574277267 := by
  unfold tailWord_281505
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267330845162937071485969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6844887230108624714323979 10267330845162937071485969)
  ·
    refine ⟨7700498133872202803614477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10267330845162937071485969 7700498133872202803614477)
    ·
      refine ⟨2887686800202076051355429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7700498133872202803614477 2887686800202076051355429)
      ·
        refine ⟨541441275037889259629143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2887686800202076051355429 541441275037889259629143)
        ·
          refine ⟨812161912556833889443715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541441275037889259629143 812161912556833889443715)
          ·
            refine ⟨1218242868835250834165573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812161912556833889443715 1218242868835250834165573)
            ·
              refine ⟨228420537906609531406045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1218242868835250834165573 228420537906609531406045)
              ·
                refine ⟨85657701714978574277267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228420537906609531406045 85657701714978574277267)
                ·
                  rfl

theorem cell19_281505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_281505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281505 prefixEnd_281505 := by exact prefixLift 281505
  have htrace : WordTrace (prefixWord ++ tailWord_281505) baseStart_281505 baseEnd_281505 := by
    simpa [prefixWord, tailWord_281505, baseEnd_281505] using wordTrace_append hprefix tailTrace_281505
  have hstable : (prefixWord ++ tailWord_281505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281505).length < 2 ^ (prefixWord ++ tailWord_281505).sum := by decide
  have hdescent : baseEnd_281505 < baseStart_281505 := by decide
  rcases family_descends (prefixWord ++ tailWord_281505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281507 : List Nat := [1, 1, 1, 4, 1, 2, 6, 3]
def baseStart_281507 : Nat := 118140960795 + 281507 * 2 ^ 59
def prefixEnd_281507 : Nat := 4983230072969 + 3 ^ 40 * 281507 * 2
def baseEnd_281507 : Nat := 85658310284643162232817

theorem tailTrace_281507 : CollatzResearch.WordTrace tailWord_281507 prefixEnd_281507 85658310284643162232817 := by
  unfold tailWord_281507
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267403791155691413058775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6844935860770460942039183 10267403791155691413058775)
  ·
    refine ⟨15401105686733537119588163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10267403791155691413058775 15401105686733537119588163)
    ·
      refine ⟨23101658530100305679382245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15401105686733537119588163 23101658530100305679382245)
      ·
        refine ⟨4331560974393807314884171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23101658530100305679382245 4331560974393807314884171)
        ·
          refine ⟨6497341461590710972326257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331560974393807314884171 6497341461590710972326257)
          ·
            refine ⟨4873006096193033229244693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6497341461590710972326257 4873006096193033229244693)
            ·
              refine ⟨228422160759048432620845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4873006096193033229244693 228422160759048432620845)
              ·
                refine ⟨85658310284643162232817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228422160759048432620845 85658310284643162232817)
                ·
                  rfl

theorem cell19_281507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_281507 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281507 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281507 prefixEnd_281507 := by exact prefixLift 281507
  have htrace : WordTrace (prefixWord ++ tailWord_281507) baseStart_281507 baseEnd_281507 := by
    simpa [prefixWord, tailWord_281507, baseEnd_281507] using wordTrace_append hprefix tailTrace_281507
  have hstable : (prefixWord ++ tailWord_281507).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281507).length < 2 ^ (prefixWord ++ tailWord_281507).sum := by decide
  have hdescent : baseEnd_281507 < baseStart_281507 := by decide
  rcases family_descends (prefixWord ++ tailWord_281507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281524 : List Nat := [2, 5, 2, 1, 1, 1, 7]
def baseStart_281524 : Nat := 118140960795 + 281524 * 2 ^ 59
def prefixEnd_281524 : Nat := 4983230072969 + 3 ^ 40 * 281524 * 2
def baseEnd_281524 : Nat := 28554494375597386618331

theorem tailTrace_281524 : CollatzResearch.WordTrace tailWord_281524 prefixEnd_281524 28554494375597386618331 := by
  unfold tailWord_281524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134011916047051658213813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6845349221396068877618417 5134011916047051658213813)
  ·
    refine ⟨481313617129411092957545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5134011916047051658213813 481313617129411092957545)
    ·
      refine ⟨360985212847058319718159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 481313617129411092957545 360985212847058319718159)
      ·
        refine ⟨541477819270587479577239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360985212847058319718159 541477819270587479577239)
        ·
          refine ⟨812216728905881219365859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541477819270587479577239 812216728905881219365859)
          ·
            refine ⟨1218325093358821829048789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812216728905881219365859 1218325093358821829048789)
            ·
              refine ⟨28554494375597386618331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1218325093358821829048789 28554494375597386618331)
              ·
                rfl

theorem cell19_281524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_281524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281524 prefixEnd_281524 := by exact prefixLift 281524
  have htrace : WordTrace (prefixWord ++ tailWord_281524) baseStart_281524 baseEnd_281524 := by
    simpa [prefixWord, tailWord_281524, baseEnd_281524] using wordTrace_append hprefix tailTrace_281524
  have hstable : (prefixWord ++ tailWord_281524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281524).length < 2 ^ (prefixWord ++ tailWord_281524).sum := by decide
  have hdescent : baseEnd_281524 < baseStart_281524 := by decide
  rcases family_descends (prefixWord ++ tailWord_281524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281528 : List Nat := [2, 1, 2, 1, 2, 4, 7]
def baseStart_281528 : Nat := 118140960795 + 281528 * 2 ^ 59
def prefixEnd_281528 : Nat := 4983230072969 + 3 ^ 40 * 281528 * 2
def baseEnd_281528 : Nat := 28554900088707111922031

theorem tailTrace_281528 : CollatzResearch.WordTrace tailWord_281528 prefixEnd_281528 28554900088707111922031 := by
  unfold tailWord_281528
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134084862039805999786619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6845446482719741333048825 5134084862039805999786619)
  ·
    refine ⟨7701127293059708999679929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5134084862039805999786619 7701127293059708999679929)
    ·
      refine ⟨5775845469794781749759947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7701127293059708999679929 5775845469794781749759947)
      ·
        refine ⟨8663768204692172624639921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5775845469794781749759947 8663768204692172624639921)
        ·
          refine ⟨6497826153519129468479941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8663768204692172624639921 6497826153519129468479941)
          ·
            refine ⟨1218342403784836775339989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6497826153519129468479941 1218342403784836775339989)
            ·
              refine ⟨28554900088707111922031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1218342403784836775339989 28554900088707111922031)
              ·
                rfl

theorem cell19_281528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_281528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281528 prefixEnd_281528 := by exact prefixLift 281528
  have htrace : WordTrace (prefixWord ++ tailWord_281528) baseStart_281528 baseEnd_281528 := by
    simpa [prefixWord, tailWord_281528, baseEnd_281528] using wordTrace_append hprefix tailTrace_281528
  have hstable : (prefixWord ++ tailWord_281528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281528).length < 2 ^ (prefixWord ++ tailWord_281528).sum := by decide
  have hdescent : baseEnd_281528 < baseStart_281528 := by decide
  rcases family_descends (prefixWord ++ tailWord_281528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281547 : List Nat := [1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_281547 : Nat := 118140960795 + 281547 * 2 ^ 59
def prefixEnd_281547 : Nat := 4983230072969 + 3 ^ 40 * 281547 * 2
def baseEnd_281547 : Nat := 85670481677934921343819

theorem tailTrace_281547 : CollatzResearch.WordTrace tailWord_281547 prefixEnd_281547 85670481677934921343819 := by
  unfold tailWord_281547
  simp only [CollatzResearch.WordTrace]
  refine ⟨10268862711010778244514895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6845908474007185496343263 10268862711010778244514895)
  ·
    refine ⟨15403294066516167366772343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10268862711010778244514895 15403294066516167366772343)
    ·
      refine ⟨23104941099774251050158515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15403294066516167366772343 23104941099774251050158515)
      ·
        refine ⟨34657411649661376575237773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23104941099774251050158515 34657411649661376575237773)
        ·
          refine ⟨12996529368623016215714165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34657411649661376575237773 12996529368623016215714165)
          ·
            refine ⟨1218424628308407770223203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12996529368623016215714165 1218424628308407770223203)
            ·
              refine ⟨1827636942462611655334805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218424628308407770223203 1827636942462611655334805)
              ·
                refine ⟨85670481677934921343819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1827636942462611655334805 85670481677934921343819)
                ·
                  rfl

theorem cell19_281547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_281547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281547 prefixEnd_281547 := by exact prefixLift 281547
  have htrace : WordTrace (prefixWord ++ tailWord_281547) baseStart_281547 baseEnd_281547 := by
    simpa [prefixWord, tailWord_281547, baseEnd_281547] using wordTrace_append hprefix tailTrace_281547
  have hstable : (prefixWord ++ tailWord_281547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281547).length < 2 ^ (prefixWord ++ tailWord_281547).sum := by decide
  have hdescent : baseEnd_281547 < baseStart_281547 := by decide
  rcases family_descends (prefixWord ++ tailWord_281547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281585 : List Nat := [1, 2, 2, 2, 4, 8]
def baseStart_281585 : Nat := 118140960795 + 281585 * 2 ^ 59
def prefixEnd_281585 : Nat := 4983230072969 + 3 ^ 40 * 281585 * 2
def baseEnd_281585 : Nat := 9520227166840232499919

theorem tailTrace_281585 : CollatzResearch.WordTrace tailWord_281585 prefixEnd_281585 9520227166840232499919 := by
  unfold tailWord_281585
  simp only [CollatzResearch.WordTrace]
  refine ⟨10270248684873110734398209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6846832456582073822932139 10270248684873110734398209)
  ·
    refine ⟨7702686513654833050798657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10270248684873110734398209 7702686513654833050798657)
    ·
      refine ⟨5777014885241124788098993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7702686513654833050798657 5777014885241124788098993)
      ·
        refine ⟨4332761163930843591074245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5777014885241124788098993 4332761163930843591074245)
        ·
          refine ⟨812392718237033173326421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4332761163930843591074245 812392718237033173326421)
          ·
            refine ⟨9520227166840232499919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 812392718237033173326421 9520227166840232499919)
            ·
              rfl

theorem cell19_281585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_281585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281585 prefixEnd_281585 := by exact prefixLift 281585
  have htrace : WordTrace (prefixWord ++ tailWord_281585) baseStart_281585 baseEnd_281585 := by
    simpa [prefixWord, tailWord_281585, baseEnd_281585] using wordTrace_append hprefix tailTrace_281585
  have hstable : (prefixWord ++ tailWord_281585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281585).length < 2 ^ (prefixWord ++ tailWord_281585).sum := by decide
  have hdescent : baseEnd_281585 < baseStart_281585 := by decide
  rcases family_descends (prefixWord ++ tailWord_281585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281598 : List Nat := [4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_281598 : Nat := 118140960795 + 281598 * 2 ^ 59
def prefixEnd_281598 : Nat := 4983230072969 + 3 ^ 40 * 281598 * 2
def baseEnd_281598 : Nat := 85686000204381914210347

theorem tailTrace_281598 : CollatzResearch.WordTrace tailWord_281598 prefixEnd_281598 85686000204381914210347 := by
  unfold tailWord_281598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283840354228251744327681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6847148555884009303080965 1283840354228251744327681)
  ·
    refine ⟨962880265671188808245761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1283840354228251744327681 962880265671188808245761)
    ·
      refine ⟨722160199253391606184321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 962880265671188808245761 722160199253391606184321)
      ·
        refine ⟨541620149440043704638241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 722160199253391606184321 541620149440043704638241)
        ·
          refine ⟨406215112080032778478681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541620149440043704638241 406215112080032778478681)
          ·
            refine ⟨304661334060024583859011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406215112080032778478681 304661334060024583859011)
            ·
              refine ⟨456992001090036875788517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304661334060024583859011 456992001090036875788517)
              ·
                refine ⟨85686000204381914210347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456992001090036875788517 85686000204381914210347)
                ·
                  rfl

theorem cell19_281598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_281598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281598 prefixEnd_281598 := by exact prefixLift 281598
  have htrace : WordTrace (prefixWord ++ tailWord_281598) baseStart_281598 baseEnd_281598 := by
    simpa [prefixWord, tailWord_281598, baseEnd_281598] using wordTrace_append hprefix tailTrace_281598
  have hstable : (prefixWord ++ tailWord_281598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281598).length < 2 ^ (prefixWord ++ tailWord_281598).sum := by decide
  have hdescent : baseEnd_281598 < baseStart_281598 := by decide
  rcases family_descends (prefixWord ++ tailWord_281598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281693 : List Nat := [1, 4, 4, 1, 3, 1, 5]
def baseStart_281693 : Nat := 118140960795 + 281693 * 2 ^ 59
def prefixEnd_281693 : Nat := 4983230072969 + 3 ^ 40 * 281693 * 2
def baseEnd_281693 : Nat := 28571635754483280699659

theorem tailTrace_281693 : CollatzResearch.WordTrace tailWord_281693 prefixEnd_281693 28571635754483280699659 := by
  unfold tailWord_281693
  simp only [CollatzResearch.WordTrace]
  refine ⟨10274187768481845179329733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6849458512321230119553155 10274187768481845179329733)
  ·
    refine ⟨1926410206590345971124325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10274187768481845179329733 1926410206590345971124325)
    ·
      refine ⟨361201913735689869585811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1926410206590345971124325 361201913735689869585811)
      ·
        refine ⟨541802870603534804378717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361201913735689869585811 541802870603534804378717)
        ·
          refine ⟨203176076476325551642019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 541802870603534804378717 203176076476325551642019)
          ·
            refine ⟨304764114714488327463029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203176076476325551642019 304764114714488327463029)
            ·
              refine ⟨28571635754483280699659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 304764114714488327463029 28571635754483280699659)
              ·
                rfl

theorem cell19_281693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_281693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281693 prefixEnd_281693 := by exact prefixLift 281693
  have htrace : WordTrace (prefixWord ++ tailWord_281693) baseStart_281693 baseEnd_281693 := by
    simpa [prefixWord, tailWord_281693, baseEnd_281693] using wordTrace_append hprefix tailTrace_281693
  have hstable : (prefixWord ++ tailWord_281693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281693).length < 2 ^ (prefixWord ++ tailWord_281693).sum := by decide
  have hdescent : baseEnd_281693 < baseStart_281693 := by decide
  rcases family_descends (prefixWord ++ tailWord_281693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281737 : List Nat := [1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_281737 : Nat := 118140960795 + 281737 * 2 ^ 59
def prefixEnd_281737 : Nat := 4983230072969 + 3 ^ 40 * 281737 * 2
def baseEnd_281737 : Nat := 85728295796070777121079

theorem tailTrace_281737 : CollatzResearch.WordTrace tailWord_281737 prefixEnd_281737 85728295796070777121079 := by
  unfold tailWord_281737
  simp only [CollatzResearch.WordTrace]
  refine ⟨10275792580322440693931465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6850528386881627129287643 10275792580322440693931465)
  ·
    refine ⟨7706844435241830520448599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10275792580322440693931465 7706844435241830520448599)
    ·
      refine ⟨11560266652862745780672899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7706844435241830520448599 11560266652862745780672899)
      ·
        refine ⟨17340399979294118671009349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11560266652862745780672899 17340399979294118671009349)
        ·
          refine ⟨3251324996117647250814253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17340399979294118671009349 3251324996117647250814253)
          ·
            refine ⟨1219246873544117719055345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3251324996117647250814253 1219246873544117719055345)
            ·
              refine ⟨914435155158088289291509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1219246873544117719055345 914435155158088289291509)
              ·
                refine ⟨85728295796070777121079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 914435155158088289291509 85728295796070777121079)
                ·
                  rfl

theorem cell19_281737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_281737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281737 prefixEnd_281737 := by exact prefixLift 281737
  have htrace : WordTrace (prefixWord ++ tailWord_281737) baseStart_281737 baseEnd_281737 := by
    simpa [prefixWord, tailWord_281737, baseEnd_281737] using wordTrace_append hprefix tailTrace_281737
  have hstable : (prefixWord ++ tailWord_281737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281737).length < 2 ^ (prefixWord ++ tailWord_281737).sum := by decide
  have hdescent : baseEnd_281737 < baseStart_281737 := by decide
  rcases family_descends (prefixWord ++ tailWord_281737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281756 : List Nat := [2, 2, 3, 2, 1, 9]
def baseStart_281756 : Nat := 118140960795 + 281756 * 2 ^ 59
def prefixEnd_281756 : Nat := 4983230072969 + 3 ^ 40 * 281756 * 2
def baseEnd_281756 : Nat := 9526008578653818077645

theorem tailTrace_281756 : CollatzResearch.WordTrace tailWord_281756 prefixEnd_281756 9526008578653818077645 := by
  unfold tailWord_281756
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138242783626803469436561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6850990378169071292582081 5138242783626803469436561)
  ·
    refine ⟨3853682087720102602077421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5138242783626803469436561 3853682087720102602077421)
    ·
      refine ⟨1445130782895038475779033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3853682087720102602077421 1445130782895038475779033)
      ·
        refine ⟨1083848087171278856834275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1445130782895038475779033 1083848087171278856834275)
        ·
          refine ⟨1625772130756918285251413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083848087171278856834275 1625772130756918285251413)
          ·
            refine ⟨9526008578653818077645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1625772130756918285251413 9526008578653818077645)
            ·
              rfl

theorem cell19_281756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_281756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281756 prefixEnd_281756 := by exact prefixLift 281756
  have htrace : WordTrace (prefixWord ++ tailWord_281756) baseStart_281756 baseEnd_281756 := by
    simpa [prefixWord, tailWord_281756, baseEnd_281756] using wordTrace_append hprefix tailTrace_281756
  have hstable : (prefixWord ++ tailWord_281756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281756).length < 2 ^ (prefixWord ++ tailWord_281756).sum := by decide
  have hdescent : baseEnd_281756 < baseStart_281756 := by decide
  rcases family_descends (prefixWord ++ tailWord_281756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281775 : List Nat := [1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_281775 : Nat := 118140960795 + 281775 * 2 ^ 59
def prefixEnd_281775 : Nat := 4983230072969 + 3 ^ 40 * 281775 * 2
def baseEnd_281775 : Nat := 85739858619697948276531

theorem tailTrace_281775 : CollatzResearch.WordTrace tailWord_281775 prefixEnd_281775 85739858619697948276531 := by
  unfold tailWord_281775
  simp only [CollatzResearch.WordTrace]
  refine ⟨10277178554184773183814779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6851452369456515455876519 10277178554184773183814779)
  ·
    refine ⟨15415767831277159775722169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10277178554184773183814779 15415767831277159775722169)
    ·
      refine ⟨11561825873457869831791627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15415767831277159775722169 11561825873457869831791627)
      ·
        refine ⟨17342738810186804747687441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11561825873457869831791627 17342738810186804747687441)
        ·
          refine ⟨13007054107640103560765581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17342738810186804747687441 13007054107640103560765581)
          ·
            refine ⟨4877645290365038835287093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13007054107640103560765581 4877645290365038835287093)
            ·
              refine ⟨457279245971722390808165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4877645290365038835287093 457279245971722390808165)
              ·
                refine ⟨85739858619697948276531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457279245971722390808165 85739858619697948276531)
                ·
                  rfl

theorem cell19_281775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_281775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281775 prefixEnd_281775 := by exact prefixLift 281775
  have htrace : WordTrace (prefixWord ++ tailWord_281775) baseStart_281775 baseEnd_281775 := by
    simpa [prefixWord, tailWord_281775, baseEnd_281775] using wordTrace_append hprefix tailTrace_281775
  have hstable : (prefixWord ++ tailWord_281775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281775).length < 2 ^ (prefixWord ++ tailWord_281775).sum := by decide
  have hdescent : baseEnd_281775 < baseStart_281775 := by decide
  rcases family_descends (prefixWord ++ tailWord_281775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281790 : List Nat := [4, 2, 1, 1, 3, 2, 3, 3]
def baseStart_281790 : Nat := 118140960795 + 281790 * 2 ^ 59
def prefixEnd_281790 : Nat := 4983230072969 + 3 ^ 40 * 281790 * 2
def baseEnd_281790 : Nat := 85744422892182357943157

theorem tailTrace_281790 : CollatzResearch.WordTrace tailWord_281790 prefixEnd_281790 85744422892182357943157 := by
  unfold tailWord_281790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284715706141303843201353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6851817099420287163740549 1284715706141303843201353)
  ·
    refine ⟨963536779605977882401015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1284715706141303843201353 963536779605977882401015)
    ·
      refine ⟨1445305169408966823601523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963536779605977882401015 1445305169408966823601523)
      ·
        refine ⟨2167957754113450235402285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445305169408966823601523 2167957754113450235402285)
        ·
          refine ⟨812984157792543838275857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2167957754113450235402285 812984157792543838275857)
          ·
            refine ⟨609738118344407878706893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812984157792543838275857 609738118344407878706893)
            ·
              refine ⟨228651794379152954515085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609738118344407878706893 228651794379152954515085)
              ·
                refine ⟨85744422892182357943157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228651794379152954515085 85744422892182357943157)
                ·
                  rfl

theorem cell19_281790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_281790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281790 prefixEnd_281790 := by exact prefixLift 281790
  have htrace : WordTrace (prefixWord ++ tailWord_281790) baseStart_281790 baseEnd_281790 := by
    simpa [prefixWord, tailWord_281790, baseEnd_281790] using wordTrace_append hprefix tailTrace_281790
  have hstable : (prefixWord ++ tailWord_281790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281790).length < 2 ^ (prefixWord ++ tailWord_281790).sum := by decide
  have hdescent : baseEnd_281790 < baseStart_281790 := by decide
  rcases family_descends (prefixWord ++ tailWord_281790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281832 : List Nat := [2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_281832 : Nat := 118140960795 + 281832 * 2 ^ 59
def prefixEnd_281832 : Nat := 4983230072969 + 3 ^ 40 * 281832 * 2
def baseEnd_281832 : Nat := 85757202855138705009709

theorem tailTrace_281832 : CollatzResearch.WordTrace tailWord_281832 prefixEnd_281832 85757202855138705009709 := by
  unfold tailWord_281832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139628757489135959319875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6852838343318847945759833 5139628757489135959319875)
  ·
    refine ⟨7709443136233703938979813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5139628757489135959319875 7709443136233703938979813)
    ·
      refine ⟨1445520588043819488558715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7709443136233703938979813 1445520588043819488558715)
      ·
        refine ⟨2168280882065729232838073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445520588043819488558715 2168280882065729232838073)
        ·
          refine ⟨1626210661549296924628555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2168280882065729232838073 1626210661549296924628555)
          ·
            refine ⟨2439315992323945386942833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626210661549296924628555 2439315992323945386942833)
            ·
              refine ⟨1829486994242959040207125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439315992323945386942833 1829486994242959040207125)
              ·
                refine ⟨85757202855138705009709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1829486994242959040207125 85757202855138705009709)
                ·
                  rfl

theorem cell19_281832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_281832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281832 prefixEnd_281832 := by exact prefixLift 281832
  have htrace : WordTrace (prefixWord ++ tailWord_281832) baseStart_281832 baseEnd_281832 := by
    simpa [prefixWord, tailWord_281832, baseEnd_281832] using wordTrace_append hprefix tailTrace_281832
  have hstable : (prefixWord ++ tailWord_281832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281832).length < 2 ^ (prefixWord ++ tailWord_281832).sum := by decide
  have hdescent : baseEnd_281832 < baseStart_281832 := by decide
  rcases family_descends (prefixWord ++ tailWord_281832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281870 : List Nat := [4, 1, 1, 2, 1, 3, 7]
def baseStart_281870 : Nat := 118140960795 + 281870 * 2 ^ 59
def prefixEnd_281870 : Nat := 4983230072969 + 3 ^ 40 * 281870 * 2
def baseEnd_281870 : Nat := 28589588559588625388387

theorem tailTrace_281870 : CollatzResearch.WordTrace tailWord_281870 prefixEnd_281870 28589588559588625388387 := by
  unfold tailWord_281870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285080436105075551065383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6853762325893736272348709 1285080436105075551065383)
  ·
    refine ⟨1927620654157613326598075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1285080436105075551065383 1927620654157613326598075)
    ·
      refine ⟨2891430981236419989897113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1927620654157613326598075 2891430981236419989897113)
      ·
        refine ⟨2168573235927314992422835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2891430981236419989897113 2168573235927314992422835)
        ·
          refine ⟨3252859853890972488634253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168573235927314992422835 3252859853890972488634253)
          ·
            refine ⟨1219822445209114683237845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3252859853890972488634253 1219822445209114683237845)
            ·
              refine ⟨28589588559588625388387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1219822445209114683237845 28589588559588625388387)
              ·
                rfl

theorem cell19_281870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_281870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281870 prefixEnd_281870 := by exact prefixLift 281870
  have htrace : WordTrace (prefixWord ++ tailWord_281870) baseStart_281870 baseEnd_281870 := by
    simpa [prefixWord, tailWord_281870, baseEnd_281870] using wordTrace_append hprefix tailTrace_281870
  have hstable : (prefixWord ++ tailWord_281870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281870).length < 2 ^ (prefixWord ++ tailWord_281870).sum := by decide
  have hdescent : baseEnd_281870 < baseStart_281870 := by decide
  rcases family_descends (prefixWord ++ tailWord_281870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281887 : List Nat := [1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_281887 : Nat := 118140960795 + 281887 * 2 ^ 59
def prefixEnd_281887 : Nat := 4983230072969 + 3 ^ 40 * 281887 * 2
def baseEnd_281887 : Nat := 85773938520914873787337

theorem tailTrace_281887 : CollatzResearch.WordTrace tailWord_281887 prefixEnd_281887 85773938520914873787337 := by
  unfold tailWord_281887
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281263529779016311891915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6854175686519344207927943 10281263529779016311891915)
  ·
    refine ⟨15421895294668524467837873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10281263529779016311891915 15421895294668524467837873)
    ·
      refine ⟨11566421471001393350878405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15421895294668524467837873 11566421471001393350878405)
      ·
        refine ⟨2168704025812761253289701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11566421471001393350878405 2168704025812761253289701)
        ·
          refine ⟨406632004839892734991819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2168704025812761253289701 406632004839892734991819)
          ·
            refine ⟨609948007259839102487729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406632004839892734991819 609948007259839102487729)
            ·
              refine ⟨457461005444879326865797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609948007259839102487729 457461005444879326865797)
              ·
                refine ⟨85773938520914873787337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457461005444879326865797 85773938520914873787337)
                ·
                  rfl

theorem cell19_281887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_281887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281887 prefixEnd_281887 := by exact prefixLift 281887
  have htrace : WordTrace (prefixWord ++ tailWord_281887) baseStart_281887 baseEnd_281887 := by
    simpa [prefixWord, tailWord_281887, baseEnd_281887] using wordTrace_append hprefix tailTrace_281887
  have hstable : (prefixWord ++ tailWord_281887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281887).length < 2 ^ (prefixWord ++ tailWord_281887).sum := by decide
  have hdescent : baseEnd_281887 < baseStart_281887 := by decide
  rcases family_descends (prefixWord ++ tailWord_281887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281946 : List Nat := [3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_281946 : Nat := 118140960795 + 281946 * 2 ^ 59
def prefixEnd_281946 : Nat := 4983230072969 + 3 ^ 40 * 281946 * 2
def baseEnd_281946 : Nat := 85791891326020218476065

theorem tailTrace_281946 : CollatzResearch.WordTrace tailWord_281946 prefixEnd_281946 85791891326020218476065 := by
  unfold tailWord_281946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570853859141317347072423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6855610291043512925526461 2570853859141317347072423)
  ·
    refine ⟨3856280788711976020608635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2570853859141317347072423 3856280788711976020608635)
    ·
      refine ⟨5784421183067964030912953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856280788711976020608635 5784421183067964030912953)
      ·
        refine ⟨4338315887300973023184715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5784421183067964030912953 4338315887300973023184715)
        ·
          refine ⟨6507473830951459534777073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338315887300973023184715 6507473830951459534777073)
          ·
            refine ⟨4880605373213594651082805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6507473830951459534777073 4880605373213594651082805)
            ·
              refine ⟨457556753738774498539013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4880605373213594651082805 457556753738774498539013)
              ·
                refine ⟨85791891326020218476065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457556753738774498539013 85791891326020218476065)
                ·
                  rfl

theorem cell19_281946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_281946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_281946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_281946 prefixEnd_281946 := by exact prefixLift 281946
  have htrace : WordTrace (prefixWord ++ tailWord_281946) baseStart_281946 baseEnd_281946 := by
    simpa [prefixWord, tailWord_281946, baseEnd_281946] using wordTrace_append hprefix tailTrace_281946
  have hstable : (prefixWord ++ tailWord_281946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281946).length < 2 ^ (prefixWord ++ tailWord_281946).sum := by decide
  have hdescent : baseEnd_281946 < baseStart_281946 := by decide
  rcases family_descends (prefixWord ++ tailWord_281946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282014 : List Nat := [4, 3, 1, 2, 3, 1, 2, 3]
def baseStart_282014 : Nat := 118140960795 + 282014 * 2 ^ 59
def prefixEnd_282014 : Nat := 4983230072969 + 3 ^ 40 * 282014 * 2
def baseEnd_282014 : Nat := 85812582694616208964769

theorem tailTrace_282014 : CollatzResearch.WordTrace tailWord_282014 prefixEnd_282014 85812582694616208964769 := by
  unfold tailWord_282014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285736950039864625220637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6857263733545944667843397 1285736950039864625220637)
  ·
    refine ⟨482151356264949234457739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1285736950039864625220637 482151356264949234457739)
    ·
      refine ⟨723227034397423851686609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482151356264949234457739 723227034397423851686609)
      ·
        refine ⟨542420275798067888764957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 723227034397423851686609 542420275798067888764957)
        ·
          refine ⟨203407603424275458286859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542420275798067888764957 203407603424275458286859)
          ·
            refine ⟨305111405136413187430289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203407603424275458286859 305111405136413187430289)
            ·
              refine ⟨228833553852309890572717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305111405136413187430289 228833553852309890572717)
              ·
                refine ⟨85812582694616208964769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228833553852309890572717 85812582694616208964769)
                ·
                  rfl

theorem cell19_282014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_282014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282014 prefixEnd_282014 := by exact prefixLift 282014
  have htrace : WordTrace (prefixWord ++ tailWord_282014) baseStart_282014 baseEnd_282014 := by
    simpa [prefixWord, tailWord_282014, baseEnd_282014] using wordTrace_append hprefix tailTrace_282014
  have hstable : (prefixWord ++ tailWord_282014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282014).length < 2 ^ (prefixWord ++ tailWord_282014).sum := by decide
  have hdescent : baseEnd_282014 < baseStart_282014 := by decide
  rcases family_descends (prefixWord ++ tailWord_282014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282018 : List Nat := [3, 3, 1, 2, 1, 4, 2, 3]
def baseStart_282018 : Nat := 118140960795 + 282018 * 2 ^ 59
def prefixEnd_282018 : Nat := 4983230072969 + 3 ^ 40 * 282018 * 2
def baseEnd_282018 : Nat := 85813799833945384875869

theorem tailTrace_282018 : CollatzResearch.WordTrace tailWord_282018 prefixEnd_282018 85813799833945384875869 := by
  unfold tailWord_282018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571510373076106421227677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6857360994869617123273805 2571510373076106421227677)
  ·
    refine ⟨964316389903539907960379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2571510373076106421227677 964316389903539907960379)
    ·
      refine ⟨1446474584855309861940569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964316389903539907960379 1446474584855309861940569)
      ·
        refine ⟨1084855938641482396455427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1446474584855309861940569 1084855938641482396455427)
        ·
          refine ⟨1627283907962223594683141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084855938641482396455427 1627283907962223594683141)
          ·
            refine ⟨305115732742916924003089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1627283907962223594683141 305115732742916924003089)
            ·
              refine ⟨228836799557187693002317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305115732742916924003089 228836799557187693002317)
              ·
                refine ⟨85813799833945384875869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228836799557187693002317 85813799833945384875869)
                ·
                  rfl

theorem cell19_282018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_282018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282018 prefixEnd_282018 := by exact prefixLift 282018
  have htrace : WordTrace (prefixWord ++ tailWord_282018) baseStart_282018 baseEnd_282018 := by
    simpa [prefixWord, tailWord_282018, baseEnd_282018] using wordTrace_append hprefix tailTrace_282018
  have hstable : (prefixWord ++ tailWord_282018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282018).length < 2 ^ (prefixWord ++ tailWord_282018).sum := by decide
  have hdescent : baseEnd_282018 < baseStart_282018 := by decide
  rcases family_descends (prefixWord ++ tailWord_282018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282060 : List Nat := [2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_282060 : Nat := 118140960795 + 282060 * 2 ^ 59
def prefixEnd_282060 : Nat := 4983230072969 + 3 ^ 40 * 282060 * 2
def baseEnd_282060 : Nat := 85826579796901731942421

theorem tailTrace_282060 : CollatzResearch.WordTrace tailWord_282060 prefixEnd_282060 85826579796901731942421 := by
  unfold tailWord_282060
  simp only [CollatzResearch.WordTrace]
  refine ⟨5143786679076133428969817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6858382238768177905293089 5143786679076133428969817)
  ·
    refine ⟨3857840009307100071727363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5143786679076133428969817 3857840009307100071727363)
    ·
      refine ⟨5786760013960650107591045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3857840009307100071727363 5786760013960650107591045)
      ·
        refine ⟨1085017502617621895173321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5786760013960650107591045 1085017502617621895173321)
        ·
          refine ⟨813763126963216421379991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085017502617621895173321 813763126963216421379991)
          ·
            refine ⟨1220644690444824632069987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813763126963216421379991 1220644690444824632069987)
            ·
              refine ⟨1830967035667236948104981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220644690444824632069987 1830967035667236948104981)
              ·
                refine ⟨85826579796901731942421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1830967035667236948104981 85826579796901731942421)
                ·
                  rfl

theorem cell19_282060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_282060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282060 prefixEnd_282060 := by exact prefixLift 282060
  have htrace : WordTrace (prefixWord ++ tailWord_282060) baseStart_282060 baseEnd_282060 := by
    simpa [prefixWord, tailWord_282060, baseEnd_282060] using wordTrace_append hprefix tailTrace_282060
  have hstable : (prefixWord ++ tailWord_282060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282060).length < 2 ^ (prefixWord ++ tailWord_282060).sum := by decide
  have hdescent : baseEnd_282060 < baseStart_282060 := by decide
  rcases family_descends (prefixWord ++ tailWord_282060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282098 : List Nat := [3, 2, 1, 4, 1, 8]
def baseStart_282098 : Nat := 118140960795 + 282098 * 2 ^ 59
def prefixEnd_282098 : Nat := 4983230072969 + 3 ^ 40 * 282098 * 2
def baseEnd_282098 : Nat := 9537571402280989233097

theorem tailTrace_282098 : CollatzResearch.WordTrace tailWord_282098 prefixEnd_282098 9537571402280989233097 := by
  unfold tailWord_282098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572239833003649836955737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6859306221343066231881965 2572239833003649836955737)
  ·
    refine ⟨1929179874752737377716803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2572239833003649836955737 1929179874752737377716803)
    ·
      refine ⟨2893769812129106066575205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1929179874752737377716803 2893769812129106066575205)
      ·
        refine ⟨542581839774207387482851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2893769812129106066575205 542581839774207387482851)
        ·
          refine ⟨813872759661311081224277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542581839774207387482851 813872759661311081224277)
          ·
            refine ⟨9537571402280989233097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 813872759661311081224277 9537571402280989233097)
            ·
              rfl

theorem cell19_282098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_282098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282098 prefixEnd_282098 := by exact prefixLift 282098
  have htrace : WordTrace (prefixWord ++ tailWord_282098) baseStart_282098 baseEnd_282098 := by
    simpa [prefixWord, tailWord_282098, baseEnd_282098] using wordTrace_append hprefix tailTrace_282098
  have hstable : (prefixWord ++ tailWord_282098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282098).length < 2 ^ (prefixWord ++ tailWord_282098).sum := by decide
  have hdescent : baseEnd_282098 < baseStart_282098 := by decide
  rcases family_descends (prefixWord ++ tailWord_282098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282113 : List Nat := [1, 2, 4, 1, 5, 1, 1, 4]
def baseStart_282113 : Nat := 118140960795 + 282113 * 2 ^ 59
def prefixEnd_282113 : Nat := 4983230072969 + 3 ^ 40 * 282113 * 2
def baseEnd_282113 : Nat := 85842706893013312764499

theorem tailTrace_282113 : CollatzResearch.WordTrace tailWord_282113 prefixEnd_282113 85842706893013312764499 := by
  unfold tailWord_282113
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289506426960256909618993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6859670951306837939745995 10289506426960256909618993)
  ·
    refine ⟨7717129820220192682214245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10289506426960256909618993 7717129820220192682214245)
    ·
      refine ⟨1446961841291286127915171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7717129820220192682214245 1446961841291286127915171)
      ·
        refine ⟨2170442761936929191872757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446961841291286127915171 2170442761936929191872757)
        ·
          refine ⟨203479008931587111738071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2170442761936929191872757 203479008931587111738071)
          ·
            refine ⟨305218513397380667607107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203479008931587111738071 305218513397380667607107)
            ·
              refine ⟨457827770096071001410661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305218513397380667607107 457827770096071001410661)
              ·
                refine ⟨85842706893013312764499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457827770096071001410661 85842706893013312764499)
                ·
                  rfl

theorem cell19_282113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_282113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282113 prefixEnd_282113 := by exact prefixLift 282113
  have htrace : WordTrace (prefixWord ++ tailWord_282113) baseStart_282113 baseEnd_282113 := by
    simpa [prefixWord, tailWord_282113, baseEnd_282113] using wordTrace_append hprefix tailTrace_282113
  have hstable : (prefixWord ++ tailWord_282113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282113).length < 2 ^ (prefixWord ++ tailWord_282113).sum := by decide
  have hdescent : baseEnd_282113 < baseStart_282113 := by decide
  rcases family_descends (prefixWord ++ tailWord_282113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282176 : List Nat := [2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_282176 : Nat := 118140960795 + 282176 * 2 ^ 59
def prefixEnd_282176 : Nat := 4983230072969 + 3 ^ 40 * 282176 * 2
def baseEnd_282176 : Nat := 85861876837447833364327

theorem tailTrace_282176 : CollatzResearch.WordTrace tailWord_282176 prefixEnd_282176 85861876837447833364327 := by
  unfold tailWord_282176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5145902112866009334581191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6861202817154679112774921 5145902112866009334581191)
  ·
    refine ⟨7718853169299014001871787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5145902112866009334581191 7718853169299014001871787)
    ·
      refine ⟨11578279753948521002807681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7718853169299014001871787 11578279753948521002807681)
      ·
        refine ⟨8683709815461390752105761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11578279753948521002807681 8683709815461390752105761)
        ·
          refine ⟨6512782361596043064079321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8683709815461390752105761 6512782361596043064079321)
          ·
            refine ⟨4884586771197032298059491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6512782361596043064079321 4884586771197032298059491)
            ·
              refine ⟨7326880156795548447089237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884586771197032298059491 7326880156795548447089237)
              ·
                refine ⟨85861876837447833364327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7326880156795548447089237 85861876837447833364327)
                ·
                  rfl

theorem cell19_282176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_282176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282176 prefixEnd_282176 := by exact prefixLift 282176
  have htrace : WordTrace (prefixWord ++ tailWord_282176) baseStart_282176 baseEnd_282176 := by
    simpa [prefixWord, tailWord_282176, baseEnd_282176] using wordTrace_append hprefix tailTrace_282176
  have hstable : (prefixWord ++ tailWord_282176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282176).length < 2 ^ (prefixWord ++ tailWord_282176).sum := by decide
  have hdescent : baseEnd_282176 < baseStart_282176 := by decide
  rcases family_descends (prefixWord ++ tailWord_282176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282212 : List Nat := [2, 3, 1, 1, 2, 5, 5]
def baseStart_282212 : Nat := 118140960795 + 282212 * 2 ^ 59
def prefixEnd_282212 : Nat := 4983230072969 + 3 ^ 40 * 282212 * 2
def baseEnd_282212 : Nat := 28624277030470138854743

theorem tailTrace_282212 : CollatzResearch.WordTrace tailWord_282212 prefixEnd_282212 28624277030470138854743 := by
  unfold tailWord_282212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146558626800798408736445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6862078169067731211648593 5146558626800798408736445)
  ·
    refine ⟨1929959485050299403276167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5146558626800798408736445 1929959485050299403276167)
    ·
      refine ⟨2894939227575449104914251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1929959485050299403276167 2894939227575449104914251)
      ·
        refine ⟨4342408841363173657371377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894939227575449104914251 4342408841363173657371377)
        ·
          refine ⟨3256806631022380243028533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4342408841363173657371377 3256806631022380243028533)
          ·
            refine ⟨305325621658348147783925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3256806631022380243028533 305325621658348147783925)
            ·
              refine ⟨28624277030470138854743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 305325621658348147783925 28624277030470138854743)
              ·
                rfl

theorem cell19_282212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_282212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282212 prefixEnd_282212 := by exact prefixLift 282212
  have htrace : WordTrace (prefixWord ++ tailWord_282212) baseStart_282212 baseEnd_282212 := by
    simpa [prefixWord, tailWord_282212, baseEnd_282212] using wordTrace_append hprefix tailTrace_282212
  have hstable : (prefixWord ++ tailWord_282212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282212).length < 2 ^ (prefixWord ++ tailWord_282212).sum := by decide
  have hdescent : baseEnd_282212 < baseStart_282212 := by decide
  rcases family_descends (prefixWord ++ tailWord_282212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282229 : List Nat := [1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_282229 : Nat := 118140960795 + 282229 * 2 ^ 59
def prefixEnd_282229 : Nat := 4983230072969 + 3 ^ 40 * 282229 * 2
def baseEnd_282229 : Nat := 85878003933559414186405

theorem tailTrace_282229 : CollatzResearch.WordTrace tailWord_282229 prefixEnd_282229 85878003933559414186405 := by
  unfold tailWord_282229
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293737294540008720841741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6862491529693339147227827 10293737294540008720841741)
  ·
    refine ⟨3860151485452503270315653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10293737294540008720841741 3860151485452503270315653)
    ·
      refine ⟨723778403522344363184185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3860151485452503270315653 723778403522344363184185)
      ·
        refine ⟨542833802641758272388139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 723778403522344363184185 542833802641758272388139)
        ·
          refine ⟨814250703962637408582209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542833802641758272388139 814250703962637408582209)
          ·
            refine ⟨610688027971978056436657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 814250703962637408582209 610688027971978056436657)
            ·
              refine ⟨458016020978983542327493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610688027971978056436657 458016020978983542327493)
              ·
                refine ⟨85878003933559414186405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458016020978983542327493 85878003933559414186405)
                ·
                  rfl

theorem cell19_282229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_282229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282229 prefixEnd_282229 := by exact prefixLift 282229
  have htrace : WordTrace (prefixWord ++ tailWord_282229) baseStart_282229 baseEnd_282229 := by
    simpa [prefixWord, tailWord_282229, baseEnd_282229] using wordTrace_append hprefix tailTrace_282229
  have hstable : (prefixWord ++ tailWord_282229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282229).length < 2 ^ (prefixWord ++ tailWord_282229).sum := by decide
  have hdescent : baseEnd_282229 < baseStart_282229 := by decide
  rcases family_descends (prefixWord ++ tailWord_282229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282250 : List Nat := [3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_282250 : Nat := 118140960795 + 282250 * 2 ^ 59
def prefixEnd_282250 : Nat := 4983230072969 + 3 ^ 40 * 282250 * 2
def baseEnd_282250 : Nat := 85884393915037587719681

theorem tailTrace_282250 : CollatzResearch.WordTrace tailWord_282250 prefixEnd_282250 85884393915037587719681 := by
  unfold tailWord_282250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2573625806865982326839051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6863002151642619538237469 2573625806865982326839051)
  ·
    refine ⟨3860438710298973490258577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2573625806865982326839051 3860438710298973490258577)
    ·
      refine ⟨2895329032724230117693933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3860438710298973490258577 2895329032724230117693933)
      ·
        refine ⟨1085748387271586294135225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2895329032724230117693933 1085748387271586294135225)
        ·
          refine ⟨814311290453689720601419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085748387271586294135225 814311290453689720601419)
          ·
            refine ⟨1221466935680534580902129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814311290453689720601419 1221466935680534580902129)
            ·
              refine ⟨916100201760400935676597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1221466935680534580902129 916100201760400935676597)
              ·
                refine ⟨85884393915037587719681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 916100201760400935676597 85884393915037587719681)
                ·
                  rfl

theorem cell19_282250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_282250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282250 prefixEnd_282250 := by exact prefixLift 282250
  have htrace : WordTrace (prefixWord ++ tailWord_282250) baseStart_282250 baseEnd_282250 := by
    simpa [prefixWord, tailWord_282250, baseEnd_282250] using wordTrace_append hprefix tailTrace_282250
  have hstable : (prefixWord ++ tailWord_282250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282250).length < 2 ^ (prefixWord ++ tailWord_282250).sum := by decide
  have hdescent : baseEnd_282250 < baseStart_282250 := by decide
  rcases family_descends (prefixWord ++ tailWord_282250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282252 : List Nat := [2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_282252 : Nat := 118140960795 + 282252 * 2 ^ 59
def prefixEnd_282252 : Nat := 4983230072969 + 3 ^ 40 * 282252 * 2
def baseEnd_282252 : Nat := 85885002484702175675231

theorem tailTrace_282252 : CollatzResearch.WordTrace tailWord_282252 prefixEnd_282252 85885002484702175675231 := by
  unfold tailWord_282252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147288086728341824464505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6863050782304455765952673 5147288086728341824464505)
  ·
    refine ⟨3860466065046256368348379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5147288086728341824464505 3860466065046256368348379)
    ·
      refine ⟨5790699097569384552522569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3860466065046256368348379 5790699097569384552522569)
      ·
        refine ⟨4343024323177038414391927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5790699097569384552522569 4343024323177038414391927)
        ·
          refine ⟨6514536484765557621587891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343024323177038414391927 6514536484765557621587891)
          ·
            refine ⟨9771804727148336432381837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6514536484765557621587891 9771804727148336432381837)
            ·
              refine ⟨3664426772680626162143189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9771804727148336432381837 3664426772680626162143189)
              ·
                refine ⟨85885002484702175675231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3664426772680626162143189 85885002484702175675231)
                ·
                  rfl

theorem cell19_282252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_282252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282252 prefixEnd_282252 := by exact prefixLift 282252
  have htrace : WordTrace (prefixWord ++ tailWord_282252) baseStart_282252 baseEnd_282252 := by
    simpa [prefixWord, tailWord_282252, baseEnd_282252] using wordTrace_append hprefix tailTrace_282252
  have hstable : (prefixWord ++ tailWord_282252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282252).length < 2 ^ (prefixWord ++ tailWord_282252).sum := by decide
  have hdescent : baseEnd_282252 < baseStart_282252 := by decide
  rcases family_descends (prefixWord ++ tailWord_282252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282280 : List Nat := [2, 1, 7, 1, 2, 1, 1, 4]
def baseStart_282280 : Nat := 118140960795 + 282280 * 2 ^ 59
def prefixEnd_282280 : Nat := 4983230072969 + 3 ^ 40 * 282280 * 2
def baseEnd_282280 : Nat := 85893522460006407052933

theorem tailTrace_282280 : CollatzResearch.WordTrace tailWord_282280 prefixEnd_282280 85893522460006407052933 := by
  unfold tailWord_282280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147798708677622215474147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6863731611570162953965529 5147798708677622215474147)
  ·
    refine ⟨7721698063016433323211221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5147798708677622215474147 7721698063016433323211221)
    ·
      refine ⟨180977298351947656012763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7721698063016433323211221 180977298351947656012763)
      ·
        refine ⟨271465947527921484019145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180977298351947656012763 271465947527921484019145)
        ·
          refine ⟨203599460645941113014359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271465947527921484019145 203599460645941113014359)
          ·
            refine ⟨305399190968911669521539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203599460645941113014359 305399190968911669521539)
            ·
              refine ⟨458098786453367504282309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305399190968911669521539 458098786453367504282309)
              ·
                refine ⟨85893522460006407052933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458098786453367504282309 85893522460006407052933)
                ·
                  rfl

theorem cell19_282280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_282280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282280 prefixEnd_282280 := by exact prefixLift 282280
  have htrace : WordTrace (prefixWord ++ tailWord_282280) baseStart_282280 baseEnd_282280 := by
    simpa [prefixWord, tailWord_282280, baseEnd_282280] using wordTrace_append hprefix tailTrace_282280
  have hstable : (prefixWord ++ tailWord_282280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282280).length < 2 ^ (prefixWord ++ tailWord_282280).sum := by decide
  have hdescent : baseEnd_282280 < baseStart_282280 := by decide
  rcases family_descends (prefixWord ++ tailWord_282280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282328 : List Nat := [2, 1, 2, 2, 3, 1, 8]
def baseStart_282328 : Nat := 118140960795 + 282328 * 2 ^ 59
def prefixEnd_282328 : Nat := 4983230072969 + 3 ^ 40 * 282328 * 2
def baseEnd_282328 : Nat := 28636042710652172662045

theorem tailTrace_282328 : CollatzResearch.WordTrace tailWord_282328 prefixEnd_282328 28636042710652172662045 := by
  unfold tailWord_282328
  simp only [CollatzResearch.WordTrace]
  refine ⟨5148674060590674314347819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6864898747454232419130425 5148674060590674314347819)
  ·
    refine ⟨7723011090886011471521729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5148674060590674314347819 7723011090886011471521729)
    ·
      refine ⟨5792258318164508603641297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7723011090886011471521729 5792258318164508603641297)
      ·
        refine ⟨4344193738623381452730973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5792258318164508603641297 4344193738623381452730973)
        ·
          refine ⟨1629072651983768044774115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4344193738623381452730973 1629072651983768044774115)
          ·
            refine ⟨2443608977975652067161173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629072651983768044774115 2443608977975652067161173)
            ·
              refine ⟨28636042710652172662045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2443608977975652067161173 28636042710652172662045)
              ·
                rfl

theorem cell19_282328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_282328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282328 prefixEnd_282328 := by exact prefixLift 282328
  have htrace : WordTrace (prefixWord ++ tailWord_282328) baseStart_282328 baseEnd_282328 := by
    simpa [prefixWord, tailWord_282328, baseEnd_282328] using wordTrace_append hprefix tailTrace_282328
  have hstable : (prefixWord ++ tailWord_282328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282328).length < 2 ^ (prefixWord ++ tailWord_282328).sum := by decide
  have hdescent : baseEnd_282328 < baseStart_282328 := by decide
  rcases family_descends (prefixWord ++ tailWord_282328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282402 : List Nat := [3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_282402 : Nat := 118140960795 + 282402 * 2 ^ 59
def prefixEnd_282402 : Nat := 4983230072969 + 3 ^ 40 * 282402 * 2
def baseEnd_282402 : Nat := 85930645209546272341489

theorem tailTrace_282402 : CollatzResearch.WordTrace tailWord_282402 prefixEnd_282402 85930645209546272341489 := by
  unfold tailWord_282402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575011780728314816722365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6866698081942172844592973 2575011780728314816722365)
  ·
    refine ⟨965629417773118056270887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2575011780728314816722365 965629417773118056270887)
    ·
      refine ⟨1448444126659677084406331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 965629417773118056270887 1448444126659677084406331)
      ·
        refine ⟨2172666189989515626609497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448444126659677084406331 2172666189989515626609497)
        ·
          refine ⟨1629499642492136719957123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172666189989515626609497 1629499642492136719957123)
          ·
            refine ⟨2444249463738205079935685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629499642492136719957123 2444249463738205079935685)
            ·
              refine ⟨458296774450913452487941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2444249463738205079935685 458296774450913452487941)
              ·
                refine ⟨85930645209546272341489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458296774450913452487941 85930645209546272341489)
                ·
                  rfl

theorem cell19_282402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_282402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282402 prefixEnd_282402 := by exact prefixLift 282402
  have htrace : WordTrace (prefixWord ++ tailWord_282402) baseStart_282402 baseEnd_282402 := by
    simpa [prefixWord, tailWord_282402, baseEnd_282402] using wordTrace_append hprefix tailTrace_282402
  have hstable : (prefixWord ++ tailWord_282402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282402).length < 2 ^ (prefixWord ++ tailWord_282402).sum := by decide
  have hdescent : baseEnd_282402 < baseStart_282402 := by decide
  rcases family_descends (prefixWord ++ tailWord_282402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282438 : List Nat := [6, 1, 1, 2, 1, 8]
def baseStart_282438 : Nat := 118140960795 + 282438 * 2 ^ 59
def prefixEnd_282438 : Nat := 4983230072969 + 3 ^ 40 * 282438 * 2
def baseEnd_282438 : Nat := 9549066607056539504599

theorem tailTrace_282438 : CollatzResearch.WordTrace tailWord_282438 prefixEnd_282438 9549066607056539504599 := by
  unfold tailWord_282438
  simp only [CollatzResearch.WordTrace]
  refine ⟨321917504711963669224999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6867573433855224943466645 321917504711963669224999)
  ·
    refine ⟨482876257067945503837499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321917504711963669224999 482876257067945503837499)
    ·
      refine ⟨724314385601918255756249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482876257067945503837499 724314385601918255756249)
      ·
        refine ⟨543235789201438691817187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 724314385601918255756249 543235789201438691817187)
        ·
          refine ⟨814853683802158037725781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543235789201438691817187 814853683802158037725781)
          ·
            refine ⟨9549066607056539504599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 814853683802158037725781 9549066607056539504599)
            ·
              rfl

theorem cell19_282438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_282438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282438 prefixEnd_282438 := by exact prefixLift 282438
  have htrace : WordTrace (prefixWord ++ tailWord_282438) baseStart_282438 baseEnd_282438 := by
    simpa [prefixWord, tailWord_282438, baseEnd_282438] using wordTrace_append hprefix tailTrace_282438
  have hstable : (prefixWord ++ tailWord_282438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282438).length < 2 ^ (prefixWord ++ tailWord_282438).sum := by decide
  have hdescent : baseEnd_282438 < baseStart_282438 := by decide
  rcases family_descends (prefixWord ++ tailWord_282438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282474 : List Nat := [3, 1, 3, 4, 1, 1, 3, 3]
def baseStart_282474 : Nat := 118140960795 + 282474 * 2 ^ 59
def prefixEnd_282474 : Nat := 4983230072969 + 3 ^ 40 * 282474 * 2
def baseEnd_282474 : Nat := 85952553717471438741293

theorem tailTrace_282474 : CollatzResearch.WordTrace tailWord_282474 prefixEnd_282474 85952553717471438741293 := by
  unfold tailWord_282474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575668294663103890877619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6868448785768277042340317 2575668294663103890877619)
  ·
    refine ⟨3863502441994655836316429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2575668294663103890877619 3863502441994655836316429)
    ·
      refine ⟨1448813415747995938618661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3863502441994655836316429 1448813415747995938618661)
      ·
        refine ⟨271652515452749238490999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1448813415747995938618661 271652515452749238490999)
        ·
          refine ⟨407478773179123857736499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271652515452749238490999 407478773179123857736499)
          ·
            refine ⟨611218159768685786604749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407478773179123857736499 611218159768685786604749)
            ·
              refine ⟨229206809913257169976781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611218159768685786604749 229206809913257169976781)
              ·
                refine ⟨85952553717471438741293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229206809913257169976781 85952553717471438741293)
                ·
                  rfl

theorem cell19_282474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_282474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282474 prefixEnd_282474 := by exact prefixLift 282474
  have htrace : WordTrace (prefixWord ++ tailWord_282474) baseStart_282474 baseEnd_282474 := by
    simpa [prefixWord, tailWord_282474, baseEnd_282474] using wordTrace_append hprefix tailTrace_282474
  have hstable : (prefixWord ++ tailWord_282474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282474).length < 2 ^ (prefixWord ++ tailWord_282474).sum := by decide
  have hdescent : baseEnd_282474 < baseStart_282474 := by decide
  rcases family_descends (prefixWord ++ tailWord_282474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282499 : List Nat := [1, 1, 1, 3, 4, 3, 6]
def baseStart_282499 : Nat := 118140960795 + 282499 * 2 ^ 59
def prefixEnd_282499 : Nat := 4983230072969 + 3 ^ 40 * 282499 * 2
def baseEnd_282499 : Nat := 28653386946092929395223

theorem tailTrace_282499 : CollatzResearch.WordTrace tailWord_282499 prefixEnd_282499 28653386946092929395223 := by
  unfold tailWord_282499
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303585003561844833170551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6869056669041229888780367 10303585003561844833170551)
  ·
    refine ⟨15455377505342767249755827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10303585003561844833170551 15455377505342767249755827)
    ·
      refine ⟨23183066258014150874633741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15455377505342767249755827 23183066258014150874633741)
      ·
        refine ⟨8693649846755306577987653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23183066258014150874633741 8693649846755306577987653)
        ·
          refine ⟨1630059346266619983372685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8693649846755306577987653 1630059346266619983372685)
          ·
            refine ⟨611272254849982493764757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1630059346266619983372685 611272254849982493764757)
            ·
              refine ⟨28653386946092929395223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 611272254849982493764757 28653386946092929395223)
              ·
                rfl

theorem cell19_282499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_282499 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282499 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282499 prefixEnd_282499 := by exact prefixLift 282499
  have htrace : WordTrace (prefixWord ++ tailWord_282499) baseStart_282499 baseEnd_282499 := by
    simpa [prefixWord, tailWord_282499, baseEnd_282499] using wordTrace_append hprefix tailTrace_282499
  have hstable : (prefixWord ++ tailWord_282499).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282499).length < 2 ^ (prefixWord ++ tailWord_282499).sum := by decide
  have hdescent : baseEnd_282499 < baseStart_282499 := by decide
  rcases family_descends (prefixWord ++ tailWord_282499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282535 : List Nat := [1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_282535 : Nat := 118140960795 + 282535 * 2 ^ 59
def prefixEnd_282535 : Nat := 4983230072969 + 3 ^ 40 * 282535 * 2
def baseEnd_282535 : Nat := 85971115092241371385571

theorem tailTrace_282535 : CollatzResearch.WordTrace tailWord_282535 prefixEnd_282535 85971115092241371385571 := by
  unfold tailWord_282535
  simp only [CollatzResearch.WordTrace]
  refine ⟨10304898031431422981481059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6869932020954281987654039 10304898031431422981481059)
  ·
    refine ⟨15457347047147134472221589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10304898031431422981481059 15457347047147134472221589)
    ·
      refine ⟨724563142835021928385387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15457347047147134472221589 724563142835021928385387)
      ·
        refine ⟨1086844714252532892578081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724563142835021928385387 1086844714252532892578081)
        ·
          refine ⟨815133535689399669433561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1086844714252532892578081 815133535689399669433561)
          ·
            refine ⟨611350151767049752075171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815133535689399669433561 611350151767049752075171)
            ·
              refine ⟨917025227650574628112757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611350151767049752075171 917025227650574628112757)
              ·
                refine ⟨85971115092241371385571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 917025227650574628112757 85971115092241371385571)
                ·
                  rfl

theorem cell19_282535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_282535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282535 prefixEnd_282535 := by exact prefixLift 282535
  have htrace : WordTrace (prefixWord ++ tailWord_282535) baseStart_282535 baseEnd_282535 := by
    simpa [prefixWord, tailWord_282535, baseEnd_282535] using wordTrace_append hprefix tailTrace_282535
  have hstable : (prefixWord ++ tailWord_282535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282535).length < 2 ^ (prefixWord ++ tailWord_282535).sum := by decide
  have hdescent : baseEnd_282535 < baseStart_282535 := by decide
  rcases family_descends (prefixWord ++ tailWord_282535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282575 : List Nat := [1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_282575 : Nat := 118140960795 + 282575 * 2 ^ 59
def prefixEnd_282575 : Nat := 4983230072969 + 3 ^ 40 * 282575 * 2
def baseEnd_282575 : Nat := 85983286485533130496573

theorem tailTrace_282575 : CollatzResearch.WordTrace tailWord_282575 prefixEnd_282575 85983286485533130496573 := by
  unfold tailWord_282575
  simp only [CollatzResearch.WordTrace]
  refine ⟨10306356951286509812937179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6870904634191006541958119 10306356951286509812937179)
  ·
    refine ⟨15459535426929764719405769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10306356951286509812937179 15459535426929764719405769)
    ·
      refine ⟨11594651570197323539554327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15459535426929764719405769 11594651570197323539554327)
      ·
        refine ⟨17391977355295985309331491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11594651570197323539554327 17391977355295985309331491)
        ·
          refine ⟨26087966032943977963997237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17391977355295985309331491 26087966032943977963997237)
          ·
            refine ⟨2445746815588497934124741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26087966032943977963997237 2445746815588497934124741)
            ·
              refine ⟨458577527922843362648389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2445746815588497934124741 458577527922843362648389)
              ·
                refine ⟨85983286485533130496573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458577527922843362648389 85983286485533130496573)
                ·
                  rfl

theorem cell19_282575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_282575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282575 prefixEnd_282575 := by exact prefixLift 282575
  have htrace : WordTrace (prefixWord ++ tailWord_282575) baseStart_282575 baseEnd_282575 := by
    simpa [prefixWord, tailWord_282575, baseEnd_282575] using wordTrace_append hprefix tailTrace_282575
  have hstable : (prefixWord ++ tailWord_282575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282575).length < 2 ^ (prefixWord ++ tailWord_282575).sum := by decide
  have hdescent : baseEnd_282575 < baseStart_282575 := by decide
  rcases family_descends (prefixWord ++ tailWord_282575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282613 : List Nat := [1, 3, 5, 10]
def baseStart_282613 : Nat := 118140960795 + 282613 * 2 ^ 59
def prefixEnd_282613 : Nat := 4983230072969 + 3 ^ 40 * 282613 * 2
def baseEnd_282613 : Nat := 1061664806285929650025

theorem tailTrace_282613 : CollatzResearch.WordTrace tailWord_282613 prefixEnd_282613 1061664806285929650025 := by
  unfold tailWord_282613
  simp only [CollatzResearch.WordTrace]
  refine ⟨10307742925148842302820493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6871828616765894868546995 10307742925148842302820493)
  ·
    refine ⟨3865403596930815863557685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10307742925148842302820493 3865403596930815863557685)
    ·
      refine ⟨362381587212263987208533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3865403596930815863557685 362381587212263987208533)
      ·
        refine ⟨1061664806285929650025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 362381587212263987208533 1061664806285929650025)
        ·
          rfl

theorem cell19_282613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 10].length) (baseStart_282613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282613 prefixEnd_282613 := by exact prefixLift 282613
  have htrace : WordTrace (prefixWord ++ tailWord_282613) baseStart_282613 baseEnd_282613 := by
    simpa [prefixWord, tailWord_282613, baseEnd_282613] using wordTrace_append hprefix tailTrace_282613
  have hstable : (prefixWord ++ tailWord_282613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282613).length < 2 ^ (prefixWord ++ tailWord_282613).sum := by decide
  have hdescent : baseEnd_282613 < baseStart_282613 := by decide
  rcases family_descends (prefixWord ++ tailWord_282613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282647 : List Nat := [1, 1, 3, 5, 2, 1, 3, 3]
def baseStart_282647 : Nat := 118140960795 + 282647 * 2 ^ 59
def prefixEnd_282647 : Nat := 4983230072969 + 3 ^ 40 * 282647 * 2
def baseEnd_282647 : Nat := 86005194993458296896377

theorem tailTrace_282647 : CollatzResearch.WordTrace tailWord_282647 prefixEnd_282647 86005194993458296896377 := by
  unfold tailWord_282647
  simp only [CollatzResearch.WordTrace]
  refine ⟨10308983007025666109558195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6872655338017110739705463 10308983007025666109558195)
  ·
    refine ⟨15463474510538499164337293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10308983007025666109558195 15463474510538499164337293)
    ·
      refine ⟨5798802941451937186626485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15463474510538499164337293 5798802941451937186626485)
      ·
        refine ⟨543637775761119111246233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5798802941451937186626485 543637775761119111246233)
        ·
          refine ⟨407728331820839333434675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543637775761119111246233 407728331820839333434675)
          ·
            refine ⟨611592497731259000152013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407728331820839333434675 611592497731259000152013)
            ·
              refine ⟨229347186649222125057005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611592497731259000152013 229347186649222125057005)
              ·
                refine ⟨86005194993458296896377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229347186649222125057005 86005194993458296896377)
                ·
                  rfl

theorem cell19_282647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_282647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282647 prefixEnd_282647 := by exact prefixLift 282647
  have htrace : WordTrace (prefixWord ++ tailWord_282647) baseStart_282647 baseEnd_282647 := by
    simpa [prefixWord, tailWord_282647, baseEnd_282647] using wordTrace_append hprefix tailTrace_282647
  have hstable : (prefixWord ++ tailWord_282647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282647).length < 2 ^ (prefixWord ++ tailWord_282647).sum := by decide
  have hdescent : baseEnd_282647 < baseStart_282647 := by decide
  rcases family_descends (prefixWord ++ tailWord_282647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282706 : List Nat := [3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_282706 : Nat := 118140960795 + 282706 * 2 ^ 59
def prefixEnd_282706 : Nat := 4983230072969 + 3 ^ 40 * 282706 * 2
def baseEnd_282706 : Nat := 86023147798563641585105

theorem tailTrace_282706 : CollatzResearch.WordTrace tailWord_282706 prefixEnd_282706 86023147798563641585105 := by
  unfold tailWord_282706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577783728452979796488993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6874089942541279457303981 2577783728452979796488993)
  ·
    refine ⟨1933337796339734847366745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2577783728452979796488993 1933337796339734847366745)
    ·
      refine ⟨1450003347254801135525059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1933337796339734847366745 1450003347254801135525059)
      ·
        refine ⟨2175005020882201703287589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450003347254801135525059 2175005020882201703287589)
        ·
          refine ⟨407813441415412819366423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2175005020882201703287589 407813441415412819366423)
          ·
            refine ⟨611720162123119229049635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407813441415412819366423 611720162123119229049635)
            ·
              refine ⟨917580243184678843574453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611720162123119229049635 917580243184678843574453)
              ·
                refine ⟨86023147798563641585105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 917580243184678843574453 86023147798563641585105)
                ·
                  rfl

theorem cell19_282706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_282706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282706 prefixEnd_282706 := by exact prefixLift 282706
  have htrace : WordTrace (prefixWord ++ tailWord_282706) baseStart_282706 baseEnd_282706 := by
    simpa [prefixWord, tailWord_282706, baseEnd_282706] using wordTrace_append hprefix tailTrace_282706
  have hstable : (prefixWord ++ tailWord_282706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282706).length < 2 ^ (prefixWord ++ tailWord_282706).sum := by decide
  have hdescent : baseEnd_282706 < baseStart_282706 := by decide
  rcases family_descends (prefixWord ++ tailWord_282706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282782 : List Nat := [4, 3, 1, 1, 3, 7]
def baseStart_282782 : Nat := 118140960795 + 282782 * 2 ^ 59
def prefixEnd_282782 : Nat := 4983230072969 + 3 ^ 40 * 282782 * 2
def baseEnd_282782 : Nat := 9560697049535331544001

theorem tailTrace_282782 : CollatzResearch.WordTrace tailWord_282782 prefixEnd_282782 9560697049535331544001 := by
  unfold tailWord_282782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289238357692073020715325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6875937907691056110481733 1289238357692073020715325)
  ·
    refine ⟨483464384134527382768247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1289238357692073020715325 483464384134527382768247)
    ·
      refine ⟨725196576201791074152371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483464384134527382768247 725196576201791074152371)
      ·
        refine ⟨1087794864302686611228557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725196576201791074152371 1087794864302686611228557)
        ·
          refine ⟨407923074113507479210709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1087794864302686611228557 407923074113507479210709)
          ·
            refine ⟨9560697049535331544001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 407923074113507479210709 9560697049535331544001)
            ·
              rfl

theorem cell19_282782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_282782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_282782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_282782 prefixEnd_282782 := by exact prefixLift 282782
  have htrace : WordTrace (prefixWord ++ tailWord_282782) baseStart_282782 baseEnd_282782 := by
    simpa [prefixWord, tailWord_282782, baseEnd_282782] using wordTrace_append hprefix tailTrace_282782
  have hstable : (prefixWord ++ tailWord_282782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282782).length < 2 ^ (prefixWord ++ tailWord_282782).sum := by decide
  have hdescent : baseEnd_282782 < baseStart_282782 := by decide
  rcases family_descends (prefixWord ++ tailWord_282782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283033 : List Nat := [1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_283033 : Nat := 118140960795 + 283033 * 2 ^ 59
def prefixEnd_283033 : Nat := 4983230072969 + 3 ^ 40 * 283033 * 2
def baseEnd_283033 : Nat := 86122648938723772317547

theorem tailTrace_283033 : CollatzResearch.WordTrace tailWord_283033 prefixEnd_283033 86122648938723772317547 := by
  unfold tailWord_283033
  simp only [CollatzResearch.WordTrace]
  refine ⟨10323061583627254033109753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6882041055751502688739835 10323061583627254033109753)
  ·
    refine ⟨7742296187720440524832315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10323061583627254033109753 7742296187720440524832315)
    ·
      refine ⟨11613444281580660787248473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7742296187720440524832315 11613444281580660787248473)
      ·
        refine ⟨8710083211185495590436355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11613444281580660787248473 8710083211185495590436355)
        ·
          refine ⟨13065124816778243385654533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8710083211185495590436355 13065124816778243385654533)
          ·
            refine ⟨2449710903145920634810225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13065124816778243385654533 2449710903145920634810225)
            ·
              refine ⟨1837283177359440476107669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449710903145920634810225 1837283177359440476107669)
              ·
                refine ⟨86122648938723772317547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1837283177359440476107669 86122648938723772317547)
                ·
                  rfl

theorem cell19_283033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_283033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283033 prefixEnd_283033 := by exact prefixLift 283033
  have htrace : WordTrace (prefixWord ++ tailWord_283033) baseStart_283033 baseEnd_283033 := by
    simpa [prefixWord, tailWord_283033, baseEnd_283033] using wordTrace_append hprefix tailTrace_283033
  have hstable : (prefixWord ++ tailWord_283033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283033).length < 2 ^ (prefixWord ++ tailWord_283033).sum := by decide
  have hdescent : baseEnd_283033 < baseStart_283033 := by decide
  rcases family_descends (prefixWord ++ tailWord_283033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283048 : List Nat := [2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_283048 : Nat := 118140960795 + 283048 * 2 ^ 59
def prefixEnd_283048 : Nat := 4983230072969 + 3 ^ 40 * 283048 * 2
def baseEnd_283048 : Nat := 86127213211208181984173

theorem tailTrace_283048 : CollatzResearch.WordTrace tailWord_283048 prefixEnd_283048 86127213211208181984173 := by
  unfold tailWord_283048
  simp only [CollatzResearch.WordTrace]
  refine ⟨5161804339286455797452899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6882405785715274396603865 5161804339286455797452899)
  ·
    refine ⟨7742706508929683696179349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5161804339286455797452899 7742706508929683696179349)
    ·
      refine ⟨362939367606078923258407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7742706508929683696179349 362939367606078923258407)
      ·
        refine ⟨544409051409118384887611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362939367606078923258407 544409051409118384887611)
        ·
          refine ⟨816613577113677577331417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544409051409118384887611 816613577113677577331417)
          ·
            refine ⟨612460182835258182998563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816613577113677577331417 612460182835258182998563)
            ·
              refine ⟨918690274252887274497845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612460182835258182998563 918690274252887274497845)
              ·
                refine ⟨86127213211208181984173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 918690274252887274497845 86127213211208181984173)
                ·
                  rfl

theorem cell19_283048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_283048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283048 prefixEnd_283048 := by exact prefixLift 283048
  have htrace : WordTrace (prefixWord ++ tailWord_283048) baseStart_283048 baseEnd_283048 := by
    simpa [prefixWord, tailWord_283048, baseEnd_283048] using wordTrace_append hprefix tailTrace_283048
  have hstable : (prefixWord ++ tailWord_283048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283048).length < 2 ^ (prefixWord ++ tailWord_283048).sum := by decide
  have hdescent : baseEnd_283048 < baseStart_283048 := by decide
  rcases family_descends (prefixWord ++ tailWord_283048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283069 : List Nat := [1, 4, 1, 2, 2, 4, 5]
def baseStart_283069 : Nat := 118140960795 + 283069 * 2 ^ 59
def prefixEnd_283069 : Nat := 4983230072969 + 3 ^ 40 * 283069 * 2
def baseEnd_283069 : Nat := 28711201064228785172483

theorem tailTrace_283069 : CollatzResearch.WordTrace tailWord_283069 prefixEnd_283069 28711201064228785172483 := by
  unfold tailWord_283069
  simp only [CollatzResearch.WordTrace]
  refine ⟨10324374611496832181420261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6882916407664554787613507 10324374611496832181420261)
  ·
    refine ⟨1935820239655656034016299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10324374611496832181420261 1935820239655656034016299)
    ·
      refine ⟨2903730359483484051024449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935820239655656034016299 2903730359483484051024449)
      ·
        refine ⟨2177797769612613038268337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2903730359483484051024449 2177797769612613038268337)
        ·
          refine ⟨1633348327209459778701253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2177797769612613038268337 1633348327209459778701253)
          ·
            refine ⟨306252811351773708506485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1633348327209459778701253 306252811351773708506485)
            ·
              refine ⟨28711201064228785172483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 306252811351773708506485 28711201064228785172483)
              ·
                rfl

theorem cell19_283069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_283069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283069 prefixEnd_283069 := by exact prefixLift 283069
  have htrace : WordTrace (prefixWord ++ tailWord_283069) baseStart_283069 baseEnd_283069 := by
    simpa [prefixWord, tailWord_283069, baseEnd_283069] using wordTrace_append hprefix tailTrace_283069
  have hstable : (prefixWord ++ tailWord_283069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283069).length < 2 ^ (prefixWord ++ tailWord_283069).sum := by decide
  have hdescent : baseEnd_283069 < baseStart_283069 := by decide
  rcases family_descends (prefixWord ++ tailWord_283069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283143 : List Nat := [1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_283143 : Nat := 118140960795 + 283143 * 2 ^ 59
def prefixEnd_283143 : Nat := 4983230072969 + 3 ^ 40 * 283143 * 2
def baseEnd_283143 : Nat := 86156120270276109872803

theorem tailTrace_283143 : CollatzResearch.WordTrace tailWord_283143 prefixEnd_283143 86156120270276109872803 := by
  unfold tailWord_283143
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327073613228742819614083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6884715742152495213076055 10327073613228742819614083)
  ·
    refine ⟨15490610419843114229421125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10327073613228742819614083 15490610419843114229421125)
    ·
      refine ⟨2904489453720583918016461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15490610419843114229421125 2904489453720583918016461)
      ·
        refine ⟨1089183545145218969256173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2904489453720583918016461 1089183545145218969256173)
        ·
          refine ⟨408443829429457113471065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1089183545145218969256173 408443829429457113471065)
          ·
            refine ⟨306332872072092835103299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408443829429457113471065 306332872072092835103299)
            ·
              refine ⟨459499308108139252654949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306332872072092835103299 459499308108139252654949)
              ·
                refine ⟨86156120270276109872803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 459499308108139252654949 86156120270276109872803)
                ·
                  rfl

theorem cell19_283143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_283143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283143 prefixEnd_283143 := by exact prefixLift 283143
  have htrace : WordTrace (prefixWord ++ tailWord_283143) baseStart_283143 baseEnd_283143 := by
    simpa [prefixWord, tailWord_283143, baseEnd_283143] using wordTrace_append hprefix tailTrace_283143
  have hstable : (prefixWord ++ tailWord_283143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283143).length < 2 ^ (prefixWord ++ tailWord_283143).sum := by decide
  have hdescent : baseEnd_283143 < baseStart_283143 := by decide
  rcases family_descends (prefixWord ++ tailWord_283143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283221 : List Nat := [1, 3, 2, 2, 1, 1, 6, 3]
def baseStart_283221 : Nat := 118140960795 + 283221 * 2 ^ 59
def prefixEnd_283221 : Nat := 4983230072969 + 3 ^ 40 * 283221 * 2
def baseEnd_283221 : Nat := 86179854487195040139257

theorem tailTrace_283221 : CollatzResearch.WordTrace tailWord_283221 prefixEnd_283221 86179854487195040139257 := by
  unfold tailWord_283221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329918506946162140953517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6886612337964108093969011 10329918506946162140953517)
  ·
    refine ⟨3873719440104810802857569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10329918506946162140953517 3873719440104810802857569)
    ·
      refine ⟨2905289580078608102143177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3873719440104810802857569 2905289580078608102143177)
      ·
        refine ⟨2178967185058956076607383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2905289580078608102143177 2178967185058956076607383)
        ·
          refine ⟨3268450777588434114911075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178967185058956076607383 3268450777588434114911075)
          ·
            refine ⟨4902676166382651172366613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268450777588434114911075 4902676166382651172366613)
            ·
              refine ⟨229812945299186773704685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4902676166382651172366613 229812945299186773704685)
              ·
                refine ⟨86179854487195040139257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229812945299186773704685 86179854487195040139257)
                ·
                  rfl

theorem cell19_283221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_283221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283221 prefixEnd_283221 := by exact prefixLift 283221
  have htrace : WordTrace (prefixWord ++ tailWord_283221) baseStart_283221 baseEnd_283221 := by
    simpa [prefixWord, tailWord_283221, baseEnd_283221] using wordTrace_append hprefix tailTrace_283221
  have hstable : (prefixWord ++ tailWord_283221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283221).length < 2 ^ (prefixWord ++ tailWord_283221).sum := by decide
  have hdescent : baseEnd_283221 < baseStart_283221 := by decide
  rcases family_descends (prefixWord ++ tailWord_283221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283223 : List Nat := [1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_283223 : Nat := 118140960795 + 283223 * 2 ^ 59
def prefixEnd_283223 : Nat := 4983230072969 + 3 ^ 40 * 283223 * 2
def baseEnd_283223 : Nat := 86180463056859628094807

theorem tailTrace_283223 : CollatzResearch.WordTrace tailWord_283223 prefixEnd_283223 86180463056859628094807 := by
  unfold tailWord_283223
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329991452938916482526323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6886660968625944321684215 10329991452938916482526323)
  ·
    refine ⟨15494987179408374723789485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10329991452938916482526323 15494987179408374723789485)
    ·
      refine ⟨5810620192278140521421057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15494987179408374723789485 5810620192278140521421057)
      ·
        refine ⟨4357965144208605391065793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5810620192278140521421057 4357965144208605391065793)
        ·
          refine ⟨3268473858156454043299345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4357965144208605391065793 3268473858156454043299345)
          ·
            refine ⟨2451355393617340532474509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3268473858156454043299345 2451355393617340532474509)
            ·
              refine ⟨919258272606502699677941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2451355393617340532474509 919258272606502699677941)
              ·
                refine ⟨86180463056859628094807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 919258272606502699677941 86180463056859628094807)
                ·
                  rfl

theorem cell19_283223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_283223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283223 prefixEnd_283223 := by exact prefixLift 283223
  have htrace : WordTrace (prefixWord ++ tailWord_283223) baseStart_283223 baseEnd_283223 := by
    simpa [prefixWord, tailWord_283223, baseEnd_283223] using wordTrace_append hprefix tailTrace_283223
  have hstable : (prefixWord ++ tailWord_283223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283223).length < 2 ^ (prefixWord ++ tailWord_283223).sum := by decide
  have hdescent : baseEnd_283223 < baseStart_283223 := by decide
  rcases family_descends (prefixWord ++ tailWord_283223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283297 : List Nat := [1, 2, 3, 3, 4, 6]
def baseStart_283297 : Nat := 118140960795 + 283297 * 2 ^ 59
def prefixEnd_283297 : Nat := 4983230072969 + 3 ^ 40 * 283297 * 2
def baseEnd_283297 : Nat := 9578108903827709161129

theorem tailTrace_283297 : CollatzResearch.WordTrace tailWord_283297 prefixEnd_283297 9578108903827709161129 := by
  unfold tailWord_283297
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332690454670827120720145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6888460303113884747146763 10332690454670827120720145)
  ·
    refine ⟨7749517841003120340540109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10332690454670827120720145 7749517841003120340540109)
    ·
      refine ⟨2906069190376170127702541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7749517841003120340540109 2906069190376170127702541)
      ·
        refine ⟨1089775946391063797888453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2906069190376170127702541 1089775946391063797888453)
        ·
          refine ⟨204332989948324462104085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1089775946391063797888453 204332989948324462104085)
          ·
            refine ⟨9578108903827709161129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 204332989948324462104085 9578108903827709161129)
            ·
              rfl

theorem cell19_283297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 6].length) (baseStart_283297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283297 prefixEnd_283297 := by exact prefixLift 283297
  have htrace : WordTrace (prefixWord ++ tailWord_283297) baseStart_283297 baseEnd_283297 := by
    simpa [prefixWord, tailWord_283297, baseEnd_283297] using wordTrace_append hprefix tailTrace_283297
  have hstable : (prefixWord ++ tailWord_283297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283297).length < 2 ^ (prefixWord ++ tailWord_283297).sum := by decide
  have hdescent : baseEnd_283297 < baseStart_283297 := by decide
  rcases family_descends (prefixWord ++ tailWord_283297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283390 : List Nat := [4, 2, 2, 1, 2, 1, 4, 3]
def baseStart_283390 : Nat := 118140960795 + 283390 * 2 ^ 59
def prefixEnd_283390 : Nat := 4983230072969 + 3 ^ 40 * 283390 * 2
def baseEnd_283390 : Nat := 86231278623852722383241

theorem tailTrace_283390 : CollatzResearch.WordTrace tailWord_283390 prefixEnd_283390 86231278623852722383241 := by
  unfold tailWord_283390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292010305416738000481953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6890721628889269335903749 1292010305416738000481953)
  ·
    refine ⟨969007729062553500361465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1292010305416738000481953 969007729062553500361465)
    ·
      refine ⟨726755796796915125271099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 969007729062553500361465 726755796796915125271099)
      ·
        refine ⟨1090133695195372687906649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726755796796915125271099 1090133695195372687906649)
        ·
          refine ⟨817600271396529515929987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1090133695195372687906649 817600271396529515929987)
          ·
            refine ⟨1226400407094794273894981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817600271396529515929987 1226400407094794273894981)
            ·
              refine ⟨229950076330273926355309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1226400407094794273894981 229950076330273926355309)
              ·
                refine ⟨86231278623852722383241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229950076330273926355309 86231278623852722383241)
                ·
                  rfl

theorem cell19_283390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_283390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283390 prefixEnd_283390 := by exact prefixLift 283390
  have htrace : WordTrace (prefixWord ++ tailWord_283390) baseStart_283390 baseEnd_283390 := by
    simpa [prefixWord, tailWord_283390, baseEnd_283390] using wordTrace_append hprefix tailTrace_283390
  have hstable : (prefixWord ++ tailWord_283390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283390).length < 2 ^ (prefixWord ++ tailWord_283390).sum := by decide
  have hdescent : baseEnd_283390 < baseStart_283390 := by decide
  rcases family_descends (prefixWord ++ tailWord_283390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283527 : List Nat := [1, 1, 4, 2, 3, 2, 6]
def baseStart_283527 : Nat := 118140960795 + 283527 * 2 ^ 59
def prefixEnd_283527 : Nat := 4983230072969 + 3 ^ 40 * 283527 * 2
def baseEnd_283527 : Nat := 28757655215292332446141

theorem tailTrace_283527 : CollatzResearch.WordTrace tailWord_283527 prefixEnd_283527 28757655215292332446141 := by
  unfold tailWord_283527
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341079243837576401592835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6894052829225050934395223 10341079243837576401592835)
  ·
    refine ⟨15511618865756364602389253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10341079243837576401592835 15511618865756364602389253)
    ·
      refine ⟨2908428537329318362947985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15511618865756364602389253 2908428537329318362947985)
      ·
        refine ⟨2181321402996988772210989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2908428537329318362947985 2181321402996988772210989)
        ·
          refine ⟨817995526123870789579121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2181321402996988772210989 817995526123870789579121)
          ·
            refine ⟨613496644592903092184341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817995526123870789579121 613496644592903092184341)
            ·
              refine ⟨28757655215292332446141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 613496644592903092184341 28757655215292332446141)
              ·
                rfl

theorem cell19_283527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_283527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283527 prefixEnd_283527 := by exact prefixLift 283527
  have htrace : WordTrace (prefixWord ++ tailWord_283527) baseStart_283527 baseEnd_283527 := by
    simpa [prefixWord, tailWord_283527, baseEnd_283527] using wordTrace_append hprefix tailTrace_283527
  have hstable : (prefixWord ++ tailWord_283527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283527).length < 2 ^ (prefixWord ++ tailWord_283527).sum := by decide
  have hdescent : baseEnd_283527 < baseStart_283527 := by decide
  rcases family_descends (prefixWord ++ tailWord_283527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283559 : List Nat := [1, 1, 6, 1, 4, 1, 2, 3]
def baseStart_283559 : Nat := 118140960795 + 283559 * 2 ^ 59
def prefixEnd_283559 : Nat := 4983230072969 + 3 ^ 40 * 283559 * 2
def baseEnd_283559 : Nat := 86282702760510404627225

theorem tailTrace_283559 : CollatzResearch.WordTrace tailWord_283559 prefixEnd_283559 86282702760510404627225 := by
  unfold tailWord_283559
  simp only [CollatzResearch.WordTrace]
  refine ⟨10342246379721645866757731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6894830919814430577838487 10342246379721645866757731)
  ·
    refine ⟨15513369569582468800136597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10342246379721645866757731 15513369569582468800136597)
    ·
      refine ⟨727189198574178225006403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15513369569582468800136597 727189198574178225006403)
      ·
        refine ⟨1090783797861267337509605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727189198574178225006403 1090783797861267337509605)
        ·
          refine ⟨204521962098987625783051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1090783797861267337509605 204521962098987625783051)
          ·
            refine ⟨306782943148481438674577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204521962098987625783051 306782943148481438674577)
            ·
              refine ⟨230087207361361079005933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306782943148481438674577 230087207361361079005933)
              ·
                refine ⟨86282702760510404627225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230087207361361079005933 86282702760510404627225)
                ·
                  rfl

theorem cell19_283559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_283559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283559 prefixEnd_283559 := by exact prefixLift 283559
  have htrace : WordTrace (prefixWord ++ tailWord_283559) baseStart_283559 baseEnd_283559 := by
    simpa [prefixWord, tailWord_283559, baseEnd_283559] using wordTrace_append hprefix tailTrace_283559
  have hstable : (prefixWord ++ tailWord_283559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283559).length < 2 ^ (prefixWord ++ tailWord_283559).sum := by decide
  have hdescent : baseEnd_283559 < baseStart_283559 := by decide
  rcases family_descends (prefixWord ++ tailWord_283559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283584 : List Nat := [2, 1, 1, 2, 3, 5, 5]
def baseStart_283584 : Nat := 118140960795 + 283584 * 2 ^ 59
def prefixEnd_283584 : Nat := 4983230072969 + 3 ^ 40 * 283584 * 2
def baseEnd_283584 : Nat := 28763436627105918023867

theorem tailTrace_283584 : CollatzResearch.WordTrace tailWord_283584 prefixEnd_283584 28763436627105918023867 := by
  unfold tailWord_283584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5171579102315537568208903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6895438803087383424278537 5171579102315537568208903)
  ·
    refine ⟨7757368653473306352313355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5171579102315537568208903 7757368653473306352313355)
    ·
      refine ⟨11636052980209959528470033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7757368653473306352313355 11636052980209959528470033)
      ·
        refine ⟨8727039735157469646352525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11636052980209959528470033 8727039735157469646352525)
        ·
          refine ⟨3272639900684051117382197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8727039735157469646352525 3272639900684051117382197)
          ·
            refine ⟨306809990689129792254581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3272639900684051117382197 306809990689129792254581)
            ·
              refine ⟨28763436627105918023867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 306809990689129792254581 28763436627105918023867)
              ·
                rfl

theorem cell19_283584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_283584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283584 prefixEnd_283584 := by exact prefixLift 283584
  have htrace : WordTrace (prefixWord ++ tailWord_283584) baseStart_283584 baseEnd_283584 := by
    simpa [prefixWord, tailWord_283584, baseEnd_283584] using wordTrace_append hprefix tailTrace_283584
  have hstable : (prefixWord ++ tailWord_283584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283584).length < 2 ^ (prefixWord ++ tailWord_283584).sum := by decide
  have hdescent : baseEnd_283584 < baseStart_283584 := by decide
  rcases family_descends (prefixWord ++ tailWord_283584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283637 : List Nat := [1, 3, 5, 2, 2, 6]
def baseStart_283637 : Nat := 118140960795 + 283637 * 2 ^ 59
def prefixEnd_283637 : Nat := 4983230072969 + 3 ^ 40 * 283637 * 2
def baseEnd_283637 : Nat := 9589604108603259432631

theorem tailTrace_283637 : CollatzResearch.WordTrace tailWord_283637 prefixEnd_283637 9589604108603259432631 := by
  unfold tailWord_283637
  simp only [CollatzResearch.WordTrace]
  refine ⟨10345091273439065188097165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6896727515626043458731443 10345091273439065188097165)
  ·
    refine ⟨3879409227539649445536437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10345091273439065188097165 3879409227539649445536437)
    ·
      refine ⟨363694615081842135519041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3879409227539649445536437 363694615081842135519041)
      ·
        refine ⟨272770961311381601639281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363694615081842135519041 272770961311381601639281)
        ·
          refine ⟨204578220983536201229461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272770961311381601639281 204578220983536201229461)
          ·
            refine ⟨9589604108603259432631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 204578220983536201229461 9589604108603259432631)
            ·
              rfl

theorem cell19_283637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 6].length) (baseStart_283637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283637 prefixEnd_283637 := by exact prefixLift 283637
  have htrace : WordTrace (prefixWord ++ tailWord_283637) baseStart_283637 baseEnd_283637 := by
    simpa [prefixWord, tailWord_283637, baseEnd_283637] using wordTrace_append hprefix tailTrace_283637
  have hstable : (prefixWord ++ tailWord_283637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283637).length < 2 ^ (prefixWord ++ tailWord_283637).sum := by decide
  have hdescent : baseEnd_283637 < baseStart_283637 := by decide
  rcases family_descends (prefixWord ++ tailWord_283637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283658 : List Nat := [3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_283658 : Nat := 118140960795 + 283658 * 2 ^ 59
def prefixEnd_283658 : Nat := 4983230072969 + 3 ^ 40 * 283658 * 2
def baseEnd_283658 : Nat := 86312826958907508426955

theorem tailTrace_283658 : CollatzResearch.WordTrace tailWord_283658 prefixEnd_283658 86312826958907508426955 := by
  unfold tailWord_283658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586464301590746443652907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6897238137575323849741085 2586464301590746443652907)
  ·
    refine ⟨3879696452386119665479361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2586464301590746443652907 3879696452386119665479361)
    ·
      refine ⟨2909772339289589749109521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3879696452386119665479361 2909772339289589749109521)
      ·
        refine ⟨2182329254467192311832141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2909772339289589749109521 2182329254467192311832141)
        ·
          refine ⟨818373470425197116937053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2182329254467192311832141 818373470425197116937053)
          ·
            refine ⟨306890051409448918851395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 818373470425197116937053 306890051409448918851395)
            ·
              refine ⟨460335077114173378277093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306890051409448918851395 460335077114173378277093)
              ·
                refine ⟨86312826958907508426955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 460335077114173378277093 86312826958907508426955)
                ·
                  rfl

theorem cell19_283658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_283658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283658 prefixEnd_283658 := by exact prefixLift 283658
  have htrace : WordTrace (prefixWord ++ tailWord_283658) baseStart_283658 baseEnd_283658 := by
    simpa [prefixWord, tailWord_283658, baseEnd_283658] using wordTrace_append hprefix tailTrace_283658
  have hstable : (prefixWord ++ tailWord_283658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283658).length < 2 ^ (prefixWord ++ tailWord_283658).sum := by decide
  have hdescent : baseEnd_283658 < baseStart_283658 := by decide
  rcases family_descends (prefixWord ++ tailWord_283658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283660 : List Nat := [2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_283660 : Nat := 118140960795 + 283660 * 2 ^ 59
def prefixEnd_283660 : Nat := 4983230072969 + 3 ^ 40 * 283660 * 2
def baseEnd_283660 : Nat := 86313435528572096382505

theorem tailTrace_283660 : CollatzResearch.WordTrace tailWord_283660 prefixEnd_283660 86313435528572096382505 := by
  unfold tailWord_283660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172965076177870058092217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6897286768237160077456289 5172965076177870058092217)
  ·
    refine ⟨3879723807133402543569163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5172965076177870058092217 3879723807133402543569163)
    ·
      refine ⟨5819585710700103815353745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3879723807133402543569163 5819585710700103815353745)
      ·
        refine ⟨4364689283025077861515309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5819585710700103815353745 4364689283025077861515309)
        ·
          refine ⟨1636758481134404198068241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4364689283025077861515309 1636758481134404198068241)
          ·
            refine ⟨1227568860850803148551181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1636758481134404198068241 1227568860850803148551181)
            ·
              refine ⟨460338322819051180706693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1227568860850803148551181 460338322819051180706693)
              ·
                refine ⟨86313435528572096382505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 460338322819051180706693 86313435528572096382505)
                ·
                  rfl

theorem cell19_283660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_283660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283660 prefixEnd_283660 := by exact prefixLift 283660
  have htrace : WordTrace (prefixWord ++ tailWord_283660) baseStart_283660 baseEnd_283660 := by
    simpa [prefixWord, tailWord_283660, baseEnd_283660] using wordTrace_append hprefix tailTrace_283660
  have hstable : (prefixWord ++ tailWord_283660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283660).length < 2 ^ (prefixWord ++ tailWord_283660).sum := by decide
  have hdescent : baseEnd_283660 < baseStart_283660 := by decide
  rcases family_descends (prefixWord ++ tailWord_283660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283776 : List Nat := [2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_283776 : Nat := 118140960795 + 283776 * 2 ^ 59
def prefixEnd_283776 : Nat := 4983230072969 + 3 ^ 40 * 283776 * 2
def baseEnd_283776 : Nat := 86348732569118197804411

theorem tailTrace_283776 : CollatzResearch.WordTrace tailWord_283776 prefixEnd_283776 86348732569118197804411 := by
  unfold tailWord_283776
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175080509967745963703591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6900107346623661284938121 5175080509967745963703591)
  ·
    refine ⟨7762620764951618945555387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5175080509967745963703591 7762620764951618945555387)
    ·
      refine ⟨11643931147427428418333081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7762620764951618945555387 11643931147427428418333081)
      ·
        refine ⟨8732948360570571313749811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11643931147427428418333081 8732948360570571313749811)
        ·
          refine ⟨13099422540855856970624717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8732948360570571313749811 13099422540855856970624717)
          ·
            refine ⟨4912283452820946363984269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13099422540855856970624717 4912283452820946363984269)
            ·
              refine ⟨1842106294807854886494101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4912283452820946363984269 1842106294807854886494101)
              ·
                refine ⟨86348732569118197804411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1842106294807854886494101 86348732569118197804411)
                ·
                  rfl

theorem cell19_283776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_283776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283776 prefixEnd_283776 := by exact prefixLift 283776
  have htrace : WordTrace (prefixWord ++ tailWord_283776) baseStart_283776 baseEnd_283776 := by
    simpa [prefixWord, tailWord_283776, baseEnd_283776] using wordTrace_append hprefix tailTrace_283776
  have hstable : (prefixWord ++ tailWord_283776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283776).length < 2 ^ (prefixWord ++ tailWord_283776).sum := by decide
  have hdescent : baseEnd_283776 < baseStart_283776 := by decide
  rcases family_descends (prefixWord ++ tailWord_283776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283795 : List Nat := [1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_283795 : Nat := 118140960795 + 283795 * 2 ^ 59
def prefixEnd_283795 : Nat := 4983230072969 + 3 ^ 40 * 283795 * 2
def baseEnd_283795 : Nat := 86354513980931783382137

theorem tailTrace_283795 : CollatzResearch.WordTrace tailWord_283795 prefixEnd_283795 86354513980931783382137 := by
  unfold tailWord_283795
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350854006866658172348839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6900569337911105448232559 10350854006866658172348839)
  ·
    refine ⟨15526281010299987258523259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10350854006866658172348839 15526281010299987258523259)
    ·
      refine ⟨23289421515449980887784889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15526281010299987258523259 23289421515449980887784889)
      ·
        refine ⟨17467066136587485665838667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23289421515449980887784889 17467066136587485665838667)
        ·
          refine ⟨26200599204881228498758001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17467066136587485665838667 26200599204881228498758001)
          ·
            refine ⟨19650449403660921374068501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26200599204881228498758001 19650449403660921374068501)
            ·
              refine ⟨921114815796605689409461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19650449403660921374068501 921114815796605689409461)
              ·
                refine ⟨86354513980931783382137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 921114815796605689409461 86354513980931783382137)
                ·
                  rfl

theorem cell19_283795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_283795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283795 prefixEnd_283795 := by exact prefixLift 283795
  have htrace : WordTrace (prefixWord ++ tailWord_283795) baseStart_283795 baseEnd_283795 := by
    simpa [prefixWord, tailWord_283795, baseEnd_283795] using wordTrace_append hprefix tailTrace_283795
  have hstable : (prefixWord ++ tailWord_283795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283795).length < 2 ^ (prefixWord ++ tailWord_283795).sum := by decide
  have hdescent : baseEnd_283795 < baseStart_283795 := by decide
  rcases family_descends (prefixWord ++ tailWord_283795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283810 : List Nat := [3, 3, 1, 3, 3, 6]
def baseStart_283810 : Nat := 118140960795 + 283810 * 2 ^ 59
def prefixEnd_283810 : Nat := 4983230072969 + 3 ^ 40 * 283810 * 2
def baseEnd_283810 : Nat := 9595453139268465894307

theorem tailTrace_283810 : CollatzResearch.WordTrace tailWord_283810 prefixEnd_283810 9595453139268465894307 := by
  unfold tailWord_283810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2587850275453078933536221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6900934067874877156096589 2587850275453078933536221)
  ·
    refine ⟨970443853294904600076083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2587850275453078933536221 970443853294904600076083)
    ·
      refine ⟨1455665779942356900114125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970443853294904600076083 1455665779942356900114125)
      ·
        refine ⟨545874667478383837542797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1455665779942356900114125 545874667478383837542797)
        ·
          refine ⟨204703000304393939078549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 545874667478383837542797 204703000304393939078549)
          ·
            refine ⟨9595453139268465894307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 204703000304393939078549 9595453139268465894307)
            ·
              rfl

theorem cell19_283810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 6].length) (baseStart_283810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283810 prefixEnd_283810 := by exact prefixLift 283810
  have htrace : WordTrace (prefixWord ++ tailWord_283810) baseStart_283810 baseEnd_283810 := by
    simpa [prefixWord, tailWord_283810, baseEnd_283810] using wordTrace_append hprefix tailTrace_283810
  have hstable : (prefixWord ++ tailWord_283810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283810).length < 2 ^ (prefixWord ++ tailWord_283810).sum := by decide
  have hdescent : baseEnd_283810 < baseStart_283810 := by decide
  rcases family_descends (prefixWord ++ tailWord_283810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283905 : List Nat := [1, 2, 4, 1, 1, 5, 2, 3]
def baseStart_283905 : Nat := 118140960795 + 283905 * 2 ^ 59
def prefixEnd_283905 : Nat := 4983230072969 + 3 ^ 40 * 283905 * 2
def baseEnd_283905 : Nat := 86387985312484120937393

theorem tailTrace_283905 : CollatzResearch.WordTrace tailWord_283905 prefixEnd_283905 86387985312484120937393 := by
  unfold tailWord_283905
  simp only [CollatzResearch.WordTrace]
  refine ⟨10354866036468146958853169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6903244024312097972568779 10354866036468146958853169)
  ·
    refine ⟨7766149527351110219139877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10354866036468146958853169 7766149527351110219139877)
    ·
      refine ⟨1456153036378333166088727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7766149527351110219139877 1456153036378333166088727)
      ·
        refine ⟨2184229554567499749133091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456153036378333166088727 2184229554567499749133091)
        ·
          refine ⟨3276344331851249623699637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184229554567499749133091 3276344331851249623699637)
          ·
            refine ⟨307157281111054652221841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3276344331851249623699637 307157281111054652221841)
            ·
              refine ⟨230367960833290989166381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307157281111054652221841 230367960833290989166381)
              ·
                refine ⟨86387985312484120937393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230367960833290989166381 86387985312484120937393)
                ·
                  rfl

theorem cell19_283905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_283905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283905 prefixEnd_283905 := by exact prefixLift 283905
  have htrace : WordTrace (prefixWord ++ tailWord_283905) baseStart_283905 baseEnd_283905 := by
    simpa [prefixWord, tailWord_283905, baseEnd_283905] using wordTrace_append hprefix tailTrace_283905
  have hstable : (prefixWord ++ tailWord_283905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283905).length < 2 ^ (prefixWord ++ tailWord_283905).sum := by decide
  have hdescent : baseEnd_283905 < baseStart_283905 := by decide
  rcases family_descends (prefixWord ++ tailWord_283905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283907 : List Nat := [1, 1, 1, 3, 2, 4, 4, 3]
def baseStart_283907 : Nat := 118140960795 + 283907 * 2 ^ 59
def prefixEnd_283907 : Nat := 4983230072969 + 3 ^ 40 * 283907 * 2
def baseEnd_283907 : Nat := 86388593882148708892943

theorem tailTrace_283907 : CollatzResearch.WordTrace tailWord_283907 prefixEnd_283907 86388593882148708892943 := by
  unfold tailWord_283907
  simp only [CollatzResearch.WordTrace]
  refine ⟨10354938982460901300425975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6903292654973934200283983 10354938982460901300425975)
  ·
    refine ⟨15532408473691351950638963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10354938982460901300425975 15532408473691351950638963)
    ·
      refine ⟨23298612710537027925958445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15532408473691351950638963 23298612710537027925958445)
      ·
        refine ⟨8736979766451385472234417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23298612710537027925958445 8736979766451385472234417)
        ·
          refine ⟨6552734824838539104175813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8736979766451385472234417 6552734824838539104175813)
          ·
            refine ⟨1228637779657226082032965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6552734824838539104175813 1228637779657226082032965)
            ·
              refine ⟨230369583685729890381181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1228637779657226082032965 230369583685729890381181)
              ·
                refine ⟨86388593882148708892943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230369583685729890381181 86388593882148708892943)
                ·
                  rfl

theorem cell19_283907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_283907 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283907 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283907 prefixEnd_283907 := by exact prefixLift 283907
  have htrace : WordTrace (prefixWord ++ tailWord_283907) baseStart_283907 baseEnd_283907 := by
    simpa [prefixWord, tailWord_283907, baseEnd_283907] using wordTrace_append hprefix tailTrace_283907
  have hstable : (prefixWord ++ tailWord_283907).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283907).length < 2 ^ (prefixWord ++ tailWord_283907).sum := by decide
  have hdescent : baseEnd_283907 < baseStart_283907 := by decide
  rcases family_descends (prefixWord ++ tailWord_283907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283909 : List Nat := [1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_283909 : Nat := 118140960795 + 283909 * 2 ^ 59
def prefixEnd_283909 : Nat := 4983230072969 + 3 ^ 40 * 283909 * 2
def baseEnd_283909 : Nat := 86389202451813296848493

theorem tailTrace_283909 : CollatzResearch.WordTrace tailWord_283909 prefixEnd_283909 86389202451813296848493 := by
  unfold tailWord_283909
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355011928453655641998781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6903341285635770427999187 10355011928453655641998781)
  ·
    refine ⟨3883129473170120865749543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10355011928453655641998781 3883129473170120865749543)
    ·
      refine ⟨5824694209755181298624315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3883129473170120865749543 5824694209755181298624315)
      ·
        refine ⟨8737041314632771947936473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824694209755181298624315 8737041314632771947936473)
        ·
          refine ⟨6552780985974578960952355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8737041314632771947936473 6552780985974578960952355)
          ·
            refine ⟨9829171478961868441428533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6552780985974578960952355 9829171478961868441428533)
            ·
              refine ⟨921484826152675166383925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9829171478961868441428533 921484826152675166383925)
              ·
                refine ⟨86389202451813296848493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 921484826152675166383925 86389202451813296848493)
                ·
                  rfl

theorem cell19_283909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_283909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283909 prefixEnd_283909 := by exact prefixLift 283909
  have htrace : WordTrace (prefixWord ++ tailWord_283909) baseStart_283909 baseEnd_283909 := by
    simpa [prefixWord, tailWord_283909, baseEnd_283909] using wordTrace_append hprefix tailTrace_283909
  have hstable : (prefixWord ++ tailWord_283909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283909).length < 2 ^ (prefixWord ++ tailWord_283909).sum := by decide
  have hdescent : baseEnd_283909 < baseStart_283909 := by decide
  rcases family_descends (prefixWord ++ tailWord_283909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283922 : List Nat := [3, 2, 4, 2, 1, 2, 5]
def baseStart_283922 : Nat := 118140960795 + 283922 * 2 ^ 59
def prefixEnd_283922 : Nat := 4983230072969 + 3 ^ 40 * 283922 * 2
def baseEnd_283922 : Nat := 28797719384877706186523

theorem tailTrace_283922 : CollatzResearch.WordTrace tailWord_283922 prefixEnd_283922 28797719384877706186523 := by
  unfold tailWord_283922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588871519351639715555505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6903657384937705908148013 2588871519351639715555505)
  ·
    refine ⟨1941653639513729786666629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2588871519351639715555505 1941653639513729786666629)
    ·
      refine ⟨364060057408824334999993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1941653639513729786666629 364060057408824334999993)
      ·
        refine ⟨273045043056618251249995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364060057408824334999993 273045043056618251249995)
        ·
          refine ⟨409567564584927376874993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273045043056618251249995 409567564584927376874993)
          ·
            refine ⟨307175673438695532656245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409567564584927376874993 307175673438695532656245)
            ·
              refine ⟨28797719384877706186523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 307175673438695532656245 28797719384877706186523)
              ·
                rfl

theorem cell19_283922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_283922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283922 prefixEnd_283922 := by exact prefixLift 283922
  have htrace : WordTrace (prefixWord ++ tailWord_283922) baseStart_283922 baseEnd_283922 := by
    simpa [prefixWord, tailWord_283922, baseEnd_283922] using wordTrace_append hprefix tailTrace_283922
  have hstable : (prefixWord ++ tailWord_283922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283922).length < 2 ^ (prefixWord ++ tailWord_283922).sum := by decide
  have hdescent : baseEnd_283922 < baseStart_283922 := by decide
  rcases family_descends (prefixWord ++ tailWord_283922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283928 : List Nat := [2, 1, 2, 3, 1, 3, 7]
def baseStart_283928 : Nat := 118140960795 + 283928 * 2 ^ 59
def prefixEnd_283928 : Nat := 4983230072969 + 3 ^ 40 * 283928 * 2
def baseEnd_283928 : Nat := 28798327954542294142073

theorem tailTrace_283928 : CollatzResearch.WordTrace tailWord_283928 prefixEnd_283928 28798327954542294142073 := by
  unfold tailWord_283928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177852457692410943470219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6903803276923214591293625 5177852457692410943470219)
  ·
    refine ⟨7766778686538616415205329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5177852457692410943470219 7766778686538616415205329)
    ·
      refine ⟨5825084014903962311403997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7766778686538616415205329 5825084014903962311403997)
      ·
        refine ⟨2184406505588985866776499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5825084014903962311403997 2184406505588985866776499)
        ·
          refine ⟨3276609758383478800164749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184406505588985866776499 3276609758383478800164749)
          ·
            refine ⟨1228728659393804550061781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3276609758383478800164749 1228728659393804550061781)
            ·
              refine ⟨28798327954542294142073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1228728659393804550061781 28798327954542294142073)
              ·
                rfl

theorem cell19_283928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_283928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283928 prefixEnd_283928 := by exact prefixLift 283928
  have htrace : WordTrace (prefixWord ++ tailWord_283928) baseStart_283928 baseEnd_283928 := by
    simpa [prefixWord, tailWord_283928, baseEnd_283928] using wordTrace_append hprefix tailTrace_283928
  have hstable : (prefixWord ++ tailWord_283928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283928).length < 2 ^ (prefixWord ++ tailWord_283928).sum := by decide
  have hdescent : baseEnd_283928 < baseStart_283928 := by decide
  rcases family_descends (prefixWord ++ tailWord_283928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283981 : List Nat := [1, 6, 1, 3, 1, 7]
def baseStart_283981 : Nat := 118140960795 + 283981 * 2 ^ 59
def prefixEnd_283981 : Nat := 4983230072969 + 3 ^ 40 * 283981 * 2
def baseEnd_283981 : Nat := 9601234551082051472033

theorem tailTrace_283981 : CollatzResearch.WordTrace tailWord_283981 prefixEnd_283981 9601234551082051472033 := by
  unfold tailWord_283981
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357637984192811938619797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6905091989461874625746531 10357637984192811938619797)
  ·
    refine ⟨485514280509038059622803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10357637984192811938619797 485514280509038059622803)
    ·
      refine ⟨728271420763557089434205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485514280509038059622803 728271420763557089434205)
      ·
        refine ⟨273101782786333908537827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 728271420763557089434205 273101782786333908537827)
        ·
          refine ⟨409652674179500862806741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273101782786333908537827 409652674179500862806741)
          ·
            refine ⟨9601234551082051472033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 409652674179500862806741 9601234551082051472033)
            ·
              rfl

theorem cell19_283981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 7].length) (baseStart_283981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_283981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_283981 prefixEnd_283981 := by exact prefixLift 283981
  have htrace : WordTrace (prefixWord ++ tailWord_283981) baseStart_283981 baseEnd_283981 := by
    simpa [prefixWord, tailWord_283981, baseEnd_283981] using wordTrace_append hprefix tailTrace_283981
  have hstable : (prefixWord ++ tailWord_283981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283981).length < 2 ^ (prefixWord ++ tailWord_283981).sum := by decide
  have hdescent : baseEnd_283981 < baseStart_283981 := by decide
  rcases family_descends (prefixWord ++ tailWord_283981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284072 : List Nat := [2, 1, 6, 1, 3, 1, 2, 3]
def baseStart_284072 : Nat := 118140960795 + 284072 * 2 ^ 59
def prefixEnd_284072 : Nat := 4983230072969 + 3 ^ 40 * 284072 * 2
def baseEnd_284072 : Nat := 86438800879477215225827

theorem tailTrace_284072 : CollatzResearch.WordTrace tailWord_284072 prefixEnd_284072 86438800879477215225827 := by
  unfold tailWord_284072
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180478513431567240091235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6907304684575422986788313 5180478513431567240091235)
  ·
    refine ⟨7770717770147350860136853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5180478513431567240091235 7770717770147350860136853)
    ·
      refine ⟨364252395475657071568915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7770717770147350860136853 364252395475657071568915)
      ·
        refine ⟨546378593213485607353373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364252395475657071568915 546378593213485607353373)
        ·
          refine ⟨204891972455057102757515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 546378593213485607353373 204891972455057102757515)
          ·
            refine ⟨307337958682585654136273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204891972455057102757515 307337958682585654136273)
            ·
              refine ⟨230503469011939240602205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307337958682585654136273 230503469011939240602205)
              ·
                refine ⟨86438800879477215225827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230503469011939240602205 86438800879477215225827)
                ·
                  rfl

theorem cell19_284072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_284072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284072 prefixEnd_284072 := by exact prefixLift 284072
  have htrace : WordTrace (prefixWord ++ tailWord_284072) baseStart_284072 baseEnd_284072 := by
    simpa [prefixWord, tailWord_284072, baseEnd_284072] using wordTrace_append hprefix tailTrace_284072
  have hstable : (prefixWord ++ tailWord_284072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284072).length < 2 ^ (prefixWord ++ tailWord_284072).sum := by decide
  have hdescent : baseEnd_284072 < baseStart_284072 := by decide
  rcases family_descends (prefixWord ++ tailWord_284072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284171 : List Nat := [1, 1, 1, 1, 9, 1, 1, 4]
def baseStart_284171 : Nat := 118140960795 + 284171 * 2 ^ 59
def prefixEnd_284171 : Nat := 4983230072969 + 3 ^ 40 * 284171 * 2
def baseEnd_284171 : Nat := 86468925077874319025557

theorem tailTrace_284171 : CollatzResearch.WordTrace tailWord_284171 prefixEnd_284171 86468925077874319025557 := by
  unfold tailWord_284171
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364567853504474388036367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6909711902336316258690911 10364567853504474388036367)
  ·
    refine ⟨15546851780256711582054551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10364567853504474388036367 15546851780256711582054551)
    ·
      refine ⟨23320277670385067373081827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15546851780256711582054551 23320277670385067373081827)
      ·
        refine ⟨34980416505577601059622741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23320277670385067373081827 34980416505577601059622741)
        ·
          refine ⟨204963377962368756208727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 34980416505577601059622741 204963377962368756208727)
          ·
            refine ⟨307445066943553134313091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204963377962368756208727 307445066943553134313091)
            ·
              refine ⟨461167600415329701469637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307445066943553134313091 461167600415329701469637)
              ·
                refine ⟨86468925077874319025557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461167600415329701469637 86468925077874319025557)
                ·
                  rfl

theorem cell19_284171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_284171 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284171 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284171 prefixEnd_284171 := by exact prefixLift 284171
  have htrace : WordTrace (prefixWord ++ tailWord_284171) baseStart_284171 baseEnd_284171 := by
    simpa [prefixWord, tailWord_284171, baseEnd_284171] using wordTrace_append hprefix tailTrace_284171
  have hstable : (prefixWord ++ tailWord_284171).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284171).length < 2 ^ (prefixWord ++ tailWord_284171).sum := by decide
  have hdescent : baseEnd_284171 < baseStart_284171 := by decide
  rcases family_descends (prefixWord ++ tailWord_284171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284194 : List Nat := [3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_284194 : Nat := 118140960795 + 284194 * 2 ^ 59
def prefixEnd_284194 : Nat := 4983230072969 + 3 ^ 40 * 284194 * 2
def baseEnd_284194 : Nat := 86475923629017080514383

theorem tailTrace_284194 : CollatzResearch.WordTrace tailWord_284194 prefixEnd_284194 86475923629017080514383 := by
  unfold tailWord_284194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591351683105287329030909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6910271154947432877415757 2591351683105287329030909)
  ·
    refine ⟨971756881164482748386591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2591351683105287329030909 971756881164482748386591)
    ·
      refine ⟨1457635321746724122579887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 971756881164482748386591 1457635321746724122579887)
      ·
        refine ⟨2186452982620086183869831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457635321746724122579887 2186452982620086183869831)
        ·
          refine ⟨3279679473930129275804747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186452982620086183869831 3279679473930129275804747)
          ·
            refine ⟨4919519210895193913707121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279679473930129275804747 4919519210895193913707121)
            ·
              refine ⟨3689639408171395435280341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4919519210895193913707121 3689639408171395435280341)
              ·
                refine ⟨86475923629017080514383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3689639408171395435280341 86475923629017080514383)
                ·
                  rfl

theorem cell19_284194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_284194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284194 prefixEnd_284194 := by exact prefixLift 284194
  have htrace : WordTrace (prefixWord ++ tailWord_284194) baseStart_284194 baseEnd_284194 := by
    simpa [prefixWord, tailWord_284194, baseEnd_284194] using wordTrace_append hprefix tailTrace_284194
  have hstable : (prefixWord ++ tailWord_284194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284194).length < 2 ^ (prefixWord ++ tailWord_284194).sum := by decide
  have hdescent : baseEnd_284194 < baseStart_284194 := by decide
  rcases family_descends (prefixWord ++ tailWord_284194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284213 : List Nat := [1, 3, 3, 1, 1, 4, 6]
def baseStart_284213 : Nat := 118140960795 + 284213 * 2 ^ 59
def prefixEnd_284213 : Nat := 4983230072969 + 3 ^ 40 * 284213 * 2
def baseEnd_284213 : Nat := 28827235013610222030703

theorem tailTrace_284213 : CollatzResearch.WordTrace tailWord_284213 prefixEnd_284213 28827235013610222030703 := by
  unfold tailWord_284213
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366099719352315561065293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6910733146234877040710195 10366099719352315561065293)
  ·
    refine ⟨3887287394757118335399485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10366099719352315561065293 3887287394757118335399485)
    ·
      refine ⟨1457732773033919375774807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3887287394757118335399485 1457732773033919375774807)
      ·
        refine ⟨2186599159550879063662211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457732773033919375774807 2186599159550879063662211)
        ·
          refine ⟨3279898739326318595493317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186599159550879063662211 3279898739326318595493317)
          ·
            refine ⟨614981013623684736654997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3279898739326318595493317 614981013623684736654997)
            ·
              refine ⟨28827235013610222030703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 614981013623684736654997 28827235013610222030703)
              ·
                rfl

theorem cell19_284213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_284213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284213 prefixEnd_284213 := by exact prefixLift 284213
  have htrace : WordTrace (prefixWord ++ tailWord_284213) baseStart_284213 baseEnd_284213 := by
    simpa [prefixWord, tailWord_284213, baseEnd_284213] using wordTrace_append hprefix tailTrace_284213
  have hstable : (prefixWord ++ tailWord_284213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284213).length < 2 ^ (prefixWord ++ tailWord_284213).sum := by decide
  have hdescent : baseEnd_284213 < baseStart_284213 := by decide
  rcases family_descends (prefixWord ++ tailWord_284213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284289 : List Nat := [1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_284289 : Nat := 118140960795 + 284289 * 2 ^ 59
def prefixEnd_284289 : Nat := 4983230072969 + 3 ^ 40 * 284289 * 2
def baseEnd_284289 : Nat := 86504830688085008403013

theorem tailTrace_284289 : CollatzResearch.WordTrace tailWord_284289 prefixEnd_284289 86504830688085008403013 := by
  unfold tailWord_284289
  simp only [CollatzResearch.WordTrace]
  refine ⟨10368871667076980540831921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6912581111384653693887947 10368871667076980540831921)
  ·
    refine ⟨7776653750307735405623941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10368871667076980540831921 7776653750307735405623941)
    ·
      refine ⟨1458122578182700388554489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7776653750307735405623941 1458122578182700388554489)
      ·
        refine ⟨1093591933637025291415867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1458122578182700388554489 1093591933637025291415867)
        ·
          refine ⟨1640387900455537937123801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093591933637025291415867 1640387900455537937123801)
          ·
            refine ⟨1230290925341653452842851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1640387900455537937123801 1230290925341653452842851)
            ·
              refine ⟨1845436388012480179264277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230290925341653452842851 1845436388012480179264277)
              ·
                refine ⟨86504830688085008403013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1845436388012480179264277 86504830688085008403013)
                ·
                  rfl

theorem cell19_284289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_284289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284289 prefixEnd_284289 := by exact prefixLift 284289
  have htrace : WordTrace (prefixWord ++ tailWord_284289) baseStart_284289 baseEnd_284289 := by
    simpa [prefixWord, tailWord_284289, baseEnd_284289] using wordTrace_append hprefix tailTrace_284289
  have hstable : (prefixWord ++ tailWord_284289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284289).length < 2 ^ (prefixWord ++ tailWord_284289).sum := by decide
  have hdescent : baseEnd_284289 < baseStart_284289 := by decide
  rcases family_descends (prefixWord ++ tailWord_284289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284342 : List Nat := [5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_284342 : Nat := 118140960795 + 284342 * 2 ^ 59
def prefixEnd_284342 : Nat := 4983230072969 + 3 ^ 40 * 284342 * 2
def baseEnd_284342 : Nat := 86520957784196589225091

theorem tailTrace_284342 : CollatzResearch.WordTrace tailWord_284342 prefixEnd_284342 86520957784196589225091 := by
  unfold tailWord_284342
  simp only [CollatzResearch.WordTrace]
  refine ⟨648175295992810662031955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6913869823923313728340853 648175295992810662031955)
  ·
    refine ⟨972262943989215993047933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 648175295992810662031955 972262943989215993047933)
    ·
      refine ⟨364598603995955997392975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 972262943989215993047933 364598603995955997392975)
      ·
        refine ⟨546897905993933996089463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364598603995955997392975 546897905993933996089463)
        ·
          refine ⟨820346858990900994134195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546897905993933996089463 820346858990900994134195)
          ·
            refine ⟨1230520288486351491201293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820346858990900994134195 1230520288486351491201293)
            ·
              refine ⟨461445108182381809200485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230520288486351491201293 461445108182381809200485)
              ·
                refine ⟨86520957784196589225091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461445108182381809200485 86520957784196589225091)
                ·
                  rfl

theorem cell19_284342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_284342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284342 prefixEnd_284342 := by exact prefixLift 284342
  have htrace : WordTrace (prefixWord ++ tailWord_284342) baseStart_284342 baseEnd_284342 := by
    simpa [prefixWord, tailWord_284342, baseEnd_284342] using wordTrace_append hprefix tailTrace_284342
  have hstable : (prefixWord ++ tailWord_284342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284342).length < 2 ^ (prefixWord ++ tailWord_284342).sum := by decide
  have hdescent : baseEnd_284342 < baseStart_284342 := by decide
  rcases family_descends (prefixWord ++ tailWord_284342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284346 : List Nat := [3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_284346 : Nat := 118140960795 + 284346 * 2 ^ 59
def prefixEnd_284346 : Nat := 4983230072969 + 3 ^ 40 * 284346 * 2
def baseEnd_284346 : Nat := 86522174923525765136191

theorem tailTrace_284346 : CollatzResearch.WordTrace tailWord_284346 prefixEnd_284346 86522174923525765136191 := by
  unfold tailWord_284346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592737656967619818914223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6913967085246986183771261 2592737656967619818914223)
  ·
    refine ⟨3889106485451429728371335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2592737656967619818914223 3889106485451429728371335)
    ·
      refine ⟨5833659728177144592557003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889106485451429728371335 5833659728177144592557003)
      ·
        refine ⟨8750489592265716888835505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833659728177144592557003 8750489592265716888835505)
        ·
          refine ⟨6562867194199287666626629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8750489592265716888835505 6562867194199287666626629)
          ·
            refine ⟨1230537598912366437492493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6562867194199287666626629 1230537598912366437492493)
            ·
              refine ⟨461451599592137414059685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230537598912366437492493 461451599592137414059685)
              ·
                refine ⟨86522174923525765136191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461451599592137414059685 86522174923525765136191)
                ·
                  rfl

theorem cell19_284346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_284346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284346 prefixEnd_284346 := by exact prefixLift 284346
  have htrace : WordTrace (prefixWord ++ tailWord_284346) baseStart_284346 baseEnd_284346 := by
    simpa [prefixWord, tailWord_284346, baseEnd_284346] using wordTrace_append hprefix tailTrace_284346
  have hstable : (prefixWord ++ tailWord_284346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284346).length < 2 ^ (prefixWord ++ tailWord_284346).sum := by decide
  have hdescent : baseEnd_284346 < baseStart_284346 := by decide
  rcases family_descends (prefixWord ++ tailWord_284346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284367 : List Nat := [1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_284367 : Nat := 118140960795 + 284367 * 2 ^ 59
def prefixEnd_284367 : Nat := 4983230072969 + 3 ^ 40 * 284367 * 2
def baseEnd_284367 : Nat := 86528564905003938669467

theorem tailTrace_284367 : CollatzResearch.WordTrace tailWord_284367 prefixEnd_284367 86528564905003938669467 := by
  unfold tailWord_284367
  simp only [CollatzResearch.WordTrace]
  refine ⟨10371716560794399862171355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6914477707196266574780903 10371716560794399862171355)
  ·
    refine ⟨15557574841191599793257033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10371716560794399862171355 15557574841191599793257033)
    ·
      refine ⟨11668181130893699844942775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15557574841191599793257033 11668181130893699844942775)
      ·
        refine ⟨17502271696340549767414163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11668181130893699844942775 17502271696340549767414163)
        ·
          refine ⟨26253407544510824651121245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17502271696340549767414163 26253407544510824651121245)
          ·
            refine ⟨9845027829191559244170467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26253407544510824651121245 9845027829191559244170467)
            ·
              refine ⟨14767541743787338866255701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9845027829191559244170467 14767541743787338866255701)
              ·
                refine ⟨86528564905003938669467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14767541743787338866255701 86528564905003938669467)
                ·
                  rfl

theorem cell19_284367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_284367 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284367 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284367 prefixEnd_284367 := by exact prefixLift 284367
  have htrace : WordTrace (prefixWord ++ tailWord_284367) baseStart_284367 baseEnd_284367 := by
    simpa [prefixWord, tailWord_284367, baseEnd_284367] using wordTrace_append hprefix tailTrace_284367
  have hstable : (prefixWord ++ tailWord_284367).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284367).length < 2 ^ (prefixWord ++ tailWord_284367).sum := by decide
  have hdescent : baseEnd_284367 < baseStart_284367 := by decide
  rcases family_descends (prefixWord ++ tailWord_284367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284420 : List Nat := [2, 3, 2, 2, 1, 2, 4, 3]
def baseStart_284420 : Nat := 118140960795 + 284420 * 2 ^ 59
def prefixEnd_284420 : Nat := 4983230072969 + 3 ^ 40 * 284420 * 2
def baseEnd_284420 : Nat := 86544692001115519491545

theorem tailTrace_284420 : CollatzResearch.WordTrace tailWord_284420 prefixEnd_284420 86544692001115519491545 := by
  unfold tailWord_284420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5186824814801194956925357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6915766419734926609233809 5186824814801194956925357)
  ·
    refine ⟨1945059305550448108847009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5186824814801194956925357 1945059305550448108847009)
    ·
      refine ⟨1458794479162836081635257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1945059305550448108847009 1458794479162836081635257)
      ·
        refine ⟨1094095859372127061226443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1458794479162836081635257 1094095859372127061226443)
        ·
          refine ⟨1641143789058190591839665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094095859372127061226443 1641143789058190591839665)
          ·
            refine ⟨1230857841793642943879749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641143789058190591839665 1230857841793642943879749)
            ·
              refine ⟨230785845336308051977453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1230857841793642943879749 230785845336308051977453)
              ·
                refine ⟨86544692001115519491545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230785845336308051977453 86544692001115519491545)
                ·
                  rfl

theorem cell19_284420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_284420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284420 prefixEnd_284420 := by exact prefixLift 284420
  have htrace : WordTrace (prefixWord ++ tailWord_284420) baseStart_284420 baseEnd_284420 := by
    simpa [prefixWord, tailWord_284420, baseEnd_284420] using wordTrace_append hprefix tailTrace_284420
  have hstable : (prefixWord ++ tailWord_284420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284420).length < 2 ^ (prefixWord ++ tailWord_284420).sum := by decide
  have hdescent : baseEnd_284420 < baseStart_284420 := by decide
  rcases family_descends (prefixWord ++ tailWord_284420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284460 : List Nat := [2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_284460 : Nat := 118140960795 + 284460 * 2 ^ 59
def prefixEnd_284460 : Nat := 4983230072969 + 3 ^ 40 * 284460 * 2
def baseEnd_284460 : Nat := 86556863394407278602547

theorem tailTrace_284460 : CollatzResearch.WordTrace tailWord_284460 prefixEnd_284460 86556863394407278602547 := by
  unfold tailWord_284460
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187554274728738372653417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6916739032971651163537889 5187554274728738372653417)
  ·
    refine ⟨3890665706046553779490063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5187554274728738372653417 3890665706046553779490063)
    ·
      refine ⟨5835998559069830669235095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890665706046553779490063 5835998559069830669235095)
      ·
        refine ⟨8753997838604746003852643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5835998559069830669235095 8753997838604746003852643)
        ·
          refine ⟨13130996757907119005778965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8753997838604746003852643 13130996757907119005778965)
          ·
            refine ⟨615515473026896203395889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13130996757907119005778965 615515473026896203395889)
            ·
              refine ⟨461636604770172152546917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615515473026896203395889 461636604770172152546917)
              ·
                refine ⟨86556863394407278602547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461636604770172152546917 86556863394407278602547)
                ·
                  rfl

theorem cell19_284460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_284460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284460 prefixEnd_284460 := by exact prefixLift 284460
  have htrace : WordTrace (prefixWord ++ tailWord_284460) baseStart_284460 baseEnd_284460 := by
    simpa [prefixWord, tailWord_284460, baseEnd_284460] using wordTrace_append hprefix tailTrace_284460
  have hstable : (prefixWord ++ tailWord_284460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284460).length < 2 ^ (prefixWord ++ tailWord_284460).sum := by decide
  have hdescent : baseEnd_284460 < baseStart_284460 := by decide
  rcases family_descends (prefixWord ++ tailWord_284460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284515 : List Nat := [1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_284515 : Nat := 118140960795 + 284515 * 2 ^ 59
def prefixEnd_284515 : Nat := 4983230072969 + 3 ^ 40 * 284515 * 2
def baseEnd_284515 : Nat := 86573599060183447380175

theorem tailTrace_284515 : CollatzResearch.WordTrace tailWord_284515 prefixEnd_284515 86573599060183447380175 := by
  unfold tailWord_284515
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377114564258221138558999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6918076376172147425705999 10377114564258221138558999)
  ·
    refine ⟨15565671846387331707838499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10377114564258221138558999 15565671846387331707838499)
    ·
      refine ⟨23348507769580997561757749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15565671846387331707838499 23348507769580997561757749)
      ·
        refine ⟨2188922603398218521414789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23348507769580997561757749 2188922603398218521414789)
        ·
          refine ⟨410422988137165972765273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2188922603398218521414789 410422988137165972765273)
          ·
            refine ⟨307817241102874479573955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410422988137165972765273 307817241102874479573955)
            ·
              refine ⟨461725861654311719360933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307817241102874479573955 461725861654311719360933)
              ·
                refine ⟨86573599060183447380175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461725861654311719360933 86573599060183447380175)
                ·
                  rfl

theorem cell19_284515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_284515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284515 prefixEnd_284515 := by exact prefixLift 284515
  have htrace : WordTrace (prefixWord ++ tailWord_284515) baseStart_284515 baseEnd_284515 := by
    simpa [prefixWord, tailWord_284515, baseEnd_284515] using wordTrace_append hprefix tailTrace_284515
  have hstable : (prefixWord ++ tailWord_284515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284515).length < 2 ^ (prefixWord ++ tailWord_284515).sum := by decide
  have hdescent : baseEnd_284515 < baseStart_284515 := by decide
  rcases family_descends (prefixWord ++ tailWord_284515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284538 : List Nat := [3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_284538 : Nat := 118140960795 + 284538 * 2 ^ 59
def prefixEnd_284538 : Nat := 4983230072969 + 3 ^ 40 * 284538 * 2
def baseEnd_284538 : Nat := 86580597611326208869001

theorem tailTrace_284538 : CollatzResearch.WordTrace tailWord_284538 prefixEnd_284538 86580597611326208869001 := by
  unfold tailWord_284538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594488360793724016661567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6918635628783264044430845 2594488360793724016661567)
  ·
    refine ⟨3891732541190586024992351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2594488360793724016661567 3891732541190586024992351)
    ·
      refine ⟨5837598811785879037488527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3891732541190586024992351 5837598811785879037488527)
      ·
        refine ⟨8756398217678818556232791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5837598811785879037488527 8756398217678818556232791)
        ·
          refine ⟨13134597326518227834349187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756398217678818556232791 13134597326518227834349187)
          ·
            refine ⟨19701895989777341751523781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134597326518227834349187 19701895989777341751523781)
            ·
              refine ⟨3694105498083251578410709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19701895989777341751523781 3694105498083251578410709)
              ·
                refine ⟨86580597611326208869001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3694105498083251578410709 86580597611326208869001)
                ·
                  rfl

theorem cell19_284538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_284538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284538 prefixEnd_284538 := by exact prefixLift 284538
  have htrace : WordTrace (prefixWord ++ tailWord_284538) baseStart_284538 baseEnd_284538 := by
    simpa [prefixWord, tailWord_284538, baseEnd_284538] using wordTrace_append hprefix tailTrace_284538
  have hstable : (prefixWord ++ tailWord_284538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284538).length < 2 ^ (prefixWord ++ tailWord_284538).sum := by decide
  have hdescent : baseEnd_284538 < baseStart_284538 := by decide
  rcases family_descends (prefixWord ++ tailWord_284538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284576 : List Nat := [2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_284576 : Nat := 118140960795 + 284576 * 2 ^ 59
def prefixEnd_284576 : Nat := 4983230072969 + 3 ^ 40 * 284576 * 2
def baseEnd_284576 : Nat := 86592160434953380024453

theorem tailTrace_284576 : CollatzResearch.WordTrace tailWord_284576 prefixEnd_284576 86592160434953380024453 := by
  unfold tailWord_284576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189669708518614278264791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6919559611358152371019721 5189669708518614278264791)
  ·
    refine ⟨7784504562777921417397187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5189669708518614278264791 7784504562777921417397187)
    ·
      refine ⟨11676756844166882126095781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7784504562777921417397187 11676756844166882126095781)
      ·
        refine ⟨2189391908281290398642959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11676756844166882126095781 2189391908281290398642959)
        ·
          refine ⟨3284087862421935597964439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189391908281290398642959 3284087862421935597964439)
          ·
            refine ⟨4926131793632903396946659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284087862421935597964439 4926131793632903396946659)
            ·
              refine ⟨7389197690449355095419989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926131793632903396946659 7389197690449355095419989)
              ·
                refine ⟨86592160434953380024453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7389197690449355095419989 86592160434953380024453)
                ·
                  rfl

theorem cell19_284576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_284576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284576 prefixEnd_284576 := by exact prefixLift 284576
  have htrace : WordTrace (prefixWord ++ tailWord_284576) baseStart_284576 baseEnd_284576 := by
    simpa [prefixWord, tailWord_284576, baseEnd_284576] using wordTrace_append hprefix tailTrace_284576
  have hstable : (prefixWord ++ tailWord_284576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284576).length < 2 ^ (prefixWord ++ tailWord_284576).sum := by decide
  have hdescent : baseEnd_284576 < baseStart_284576 := by decide
  rcases family_descends (prefixWord ++ tailWord_284576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284593 : List Nat := [1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_284593 : Nat := 118140960795 + 284593 * 2 ^ 59
def prefixEnd_284593 : Nat := 4983230072969 + 3 ^ 40 * 284593 * 2
def baseEnd_284593 : Nat := 86597333277102377646629

theorem tailTrace_284593 : CollatzResearch.WordTrace tailWord_284593 prefixEnd_284593 86597333277102377646629 := by
  unfold tailWord_284593
  simp only [CollatzResearch.WordTrace]
  refine ⟨10379959457975640459898433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6919972971983760306598955 10379959457975640459898433)
  ·
    refine ⟨7784969593481730344923825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10379959457975640459898433 7784969593481730344923825)
    ·
      refine ⟨5838727195111297758692869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7784969593481730344923825 5838727195111297758692869)
      ·
        refine ⟨1094761349083368329754913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5838727195111297758692869 1094761349083368329754913)
        ·
          refine ⟨821071011812526247316185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1094761349083368329754913 821071011812526247316185)
          ·
            refine ⟨615803258859394685487139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821071011812526247316185 615803258859394685487139)
            ·
              refine ⟨923704888289092028230709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615803258859394685487139 923704888289092028230709)
              ·
                refine ⟨86597333277102377646629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 923704888289092028230709 86597333277102377646629)
                ·
                  rfl

theorem cell19_284593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_284593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284593 prefixEnd_284593 := by exact prefixLift 284593
  have htrace : WordTrace (prefixWord ++ tailWord_284593) baseStart_284593 baseEnd_284593 := by
    simpa [prefixWord, tailWord_284593, baseEnd_284593] using wordTrace_append hprefix tailTrace_284593
  have hstable : (prefixWord ++ tailWord_284593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284593).length < 2 ^ (prefixWord ++ tailWord_284593).sum := by decide
  have hdescent : baseEnd_284593 < baseStart_284593 := by decide
  rcases family_descends (prefixWord ++ tailWord_284593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284595 : List Nat := [1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_284595 : Nat := 118140960795 + 284595 * 2 ^ 59
def prefixEnd_284595 : Nat := 4983230072969 + 3 ^ 40 * 284595 * 2
def baseEnd_284595 : Nat := 86597941846766965602179

theorem tailTrace_284595 : CollatzResearch.WordTrace tailWord_284595 prefixEnd_284595 86597941846766965602179 := by
  unfold tailWord_284595
  simp only [CollatzResearch.WordTrace]
  refine ⟨10380032403968394801471239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6920021602645596534314159 10380032403968394801471239)
  ·
    refine ⟨15570048605952592202206859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10380032403968394801471239 15570048605952592202206859)
    ·
      refine ⟨23355072908928888303310289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15570048605952592202206859 23355072908928888303310289)
      ·
        refine ⟨17516304681696666227482717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23355072908928888303310289 17516304681696666227482717)
        ·
          refine ⟨6568614255636249835306019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17516304681696666227482717 6568614255636249835306019)
          ·
            refine ⟨9852921383454374752959029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6568614255636249835306019 9852921383454374752959029)
            ·
              refine ⟨923711379698847633089909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9852921383454374752959029 923711379698847633089909)
              ·
                refine ⟨86597941846766965602179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 923711379698847633089909 86597941846766965602179)
                ·
                  rfl

theorem cell19_284595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_284595 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284595 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284595 prefixEnd_284595 := by exact prefixLift 284595
  have htrace : WordTrace (prefixWord ++ tailWord_284595) baseStart_284595 baseEnd_284595 := by
    simpa [prefixWord, tailWord_284595, baseEnd_284595] using wordTrace_append hprefix tailTrace_284595
  have hstable : (prefixWord ++ tailWord_284595).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284595).length < 2 ^ (prefixWord ++ tailWord_284595).sum := by decide
  have hdescent : baseEnd_284595 < baseStart_284595 := by decide
  rcases family_descends (prefixWord ++ tailWord_284595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284678 : List Nat := [6, 2, 1, 2, 2, 1, 1, 4]
def baseStart_284678 : Nat := 118140960795 + 284678 * 2 ^ 59
def prefixEnd_284678 : Nat := 4983230072969 + 3 ^ 40 * 284678 * 2
def baseEnd_284678 : Nat := 86623197487847365757509

theorem tailTrace_284678 : CollatzResearch.WordTrace tailWord_284678 prefixEnd_284678 86623197487847365757509 := by
  unfold tailWord_284678
  simp only [CollatzResearch.WordTrace]
  refine ⟨324470614458365624273209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6922039775111799984495125 324470614458365624273209)
  ·
    refine ⟨243352960843774218204907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 324470614458365624273209 243352960843774218204907)
    ·
      refine ⟨365029441265661327307361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243352960843774218204907 365029441265661327307361)
      ·
        refine ⟨273772080949245995480521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365029441265661327307361 273772080949245995480521)
        ·
          refine ⟨205329060711934496610391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273772080949245995480521 205329060711934496610391)
          ·
            refine ⟨307993591067901744915587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205329060711934496610391 307993591067901744915587)
            ·
              refine ⟨461990386601852617373381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307993591067901744915587 461990386601852617373381)
              ·
                refine ⟨86623197487847365757509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461990386601852617373381 86623197487847365757509)
                ·
                  rfl

theorem cell19_284678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_284678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284678 prefixEnd_284678 := by exact prefixLift 284678
  have htrace : WordTrace (prefixWord ++ tailWord_284678) baseStart_284678 baseEnd_284678 := by
    simpa [prefixWord, tailWord_284678, baseEnd_284678] using wordTrace_append hprefix tailTrace_284678
  have hstable : (prefixWord ++ tailWord_284678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284678).length < 2 ^ (prefixWord ++ tailWord_284678).sum := by decide
  have hdescent : baseEnd_284678 < baseStart_284678 := by decide
  rcases family_descends (prefixWord ++ tailWord_284678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284705 : List Nat := [1, 2, 3, 2, 4, 1, 3, 3]
def baseStart_284705 : Nat := 118140960795 + 284705 * 2 ^ 59
def prefixEnd_284705 : Nat := 4983230072969 + 3 ^ 40 * 284705 * 2
def baseEnd_284705 : Nat := 86631413178319303157435

theorem tailTrace_284705 : CollatzResearch.WordTrace tailWord_284705 prefixEnd_284705 86631413178319303157435 := by
  unfold tailWord_284705
  simp only [CollatzResearch.WordTrace]
  refine ⟨10384044433569883587975569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6922696289046589058650379 10384044433569883587975569)
  ·
    refine ⟨7788033325177412690981677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10384044433569883587975569 7788033325177412690981677)
    ·
      refine ⟨2920512496941529759118129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7788033325177412690981677 2920512496941529759118129)
      ·
        refine ⟨2190384372706147319338597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2920512496941529759118129 2190384372706147319338597)
        ·
          refine ⟨410697069882402622375987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2190384372706147319338597 410697069882402622375987)
          ·
            refine ⟨616045604823603933563981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410697069882402622375987 616045604823603933563981)
            ·
              refine ⟨231017101808851475086493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 616045604823603933563981 231017101808851475086493)
              ·
                refine ⟨86631413178319303157435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231017101808851475086493 86631413178319303157435)
                ·
                  rfl

theorem cell19_284705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_284705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284705 prefixEnd_284705 := by exact prefixLift 284705
  have htrace : WordTrace (prefixWord ++ tailWord_284705) baseStart_284705 baseEnd_284705 := by
    simpa [prefixWord, tailWord_284705, baseEnd_284705] using wordTrace_append hprefix tailTrace_284705
  have hstable : (prefixWord ++ tailWord_284705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284705).length < 2 ^ (prefixWord ++ tailWord_284705).sum := by decide
  have hdescent : baseEnd_284705 < baseStart_284705 := by decide
  rcases family_descends (prefixWord ++ tailWord_284705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284707 : List Nat := [1, 1, 1, 4, 3, 1, 5, 3]
def baseStart_284707 : Nat := 118140960795 + 284707 * 2 ^ 59
def prefixEnd_284707 : Nat := 4983230072969 + 3 ^ 40 * 284707 * 2
def baseEnd_284707 : Nat := 86632021747983891112985

theorem tailTrace_284707 : CollatzResearch.WordTrace tailWord_284707 prefixEnd_284707 86632021747983891112985 := by
  unfold tailWord_284707
  simp only [CollatzResearch.WordTrace]
  refine ⟨10384117379562637929548375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6922744919708425286365583 10384117379562637929548375)
  ·
    refine ⟨15576176069343956894322563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10384117379562637929548375 15576176069343956894322563)
    ·
      refine ⟨23364264104015935341483845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15576176069343956894322563 23364264104015935341483845)
      ·
        refine ⟨4380799519502987876528221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23364264104015935341483845 4380799519502987876528221)
        ·
          refine ⟨1642799819813620453698083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4380799519502987876528221 1642799819813620453698083)
          ·
            refine ⟨2464199729720430680547125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642799819813620453698083 2464199729720430680547125)
            ·
              refine ⟨231018724661290376301293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2464199729720430680547125 231018724661290376301293)
              ·
                refine ⟨86632021747983891112985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231018724661290376301293 86632021747983891112985)
                ·
                  rfl

theorem cell19_284707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_284707 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284707 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284707 prefixEnd_284707 := by exact prefixLift 284707
  have htrace : WordTrace (prefixWord ++ tailWord_284707) baseStart_284707 baseEnd_284707 := by
    simpa [prefixWord, tailWord_284707, baseEnd_284707] using wordTrace_append hprefix tailTrace_284707
  have hstable : (prefixWord ++ tailWord_284707).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284707).length < 2 ^ (prefixWord ++ tailWord_284707).sum := by decide
  have hdescent : baseEnd_284707 < baseStart_284707 := by decide
  rcases family_descends (prefixWord ++ tailWord_284707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284724 : List Nat := [2, 5, 1, 2, 2, 1, 6]
def baseStart_284724 : Nat := 118140960795 + 284724 * 2 ^ 59
def prefixEnd_284724 : Nat := 4983230072969 + 3 ^ 40 * 284724 * 2
def baseEnd_284724 : Nat := 28879064863377629578387

theorem tailTrace_284724 : CollatzResearch.WordTrace tailWord_284724 prefixEnd_284724 28879064863377629578387 := by
  unfold tailWord_284724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5192368710250524916458613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6923158280334033221944817 5192368710250524916458613)
  ·
    refine ⟨486784566585986710917995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5192368710250524916458613 486784566585986710917995)
    ·
      refine ⟨730176849878980066376993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 486784566585986710917995 730176849878980066376993)
      ·
        refine ⟨547632637409235049782745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 730176849878980066376993 547632637409235049782745)
        ·
          refine ⟨410724478056926287337059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547632637409235049782745 410724478056926287337059)
          ·
            refine ⟨616086717085389431005589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410724478056926287337059 616086717085389431005589)
            ·
              refine ⟨28879064863377629578387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 616086717085389431005589 28879064863377629578387)
              ·
                rfl

theorem cell19_284724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_284724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284724 prefixEnd_284724 := by exact prefixLift 284724
  have htrace : WordTrace (prefixWord ++ tailWord_284724) baseStart_284724 baseEnd_284724 := by
    simpa [prefixWord, tailWord_284724, baseEnd_284724] using wordTrace_append hprefix tailTrace_284724
  have hstable : (prefixWord ++ tailWord_284724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284724).length < 2 ^ (prefixWord ++ tailWord_284724).sum := by decide
  have hdescent : baseEnd_284724 < baseStart_284724 := by decide
  rcases family_descends (prefixWord ++ tailWord_284724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284726 : List Nat := [5, 1, 2, 1, 1, 1, 8]
def baseStart_284726 : Nat := 118140960795 + 284726 * 2 ^ 59
def prefixEnd_284726 : Nat := 4983230072969 + 3 ^ 40 * 284726 * 2
def baseEnd_284726 : Nat := 28879267719932492230237

theorem tailTrace_284726 : CollatzResearch.WordTrace tailWord_284726 prefixEnd_284726 28879267719932492230237 := by
  unfold tailWord_284726
  simp only [CollatzResearch.WordTrace]
  refine ⟨649050647905862760905627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6923206910995869449660021 649050647905862760905627)
  ·
    refine ⟨973575971858794141358441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 649050647905862760905627 973575971858794141358441)
    ·
      refine ⟨730181978894095606018831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 973575971858794141358441 730181978894095606018831)
      ·
        refine ⟨1095272968341143409028247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730181978894095606018831 1095272968341143409028247)
        ·
          refine ⟨1642909452511715113542371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095272968341143409028247 1642909452511715113542371)
          ·
            refine ⟨2464364178767572670313557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642909452511715113542371 2464364178767572670313557)
            ·
              refine ⟨28879267719932492230237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2464364178767572670313557 28879267719932492230237)
              ·
                rfl

theorem cell19_284726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_284726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284726 prefixEnd_284726 := by exact prefixLift 284726
  have htrace : WordTrace (prefixWord ++ tailWord_284726) baseStart_284726 baseEnd_284726 := by
    simpa [prefixWord, tailWord_284726, baseEnd_284726] using wordTrace_append hprefix tailTrace_284726
  have hstable : (prefixWord ++ tailWord_284726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284726).length < 2 ^ (prefixWord ++ tailWord_284726).sum := by decide
  have hdescent : baseEnd_284726 < baseStart_284726 := by decide
  rcases family_descends (prefixWord ++ tailWord_284726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284758 : List Nat := [5, 2, 2, 1, 1, 3, 2, 3]
def baseStart_284758 : Nat := 118140960795 + 284758 * 2 ^ 59
def prefixEnd_284758 : Nat := 4983230072969 + 3 ^ 40 * 284758 * 2
def baseEnd_284758 : Nat := 86647540274430883979513

theorem tailTrace_284758 : CollatzResearch.WordTrace tailWord_284758 prefixEnd_284758 86647540274430883979513 := by
  unfold tailWord_284758
  simp only [CollatzResearch.WordTrace]
  refine ⟨649123593898617102478433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6923985001585249093103285 649123593898617102478433)
  ·
    refine ⟨486842695423962826858825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 649123593898617102478433 486842695423962826858825)
    ·
      refine ⟨365132021567972120144119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486842695423962826858825 365132021567972120144119)
      ·
        refine ⟨547698032351958180216179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365132021567972120144119 547698032351958180216179)
        ·
          refine ⟨821547048527937270324269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547698032351958180216179 821547048527937270324269)
          ·
            refine ⟨308080143197976476371601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 821547048527937270324269 308080143197976476371601)
            ·
              refine ⟨231060107398482357278701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308080143197976476371601 231060107398482357278701)
              ·
                refine ⟨86647540274430883979513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231060107398482357278701 86647540274430883979513)
                ·
                  rfl

theorem cell19_284758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_284758 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284758 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284758 prefixEnd_284758 := by exact prefixLift 284758
  have htrace : WordTrace (prefixWord ++ tailWord_284758) baseStart_284758 baseEnd_284758 := by
    simpa [prefixWord, tailWord_284758, baseEnd_284758] using wordTrace_append hprefix tailTrace_284758
  have hstable : (prefixWord ++ tailWord_284758).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284758).length < 2 ^ (prefixWord ++ tailWord_284758).sum := by decide
  have hdescent : baseEnd_284758 < baseStart_284758 := by decide
  rcases family_descends (prefixWord ++ tailWord_284758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284764 : List Nat := [2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_284764 : Nat := 118140960795 + 284764 * 2 ^ 59
def prefixEnd_284764 : Nat := 4983230072969 + 3 ^ 40 * 284764 * 2
def baseEnd_284764 : Nat := 86649365983424647846163

theorem tailTrace_284764 : CollatzResearch.WordTrace tailWord_284764 prefixEnd_284764 86649365983424647846163 := by
  unfold tailWord_284764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193098170178068332186673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6924130893570757776248897 5193098170178068332186673)
  ·
    refine ⟨3894823627633551249140005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5193098170178068332186673 3894823627633551249140005)
    ·
      refine ⟨730279430181290859213751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3894823627633551249140005 730279430181290859213751)
      ·
        refine ⟨1095419145271936288820627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730279430181290859213751 1095419145271936288820627)
        ·
          refine ⟨1643128717907904433230941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095419145271936288820627 1643128717907904433230941)
          ·
            refine ⟨616173269215464162461603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1643128717907904433230941 616173269215464162461603)
            ·
              refine ⟨924259903823196243692405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616173269215464162461603 924259903823196243692405)
              ·
                refine ⟨86649365983424647846163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924259903823196243692405 86649365983424647846163)
                ·
                  rfl

theorem cell19_284764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_284764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284764 prefixEnd_284764 := by exact prefixLift 284764
  have htrace : WordTrace (prefixWord ++ tailWord_284764) baseStart_284764 baseEnd_284764 := by
    simpa [prefixWord, tailWord_284764, baseEnd_284764] using wordTrace_append hprefix tailTrace_284764
  have hstable : (prefixWord ++ tailWord_284764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284764).length < 2 ^ (prefixWord ++ tailWord_284764).sum := by decide
  have hdescent : baseEnd_284764 < baseStart_284764 := by decide
  rcases family_descends (prefixWord ++ tailWord_284764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284937 : List Nat := [1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_284937 : Nat := 118140960795 + 284937 * 2 ^ 59
def prefixEnd_284937 : Nat := 4983230072969 + 3 ^ 40 * 284937 * 2
def baseEnd_284937 : Nat := 86702007259411506001247

theorem tailTrace_284937 : CollatzResearch.WordTrace tailWord_284937 prefixEnd_284937 86702007259411506001247 := by
  unfold tailWord_284937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10392506168729387210421065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6928337445819591473614043 10392506168729387210421065)
  ·
    refine ⟨7794379626547040407815799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10392506168729387210421065 7794379626547040407815799)
    ·
      refine ⟨11691569439820560611723699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7794379626547040407815799 11691569439820560611723699)
      ·
        refine ⟨17537354159730840917585549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11691569439820560611723699 17537354159730840917585549)
        ·
          refine ⟨6576507809899065344094581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17537354159730840917585549 6576507809899065344094581)
          ·
            refine ⟨616547607178037376008867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6576507809899065344094581 616547607178037376008867)
            ·
              refine ⟨924821410767056064013301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616547607178037376008867 924821410767056064013301)
              ·
                refine ⟨86702007259411506001247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924821410767056064013301 86702007259411506001247)
                ·
                  rfl

theorem cell19_284937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_284937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284937 prefixEnd_284937 := by exact prefixLift 284937
  have htrace : WordTrace (prefixWord ++ tailWord_284937) baseStart_284937 baseEnd_284937 := by
    simpa [prefixWord, tailWord_284937, baseEnd_284937] using wordTrace_append hprefix tailTrace_284937
  have hstable : (prefixWord ++ tailWord_284937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284937).length < 2 ^ (prefixWord ++ tailWord_284937).sum := by decide
  have hdescent : baseEnd_284937 < baseStart_284937 := by decide
  rcases family_descends (prefixWord ++ tailWord_284937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284954 : List Nat := [3, 1, 1, 3, 4, 2, 5]
def baseStart_284954 : Nat := 118140960795 + 284954 * 2 ^ 59
def prefixEnd_284954 : Nat := 4983230072969 + 3 ^ 40 * 284954 * 2
def baseEnd_284954 : Nat := 28902393367186834541141

theorem tailTrace_284954 : CollatzResearch.WordTrace tailWord_284954 prefixEnd_284954 28902393367186834541141 := by
  unfold tailWord_284954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598281552416949778447479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6928750806445199409193277 2598281552416949778447479)
  ·
    refine ⟨3897422328625424667671219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2598281552416949778447479 3897422328625424667671219)
    ·
      refine ⟨5846133492938137001506829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3897422328625424667671219 5846133492938137001506829)
      ·
        refine ⟨2192300059851801375565061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5846133492938137001506829 2192300059851801375565061)
        ·
          refine ⟨411056261222212757918449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2192300059851801375565061 411056261222212757918449)
          ·
            refine ⟨308292195916659568438837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411056261222212757918449 308292195916659568438837)
            ·
              refine ⟨28902393367186834541141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 308292195916659568438837 28902393367186834541141)
              ·
                rfl

theorem cell19_284954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_284954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_284954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_284954 prefixEnd_284954 := by exact prefixLift 284954
  have htrace : WordTrace (prefixWord ++ tailWord_284954) baseStart_284954 baseEnd_284954 := by
    simpa [prefixWord, tailWord_284954, baseEnd_284954] using wordTrace_append hprefix tailTrace_284954
  have hstable : (prefixWord ++ tailWord_284954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284954).length < 2 ^ (prefixWord ++ tailWord_284954).sum := by decide
  have hdescent : baseEnd_284954 < baseStart_284954 := by decide
  rcases family_descends (prefixWord ++ tailWord_284954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285013 : List Nat := [1, 3, 2, 2, 4, 7]
def baseStart_285013 : Nat := 118140960795 + 285013 * 2 ^ 59
def prefixEnd_285013 : Nat := 4983230072969 + 3 ^ 40 * 285013 * 2
def baseEnd_285013 : Nat := 9636125878518427590239

theorem tailTrace_285013 : CollatzResearch.WordTrace tailWord_285013 prefixEnd_285013 9636125878518427590239 := by
  unfold tailWord_285013
  simp only [CollatzResearch.WordTrace]
  refine ⟨10395278116454052190187693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6930185410969368126791795 10395278116454052190187693)
  ·
    refine ⟨3898229293670269571320385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10395278116454052190187693 3898229293670269571320385)
    ·
      refine ⟨2923671970252702178490289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3898229293670269571320385 2923671970252702178490289)
      ·
        refine ⟨2192753977689526633867717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2923671970252702178490289 2192753977689526633867717)
        ·
          refine ⟨411141370816786243850197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2192753977689526633867717 411141370816786243850197)
          ·
            refine ⟨9636125878518427590239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 411141370816786243850197 9636125878518427590239)
            ·
              rfl

theorem cell19_285013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_285013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285013 prefixEnd_285013 := by exact prefixLift 285013
  have htrace : WordTrace (prefixWord ++ tailWord_285013) baseStart_285013 baseEnd_285013 := by
    simpa [prefixWord, tailWord_285013, baseEnd_285013] using wordTrace_append hprefix tailTrace_285013
  have hstable : (prefixWord ++ tailWord_285013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285013).length < 2 ^ (prefixWord ++ tailWord_285013).sum := by decide
  have hdescent : baseEnd_285013 < baseStart_285013 := by decide
  rcases family_descends (prefixWord ++ tailWord_285013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285022 : List Nat := [4, 4, 2, 1, 1, 2, 1, 4]
def baseStart_285022 : Nat := 118140960795 + 285022 * 2 ^ 59
def prefixEnd_285022 : Nat := 4983230072969 + 3 ^ 40 * 285022 * 2
def baseEnd_285022 : Nat := 86727871470156494112127

theorem tailTrace_285022 : CollatzResearch.WordTrace tailWord_285022 prefixEnd_285022 86727871470156494112127 := by
  unfold tailWord_285022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299450796677680840908165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6930404248947631151510213 1299450796677680840908165)
  ·
    refine ⟨243647024377065157670281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1299450796677680840908165 243647024377065157670281)
    ·
      refine ⟨182735268282798868252711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243647024377065157670281 182735268282798868252711)
      ·
        refine ⟨274102902424198302379067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182735268282798868252711 274102902424198302379067)
        ·
          refine ⟨411154353636297453568601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274102902424198302379067 411154353636297453568601)
          ·
            refine ⟨308365765227223090176451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411154353636297453568601 308365765227223090176451)
            ·
              refine ⟨462548647840834635264677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308365765227223090176451 462548647840834635264677)
              ·
                refine ⟨86727871470156494112127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462548647840834635264677 86727871470156494112127)
                ·
                  rfl

theorem cell19_285022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_285022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285022 prefixEnd_285022 := by exact prefixLift 285022
  have htrace : WordTrace (prefixWord ++ tailWord_285022) baseStart_285022 baseEnd_285022 := by
    simpa [prefixWord, tailWord_285022, baseEnd_285022] using wordTrace_append hprefix tailTrace_285022
  have hstable : (prefixWord ++ tailWord_285022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285022).length < 2 ^ (prefixWord ++ tailWord_285022).sum := by decide
  have hdescent : baseEnd_285022 < baseStart_285022 := by decide
  rcases family_descends (prefixWord ++ tailWord_285022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285098 : List Nat := [3, 1, 6, 1, 2, 1, 2, 3]
def baseStart_285098 : Nat := 118140960795 + 285098 * 2 ^ 59
def prefixEnd_285098 : Nat := 4983230072969 + 3 ^ 40 * 285098 * 2
def baseEnd_285098 : Nat := 86750997117410836423031

theorem tailTrace_285098 : CollatzResearch.WordTrace tailWord_285098 prefixEnd_285098 86750997117410836423031 := by
  unfold tailWord_285098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2599594580286527926757987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6932252214097407804687965 2599594580286527926757987)
  ·
    refine ⟨3899391870429791890136981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2599594580286527926757987 3899391870429791890136981)
    ·
      refine ⟨182783993926396494850171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3899391870429791890136981 182783993926396494850171)
      ·
        refine ⟨274175990889594742275257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182783993926396494850171 274175990889594742275257)
        ·
          refine ⟨205631993167196056706443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274175990889594742275257 205631993167196056706443)
          ·
            refine ⟨308447989750794085059665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205631993167196056706443 308447989750794085059665)
            ·
              refine ⟨231335992313095563794749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308447989750794085059665 231335992313095563794749)
              ·
                refine ⟨86750997117410836423031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231335992313095563794749 86750997117410836423031)
                ·
                  rfl

theorem cell19_285098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_285098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285098 prefixEnd_285098 := by exact prefixLift 285098
  have htrace : WordTrace (prefixWord ++ tailWord_285098) baseStart_285098 baseEnd_285098 := by
    simpa [prefixWord, tailWord_285098, baseEnd_285098] using wordTrace_append hprefix tailTrace_285098
  have hstable : (prefixWord ++ tailWord_285098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285098).length < 2 ^ (prefixWord ++ tailWord_285098).sum := by decide
  have hdescent : baseEnd_285098 < baseStart_285098 := by decide
  rcases family_descends (prefixWord ++ tailWord_285098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285121 : List Nat := [1, 2, 7, 1, 1, 2, 5]
def baseStart_285121 : Nat := 118140960795 + 285121 * 2 ^ 59
def prefixEnd_285121 : Nat := 4983230072969 + 3 ^ 40 * 285121 * 2
def baseEnd_285121 : Nat := 28919331889517865970619

theorem tailTrace_285121 : CollatzResearch.WordTrace tailWord_285121 prefixEnd_285121 28919331889517865970619 := by
  unfold tailWord_285121
  simp only [CollatzResearch.WordTrace]
  refine ⟨10399217200062786635119217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6932811466708524423412811 10399217200062786635119217)
  ·
    refine ⟨7799412900047089976339413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10399217200062786635119217 7799412900047089976339413)
    ·
      refine ⟨182798739844853671320455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7799412900047089976339413 182798739844853671320455)
      ·
        refine ⟨274198109767280506980683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182798739844853671320455 274198109767280506980683)
        ·
          refine ⟨411297164650920760471025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274198109767280506980683 411297164650920760471025)
          ·
            refine ⟨308472873488190570353269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411297164650920760471025 308472873488190570353269)
            ·
              refine ⟨28919331889517865970619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 308472873488190570353269 28919331889517865970619)
              ·
                rfl

theorem cell19_285121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_285121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285121 prefixEnd_285121 := by exact prefixLift 285121
  have htrace : WordTrace (prefixWord ++ tailWord_285121) baseStart_285121 baseEnd_285121 := by
    simpa [prefixWord, tailWord_285121, baseEnd_285121] using wordTrace_append hprefix tailTrace_285121
  have hstable : (prefixWord ++ tailWord_285121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285121).length < 2 ^ (prefixWord ++ tailWord_285121).sum := by decide
  have hdescent : baseEnd_285121 < baseStart_285121 := by decide
  rcases family_descends (prefixWord ++ tailWord_285121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285127 : List Nat := [1, 1, 4, 1, 1, 6, 5]
def baseStart_285127 : Nat := 118140960795 + 285127 * 2 ^ 59
def prefixEnd_285127 : Nat := 4983230072969 + 3 ^ 40 * 285127 * 2
def baseEnd_285127 : Nat := 28919940459182453926169

theorem tailTrace_285127 : CollatzResearch.WordTrace tailWord_285127 prefixEnd_285127 28919940459182453926169 := by
  unfold tailWord_285127
  simp only [CollatzResearch.WordTrace]
  refine ⟨10399436038041049659837635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6932957358694033106558423 10399436038041049659837635)
  ·
    refine ⟨15599154057061574489756453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10399436038041049659837635 15599154057061574489756453)
    ·
      refine ⟨2924841385699045216829335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15599154057061574489756453 2924841385699045216829335)
      ·
        refine ⟨4387262078548567825244003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924841385699045216829335 4387262078548567825244003)
        ·
          refine ⟨6580893117822851737866005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387262078548567825244003 6580893117822851737866005)
          ·
            refine ⟨308479364897946175212469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6580893117822851737866005 308479364897946175212469)
            ·
              refine ⟨28919940459182453926169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 308479364897946175212469 28919940459182453926169)
              ·
                rfl

theorem cell19_285127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_285127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285127 prefixEnd_285127 := by exact prefixLift 285127
  have htrace : WordTrace (prefixWord ++ tailWord_285127) baseStart_285127 baseEnd_285127 := by
    simpa [prefixWord, tailWord_285127, baseEnd_285127] using wordTrace_append hprefix tailTrace_285127
  have hstable : (prefixWord ++ tailWord_285127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285127).length < 2 ^ (prefixWord ++ tailWord_285127).sum := by decide
  have hdescent : baseEnd_285127 < baseStart_285127 := by decide
  rcases family_descends (prefixWord ++ tailWord_285127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285129 : List Nat := [1, 2, 1, 1, 2, 1, 11]
def baseStart_285129 : Nat := 118140960795 + 285129 * 2 ^ 59
def prefixEnd_285129 : Nat := 4983230072969 + 3 ^ 40 * 285129 * 2
def baseEnd_285129 : Nat := 28920143315737316578019

theorem tailTrace_285129 : CollatzResearch.WordTrace tailWord_285129 prefixEnd_285129 28920143315737316578019 := by
  unfold tailWord_285129
  simp only [CollatzResearch.WordTrace]
  refine ⟨10399508984033804001410441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6933005989355869334273627 10399508984033804001410441)
  ·
    refine ⟨7799631738025353001057831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10399508984033804001410441 7799631738025353001057831)
    ·
      refine ⟨11699447607038029501586747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7799631738025353001057831 11699447607038029501586747)
      ·
        refine ⟨17549171410557044252380121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11699447607038029501586747 17549171410557044252380121)
        ·
          refine ⟨13161878557917783189285091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17549171410557044252380121 13161878557917783189285091)
          ·
            refine ⟨19742817836876674783927637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13161878557917783189285091 19742817836876674783927637)
            ·
              refine ⟨28920143315737316578019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19742817836876674783927637 28920143315737316578019)
              ·
                rfl

theorem cell19_285129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_285129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285129 prefixEnd_285129 := by exact prefixLift 285129
  have htrace : WordTrace (prefixWord ++ tailWord_285129) baseStart_285129 baseEnd_285129 := by
    simpa [prefixWord, tailWord_285129, baseEnd_285129] using wordTrace_append hprefix tailTrace_285129
  have hstable : (prefixWord ++ tailWord_285129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285129).length < 2 ^ (prefixWord ++ tailWord_285129).sum := by decide
  have hdescent : baseEnd_285129 < baseStart_285129 := by decide
  rcases family_descends (prefixWord ++ tailWord_285129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285146 : List Nat := [3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_285146 : Nat := 118140960795 + 285146 * 2 ^ 59
def prefixEnd_285146 : Nat := 4983230072969 + 3 ^ 40 * 285146 * 2
def baseEnd_285146 : Nat := 86765602789360947356233

theorem tailTrace_285146 : CollatzResearch.WordTrace tailWord_285146 prefixEnd_285146 86765602789360947356233 := by
  unfold tailWord_285146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600032256243053976194823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6933419349981477269852861 2600032256243053976194823)
  ·
    refine ⟨3900048384364580964292235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2600032256243053976194823 3900048384364580964292235)
    ·
      refine ⟨5850072576546871446438353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3900048384364580964292235 5850072576546871446438353)
      ·
        refine ⟨4387554432410153584828765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5850072576546871446438353 4387554432410153584828765)
        ·
          refine ⟨1645332912153807594310787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4387554432410153584828765 1645332912153807594310787)
          ·
            refine ⟨2467999368230711391466181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645332912153807594310787 2467999368230711391466181)
            ·
              refine ⟨462749881543258385899909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2467999368230711391466181 462749881543258385899909)
              ·
                refine ⟨86765602789360947356233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462749881543258385899909 86765602789360947356233)
                ·
                  rfl

theorem cell19_285146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_285146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285146 prefixEnd_285146 := by exact prefixLift 285146
  have htrace : WordTrace (prefixWord ++ tailWord_285146) baseStart_285146 baseEnd_285146 := by
    simpa [prefixWord, tailWord_285146, baseEnd_285146] using wordTrace_append hprefix tailTrace_285146
  have hstable : (prefixWord ++ tailWord_285146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285146).length < 2 ^ (prefixWord ++ tailWord_285146).sum := by decide
  have hdescent : baseEnd_285146 < baseStart_285146 := by decide
  rcases family_descends (prefixWord ++ tailWord_285146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285197 : List Nat := [1, 7, 1, 1, 1, 3, 1, 4]
def baseStart_285197 : Nat := 118140960795 + 285197 * 2 ^ 59
def prefixEnd_285197 : Nat := 4983230072969 + 3 ^ 40 * 285197 * 2
def baseEnd_285197 : Nat := 86781121315807940222761

theorem tailTrace_285197 : CollatzResearch.WordTrace tailWord_285197 prefixEnd_285197 86781121315807940222761 := by
  unfold tailWord_285197
  simp only [CollatzResearch.WordTrace]
  refine ⟨10401989147787451614885845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6934659431858301076590563 10401989147787451614885845)
  ·
    refine ⟨243796620651268397223887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10401989147787451614885845 243796620651268397223887)
    ·
      refine ⟨365694930976902595835831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243796620651268397223887 365694930976902595835831)
      ·
        refine ⟨548542396465353893753747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365694930976902595835831 548542396465353893753747)
        ·
          refine ⟨822813594698030840630621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548542396465353893753747 822813594698030840630621)
          ·
            refine ⟨308555098011761565236483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 822813594698030840630621 308555098011761565236483)
            ·
              refine ⟨462832647017642347854725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308555098011761565236483 462832647017642347854725)
              ·
                refine ⟨86781121315807940222761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462832647017642347854725 86781121315807940222761)
                ·
                  rfl

theorem cell19_285197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_285197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285197 prefixEnd_285197 := by exact prefixLift 285197
  have htrace : WordTrace (prefixWord ++ tailWord_285197) baseStart_285197 baseEnd_285197 := by
    simpa [prefixWord, tailWord_285197, baseEnd_285197] using wordTrace_append hprefix tailTrace_285197
  have hstable : (prefixWord ++ tailWord_285197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285197).length < 2 ^ (prefixWord ++ tailWord_285197).sum := by decide
  have hdescent : baseEnd_285197 < baseStart_285197 := by decide
  rcases family_descends (prefixWord ++ tailWord_285197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285296 : List Nat := [2, 1, 1, 1, 8, 1, 5]
def baseStart_285296 : Nat := 118140960795 + 285296 * 2 ^ 59
def prefixEnd_285296 : Nat := 4983230072969 + 3 ^ 40 * 285296 * 2
def baseEnd_285296 : Nat := 28937081838068348007497

theorem tailTrace_285296 : CollatzResearch.WordTrace tailWord_285296 prefixEnd_285296 28937081838068348007497 := by
  unfold tailWord_285296
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202799987214395761369871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6937066649619194348493161 5202799987214395761369871)
  ·
    refine ⟨7804199980821593642054807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5202799987214395761369871 7804199980821593642054807)
    ·
      refine ⟨11706299971232390463082211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804199980821593642054807 11706299971232390463082211)
      ·
        refine ⟨17559449956848585694623317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11706299971232390463082211 17559449956848585694623317)
        ·
          refine ⟨205774804181819363608867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 17559449956848585694623317 205774804181819363608867)
          ·
            refine ⟨308662206272729045413301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205774804181819363608867 308662206272729045413301)
            ·
              refine ⟨28937081838068348007497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 308662206272729045413301 28937081838068348007497)
              ·
                rfl

theorem cell19_285296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_285296 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285296 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285296 prefixEnd_285296 := by exact prefixLift 285296
  have htrace : WordTrace (prefixWord ++ tailWord_285296) baseStart_285296 baseEnd_285296 := by
    simpa [prefixWord, tailWord_285296, baseEnd_285296] using wordTrace_append hprefix tailTrace_285296
  have hstable : (prefixWord ++ tailWord_285296).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285296).length < 2 ^ (prefixWord ++ tailWord_285296).sum := by decide
  have hdescent : baseEnd_285296 < baseStart_285296 := by decide
  rcases family_descends (prefixWord ++ tailWord_285296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285317 : List Nat := [1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_285317 : Nat := 118140960795 + 285317 * 2 ^ 59
def prefixEnd_285317 : Nat := 4983230072969 + 3 ^ 40 * 285317 * 2
def baseEnd_285317 : Nat := 86817635495683217555767

theorem tailTrace_285317 : CollatzResearch.WordTrace tailWord_285317 prefixEnd_285317 86817635495683217555767 := by
  unfold tailWord_285317
  simp only [CollatzResearch.WordTrace]
  refine ⟨10406365907352712109254205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6937577271568474739502803 10406365907352712109254205)
  ·
    refine ⟨3902387215257267040970327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10406365907352712109254205 3902387215257267040970327)
    ·
      refine ⟨5853580822885900561455491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3902387215257267040970327 5853580822885900561455491)
      ·
        refine ⟨8780371234328850842183237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5853580822885900561455491 8780371234328850842183237)
        ·
          refine ⟨1646319606436659532909357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8780371234328850842183237 1646319606436659532909357)
          ·
            refine ⟨617369852413747324841009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1646319606436659532909357 617369852413747324841009)
            ·
              refine ⟨463027389310310493630757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617369852413747324841009 463027389310310493630757)
              ·
                refine ⟨86817635495683217555767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 463027389310310493630757 86817635495683217555767)
                ·
                  rfl

theorem cell19_285317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_285317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285317 prefixEnd_285317 := by exact prefixLift 285317
  have htrace : WordTrace (prefixWord ++ tailWord_285317) baseStart_285317 baseEnd_285317 := by
    simpa [prefixWord, tailWord_285317, baseEnd_285317] using wordTrace_append hprefix tailTrace_285317
  have hstable : (prefixWord ++ tailWord_285317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285317).length < 2 ^ (prefixWord ++ tailWord_285317).sum := by decide
  have hdescent : baseEnd_285317 < baseStart_285317 := by decide
  rcases family_descends (prefixWord ++ tailWord_285317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285393 : List Nat := [1, 2, 2, 1, 2, 3, 5, 3]
def baseStart_285393 : Nat := 118140960795 + 285393 * 2 ^ 59
def prefixEnd_285393 : Nat := 4983230072969 + 3 ^ 40 * 285393 * 2
def baseEnd_285393 : Nat := 86840761142937559866671

theorem tailTrace_285393 : CollatzResearch.WordTrace tailWord_285393 prefixEnd_285393 86840761142937559866671 := by
  unfold tailWord_285393
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409137855077377089020833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6939425236718251392680555 10409137855077377089020833)
  ·
    refine ⟨7806853391308032816765625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10409137855077377089020833 7806853391308032816765625)
    ·
      refine ⟨5855140043481024612574219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7806853391308032816765625 5855140043481024612574219)
      ·
        refine ⟨8782710065221536918861329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5855140043481024612574219 8782710065221536918861329)
        ·
          refine ⟨6587032548916152689145997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8782710065221536918861329 6587032548916152689145997)
          ·
            refine ⟨2470137205843557258429749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6587032548916152689145997 2470137205843557258429749)
            ·
              refine ⟨231575363047833492977789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2470137205843557258429749 231575363047833492977789)
              ·
                refine ⟨86840761142937559866671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231575363047833492977789 86840761142937559866671)
                ·
                  rfl

theorem cell19_285393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_285393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285393 prefixEnd_285393 := by exact prefixLift 285393
  have htrace : WordTrace (prefixWord ++ tailWord_285393) baseStart_285393 baseEnd_285393 := by
    simpa [prefixWord, tailWord_285393, baseEnd_285393] using wordTrace_append hprefix tailTrace_285393
  have hstable : (prefixWord ++ tailWord_285393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285393).length < 2 ^ (prefixWord ++ tailWord_285393).sum := by decide
  have hdescent : baseEnd_285393 < baseStart_285393 := by decide
  rcases family_descends (prefixWord ++ tailWord_285393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285448 : List Nat := [2, 1, 3, 2, 2, 4, 2, 3]
def baseStart_285448 : Nat := 118140960795 + 285448 * 2 ^ 59
def prefixEnd_285448 : Nat := 4983230072969 + 3 ^ 40 * 285448 * 2
def baseEnd_285448 : Nat := 86857496808713728644299

theorem tailTrace_285448 : CollatzResearch.WordTrace tailWord_285448 prefixEnd_285448 86857496808713728644299 := by
  unfold tailWord_285448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205571934939060741136499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6940762579918747654848665 5205571934939060741136499)
  ·
    refine ⟨7808357902408591111704749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5205571934939060741136499 7808357902408591111704749)
    ·
      refine ⟨2928134213403221666889281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7808357902408591111704749 2928134213403221666889281)
      ·
        refine ⟨2196100660052416250166961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2928134213403221666889281 2196100660052416250166961)
        ·
          refine ⟨1647075495039312187625221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2196100660052416250166961 1647075495039312187625221)
          ·
            refine ⟨308826655319871035179729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1647075495039312187625221 308826655319871035179729)
            ·
              refine ⟨231619991489903276384797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308826655319871035179729 231619991489903276384797)
              ·
                refine ⟨86857496808713728644299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231619991489903276384797 86857496808713728644299)
                ·
                  rfl

theorem cell19_285448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_285448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285448 prefixEnd_285448 := by exact prefixLift 285448
  have htrace : WordTrace (prefixWord ++ tailWord_285448) baseStart_285448 baseEnd_285448 := by
    simpa [prefixWord, tailWord_285448, baseEnd_285448] using wordTrace_append hprefix tailTrace_285448
  have hstable : (prefixWord ++ tailWord_285448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285448).length < 2 ^ (prefixWord ++ tailWord_285448).sum := by decide
  have hdescent : baseEnd_285448 < baseStart_285448 := by decide
  rcases family_descends (prefixWord ++ tailWord_285448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285471 : List Nat := [1, 1, 2, 4, 2, 2, 7]
def baseStart_285471 : Nat := 118140960795 + 285471 * 2 ^ 59
def prefixEnd_285471 : Nat := 4983230072969 + 3 ^ 40 * 285471 * 2
def baseEnd_285471 : Nat := 28954831786618830044375

theorem tailTrace_285471 : CollatzResearch.WordTrace tailWord_285471 prefixEnd_285471 28954831786618830044375 := by
  unfold tailWord_285471
  simp only [CollatzResearch.WordTrace]
  refine ⟨10411982748794796410360267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6941321832529864273573511 10411982748794796410360267)
  ·
    refine ⟨15617974123192194615540401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10411982748794796410360267 15617974123192194615540401)
    ·
      refine ⟨11713480592394145961655301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15617974123192194615540401 11713480592394145961655301)
      ·
        refine ⟨2196277611073902367810369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11713480592394145961655301 2196277611073902367810369)
        ·
          refine ⟨1647208208305426775857777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2196277611073902367810369 1647208208305426775857777)
          ·
            refine ⟨1235406156229070081893333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647208208305426775857777 1235406156229070081893333)
            ·
              refine ⟨28954831786618830044375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1235406156229070081893333 28954831786618830044375)
              ·
                rfl

theorem cell19_285471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_285471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285471 prefixEnd_285471 := by exact prefixLift 285471
  have htrace : WordTrace (prefixWord ++ tailWord_285471) baseStart_285471 baseEnd_285471 := by
    simpa [prefixWord, tailWord_285471, baseEnd_285471] using wordTrace_append hprefix tailTrace_285471
  have hstable : (prefixWord ++ tailWord_285471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285471).length < 2 ^ (prefixWord ++ tailWord_285471).sum := by decide
  have hdescent : baseEnd_285471 < baseStart_285471 := by decide
  rcases family_descends (prefixWord ++ tailWord_285471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285486 : List Nat := [4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_285486 : Nat := 118140960795 + 285486 * 2 ^ 59
def prefixEnd_285486 : Nat := 4983230072969 + 3 ^ 40 * 285486 * 2
def baseEnd_285486 : Nat := 86869059632340899799751

theorem tailTrace_285486 : CollatzResearch.WordTrace tailWord_285486 prefixEnd_285486 86869059632340899799751 := by
  unfold tailWord_285486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301566230467556746519539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6941686562493635981437541 1301566230467556746519539)
  ·
    refine ⟨1952349345701335119779309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1301566230467556746519539 1952349345701335119779309)
    ·
      refine ⟨732131004638000669917241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1952349345701335119779309 732131004638000669917241)
      ·
        refine ⟨549098253478500502437931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 732131004638000669917241 549098253478500502437931)
        ·
          refine ⟨823647380217750753656897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549098253478500502437931 823647380217750753656897)
          ·
            refine ⟨617735535163313065242673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823647380217750753656897 617735535163313065242673)
            ·
              refine ⟨463301651372484798932005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617735535163313065242673 463301651372484798932005)
              ·
                refine ⟨86869059632340899799751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 463301651372484798932005 86869059632340899799751)
                ·
                  rfl

theorem cell19_285486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_285486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285486 prefixEnd_285486 := by exact prefixLift 285486
  have htrace : WordTrace (prefixWord ++ tailWord_285486) baseStart_285486 baseEnd_285486 := by
    simpa [prefixWord, tailWord_285486, baseEnd_285486] using wordTrace_append hprefix tailTrace_285486
  have hstable : (prefixWord ++ tailWord_285486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285486).length < 2 ^ (prefixWord ++ tailWord_285486).sum := by decide
  have hdescent : baseEnd_285486 < baseStart_285486 := by decide
  rcases family_descends (prefixWord ++ tailWord_285486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285547 : List Nat := [1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_285547 : Nat := 118140960795 + 285547 * 2 ^ 59
def prefixEnd_285547 : Nat := 4983230072969 + 3 ^ 40 * 285547 * 2
def baseEnd_285547 : Nat := 86887621007110832444029

theorem tailTrace_285547 : CollatzResearch.WordTrace tailWord_285547 prefixEnd_285547 86887621007110832444029 := by
  unfold tailWord_285547
  simp only [CollatzResearch.WordTrace]
  refine ⟨10414754696519461390126895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6943169797679640926751263 10414754696519461390126895)
  ·
    refine ⟨15622132044779192085190343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10414754696519461390126895 15622132044779192085190343)
    ·
      refine ⟨23433198067168788127785515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15622132044779192085190343 23433198067168788127785515)
      ·
        refine ⟨35149797100753182191678273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23433198067168788127785515 35149797100753182191678273)
        ·
          refine ⟨26362347825564886643758705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35149797100753182191678273 26362347825564886643758705)
          ·
            refine ⟨19771760869173664982819029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26362347825564886643758705 19771760869173664982819029)
            ·
              refine ⟨463400645371257773034821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19771760869173664982819029 463400645371257773034821)
              ·
                refine ⟨86887621007110832444029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 463400645371257773034821 86887621007110832444029)
                ·
                  rfl

theorem cell19_285547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_285547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285547 prefixEnd_285547 := by exact prefixLift 285547
  have htrace : WordTrace (prefixWord ++ tailWord_285547) baseStart_285547 baseEnd_285547 := by
    simpa [prefixWord, tailWord_285547, baseEnd_285547] using wordTrace_append hprefix tailTrace_285547
  have hstable : (prefixWord ++ tailWord_285547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285547).length < 2 ^ (prefixWord ++ tailWord_285547).sum := by decide
  have hdescent : baseEnd_285547 < baseStart_285547 := by decide
  rcases family_descends (prefixWord ++ tailWord_285547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285604 : List Nat := [2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_285604 : Nat := 118140960795 + 285604 * 2 ^ 59
def prefixEnd_285604 : Nat := 4983230072969 + 3 ^ 40 * 285604 * 2
def baseEnd_285604 : Nat := 86904965242551589177207

theorem tailTrace_285604 : CollatzResearch.WordTrace tailWord_285604 prefixEnd_285604 86904965242551589177207 := by
  unfold tailWord_285604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208416828656480062475933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6944555771541973416634577 5208416828656480062475933)
  ·
    refine ⟨1953156310746180023428475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5208416828656480062475933 1953156310746180023428475)
    ·
      refine ⟨2929734466119270035142713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1953156310746180023428475 2929734466119270035142713)
      ·
        refine ⟨2197300849589452526357035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2929734466119270035142713 2197300849589452526357035)
        ·
          refine ⟨3295951274384178789535553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197300849589452526357035 3295951274384178789535553)
          ·
            refine ⟨2471963455788134092151665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295951274384178789535553 2471963455788134092151665)
            ·
              refine ⟨1853972591841100569113749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471963455788134092151665 1853972591841100569113749)
              ·
                refine ⟨86904965242551589177207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1853972591841100569113749 86904965242551589177207)
                ·
                  rfl

theorem cell19_285604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_285604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285604 prefixEnd_285604 := by exact prefixLift 285604
  have htrace : WordTrace (prefixWord ++ tailWord_285604) baseStart_285604 baseEnd_285604 := by
    simpa [prefixWord, tailWord_285604, baseEnd_285604] using wordTrace_append hprefix tailTrace_285604
  have hstable : (prefixWord ++ tailWord_285604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285604).length < 2 ^ (prefixWord ++ tailWord_285604).sum := by decide
  have hdescent : baseEnd_285604 < baseStart_285604 := by decide
  rcases family_descends (prefixWord ++ tailWord_285604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285617 : List Nat := [1, 2, 2, 4, 4, 1, 2, 3]
def baseStart_285617 : Nat := 118140960795 + 285617 * 2 ^ 59
def prefixEnd_285617 : Nat := 4983230072969 + 3 ^ 40 * 285617 * 2
def baseEnd_285617 : Nat := 86908920945371410888283

theorem tailTrace_285617 : CollatzResearch.WordTrace tailWord_285617 prefixEnd_285617 86908920945371410888283 := by
  unfold tailWord_285617
  simp only [CollatzResearch.WordTrace]
  refine ⟨10417307806265863345175105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6944871870843908896783403 10417307806265863345175105)
  ·
    refine ⟨7812980854699397508881329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10417307806265863345175105 7812980854699397508881329)
    ·
      refine ⟨5859735641024548131660997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7812980854699397508881329 5859735641024548131660997)
      ·
        refine ⟨1098700432692102774686437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5859735641024548131660997 1098700432692102774686437)
        ·
          refine ⟨206006331129769270253707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1098700432692102774686437 206006331129769270253707)
          ·
            refine ⟨309009496694653905380561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206006331129769270253707 309009496694653905380561)
            ·
              refine ⟨231757122520990429035421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309009496694653905380561 231757122520990429035421)
              ·
                refine ⟨86908920945371410888283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231757122520990429035421 86908920945371410888283)
                ·
                  rfl

theorem cell19_285617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_285617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285617 prefixEnd_285617 := by exact prefixLift 285617
  have htrace : WordTrace (prefixWord ++ tailWord_285617) baseStart_285617 baseEnd_285617 := by
    simpa [prefixWord, tailWord_285617, baseEnd_285617] using wordTrace_append hprefix tailTrace_285617
  have hstable : (prefixWord ++ tailWord_285617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285617).length < 2 ^ (prefixWord ++ tailWord_285617).sum := by decide
  have hdescent : baseEnd_285617 < baseStart_285617 := by decide
  rcases family_descends (prefixWord ++ tailWord_285617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285636 : List Nat := [2, 3, 3, 3, 2, 1, 5]
def baseStart_285636 : Nat := 118140960795 + 285636 * 2 ^ 59
def prefixEnd_285636 : Nat := 4983230072969 + 3 ^ 40 * 285636 * 2
def baseEnd_285636 : Nat := 28971567452394998822003

theorem tailTrace_285636 : CollatzResearch.WordTrace tailWord_285636 prefixEnd_285636 28971567452394998822003 := by
  unfold tailWord_285636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5209000396598514795058381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6945333862131353060077841 5209000396598514795058381)
  ·
    refine ⟨1953375148724443048146893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5209000396598514795058381 1953375148724443048146893)
    ·
      refine ⟨732515680771666143055085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1953375148724443048146893 732515680771666143055085)
      ·
        refine ⟨274693380289374803645657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 732515680771666143055085 274693380289374803645657)
        ·
          refine ⟨206020035217031102734243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274693380289374803645657 206020035217031102734243)
          ·
            refine ⟨309030052825546654101365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206020035217031102734243 309030052825546654101365)
            ·
              refine ⟨28971567452394998822003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 309030052825546654101365 28971567452394998822003)
              ·
                rfl

theorem cell19_285636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_285636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285636 prefixEnd_285636 := by exact prefixLift 285636
  have htrace : WordTrace (prefixWord ++ tailWord_285636) baseStart_285636 baseEnd_285636 := by
    simpa [prefixWord, tailWord_285636, baseEnd_285636] using wordTrace_append hprefix tailTrace_285636
  have hstable : (prefixWord ++ tailWord_285636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285636).length < 2 ^ (prefixWord ++ tailWord_285636).sum := by decide
  have hdescent : baseEnd_285636 < baseStart_285636 := by decide
  rcases family_descends (prefixWord ++ tailWord_285636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285640 : List Nat := [2, 1, 3, 1, 5, 2, 5]
def baseStart_285640 : Nat := 118140960795 + 285640 * 2 ^ 59
def prefixEnd_285640 : Nat := 4983230072969 + 3 ^ 40 * 285640 * 2
def baseEnd_285640 : Nat := 28971973165504724125703

theorem tailTrace_285640 : CollatzResearch.WordTrace tailWord_285640 prefixEnd_285640 28971973165504724125703 := by
  unfold tailWord_285640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5209073342591269136631187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6945431123455025515508249 5209073342591269136631187)
  ·
    refine ⟨7813610013886903704946781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5209073342591269136631187 7813610013886903704946781)
    ·
      refine ⟨2930103755207588889355043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7813610013886903704946781 2930103755207588889355043)
      ·
        refine ⟨4395155632811383334032565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2930103755207588889355043 4395155632811383334032565)
        ·
          refine ⟨412045840576067187565553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4395155632811383334032565 412045840576067187565553)
          ·
            refine ⟨309034380432050390674165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412045840576067187565553 309034380432050390674165)
            ·
              refine ⟨28971973165504724125703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 309034380432050390674165 28971973165504724125703)
              ·
                rfl

theorem cell19_285640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_285640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285640 prefixEnd_285640 := by exact prefixLift 285640
  have htrace : WordTrace (prefixWord ++ tailWord_285640) baseStart_285640 baseEnd_285640 := by
    simpa [prefixWord, tailWord_285640, baseEnd_285640] using wordTrace_append hprefix tailTrace_285640
  have hstable : (prefixWord ++ tailWord_285640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285640).length < 2 ^ (prefixWord ++ tailWord_285640).sum := by decide
  have hdescent : baseEnd_285640 < baseStart_285640 := by decide
  rcases family_descends (prefixWord ++ tailWord_285640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285756 : List Nat := [2, 2, 2, 2, 2, 3, 6]
def baseStart_285756 : Nat := 118140960795 + 285756 * 2 ^ 59
def prefixEnd_285756 : Nat := 4983230072969 + 3 ^ 40 * 285756 * 2
def baseEnd_285756 : Nat := 28983738845686757933005

theorem tailTrace_285756 : CollatzResearch.WordTrace tailWord_285756 prefixEnd_285756 28983738845686757933005 := by
  unfold tailWord_285756
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211188776381145042242561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6948251701841526722990081 5211188776381145042242561)
  ·
    refine ⟨3908391582285858781681921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5211188776381145042242561 3908391582285858781681921)
    ·
      refine ⟨2931293686714394086261441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3908391582285858781681921 2931293686714394086261441)
      ·
        refine ⟨2198470265035795564696081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2931293686714394086261441 2198470265035795564696081)
        ·
          refine ⟨1648852698776846673522061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2198470265035795564696081 1648852698776846673522061)
          ·
            refine ⟨618319762041317502570773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1648852698776846673522061 618319762041317502570773)
            ·
              refine ⟨28983738845686757933005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 618319762041317502570773 28983738845686757933005)
              ·
                rfl

theorem cell19_285756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_285756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285756 prefixEnd_285756 := by exact prefixLift 285756
  have htrace : WordTrace (prefixWord ++ tailWord_285756) baseStart_285756 baseEnd_285756 := by
    simpa [prefixWord, tailWord_285756, baseEnd_285756] using wordTrace_append hprefix tailTrace_285756
  have hstable : (prefixWord ++ tailWord_285756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285756).length < 2 ^ (prefixWord ++ tailWord_285756).sum := by decide
  have hdescent : baseEnd_285756 < baseStart_285756 := by decide
  rcases family_descends (prefixWord ++ tailWord_285756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285870 : List Nat := [4, 1, 4, 10]
def baseStart_285870 : Nat := 118140960795 + 285870 * 2 ^ 59
def prefixEnd_285870 : Nat := 4983230072969 + 3 ^ 40 * 285870 * 2
def baseEnd_285870 : Nat := 1073900061826441818091

theorem tailTrace_285870 : CollatzResearch.WordTrace tailWord_285870 prefixEnd_285870 1073900061826441818091 := by
  unfold tailWord_285870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303316934293660944266883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6951023649566191702756709 1303316934293660944266883)
  ·
    refine ⟨1954975401440491416400325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1303316934293660944266883 1954975401440491416400325)
    ·
      refine ⟨366557887770092140575061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1954975401440491416400325 366557887770092140575061)
      ·
        refine ⟨1073900061826441818091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 366557887770092140575061 1073900061826441818091)
        ·
          rfl

theorem cell19_285870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 10].length) (baseStart_285870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285870 prefixEnd_285870 := by exact prefixLift 285870
  have htrace : WordTrace (prefixWord ++ tailWord_285870) baseStart_285870 baseEnd_285870 := by
    simpa [prefixWord, tailWord_285870, baseEnd_285870] using wordTrace_append hprefix tailTrace_285870
  have hstable : (prefixWord ++ tailWord_285870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285870).length < 2 ^ (prefixWord ++ tailWord_285870).sum := by decide
  have hdescent : baseEnd_285870 < baseStart_285870 := by decide
  rcases family_descends (prefixWord ++ tailWord_285870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285891 : List Nat := [1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_285891 : Nat := 118140960795 + 285891 * 2 ^ 59
def prefixEnd_285891 : Nat := 4983230072969 + 3 ^ 40 * 285891 * 2
def baseEnd_285891 : Nat := 86992294989419960798647

theorem tailTrace_285891 : CollatzResearch.WordTrace tailWord_285891 prefixEnd_285891 86992294989419960798647 := by
  unfold tailWord_285891
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427301407273208140649527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6951534271515472093766351 10427301407273208140649527)
  ·
    refine ⟨15640952110909812210974291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10427301407273208140649527 15640952110909812210974291)
    ·
      refine ⟨23461428166364718316461437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15640952110909812210974291 23461428166364718316461437)
      ·
        refine ⟨8798035562386769368673039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23461428166364718316461437 8798035562386769368673039)
        ·
          refine ⟨13197053343580154053009559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8798035562386769368673039 13197053343580154053009559)
          ·
            refine ⟨19795580015370231079514339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13197053343580154053009559 19795580015370231079514339)
            ·
              refine ⟨29693370023055346619271509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19795580015370231079514339 29693370023055346619271509)
              ·
                refine ⟨86992294989419960798647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29693370023055346619271509 86992294989419960798647)
                ·
                  rfl

theorem cell19_285891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_285891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285891 prefixEnd_285891 := by exact prefixLift 285891
  have htrace : WordTrace (prefixWord ++ tailWord_285891) baseStart_285891 baseEnd_285891 := by
    simpa [prefixWord, tailWord_285891, baseEnd_285891] using wordTrace_append hprefix tailTrace_285891
  have hstable : (prefixWord ++ tailWord_285891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285891).length < 2 ^ (prefixWord ++ tailWord_285891).sum := by decide
  have hdescent : baseEnd_285891 < baseStart_285891 := by decide
  rcases family_descends (prefixWord ++ tailWord_285891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285906 : List Nat := [3, 2, 2, 2, 1, 1, 5, 3]
def baseStart_285906 : Nat := 118140960795 + 285906 * 2 ^ 59
def prefixEnd_285906 : Nat := 4983230072969 + 3 ^ 40 * 285906 * 2
def baseEnd_285906 : Nat := 86996859261904370465273

theorem tailTrace_285906 : CollatzResearch.WordTrace tailWord_285906 prefixEnd_285906 86996859261904370465273 := by
  unfold tailWord_285906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606962125554716425611393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6951899001479243801630381 2606962125554716425611393)
  ·
    refine ⟨1955221594166037319208545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2606962125554716425611393 1955221594166037319208545)
    ·
      refine ⟨1466416195624527989406409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1955221594166037319208545 1466416195624527989406409)
      ·
        refine ⟨1099812146718395992054807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1466416195624527989406409 1099812146718395992054807)
        ·
          refine ⟨1649718220077593988082211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099812146718395992054807 1649718220077593988082211)
          ·
            refine ⟨2474577330116390982123317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649718220077593988082211 2474577330116390982123317)
            ·
              refine ⟨231991624698411654574061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2474577330116390982123317 231991624698411654574061)
              ·
                refine ⟨86996859261904370465273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231991624698411654574061 86996859261904370465273)
                ·
                  rfl

theorem cell19_285906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_285906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285906 prefixEnd_285906 := by exact prefixLift 285906
  have htrace : WordTrace (prefixWord ++ tailWord_285906) baseStart_285906 baseEnd_285906 := by
    simpa [prefixWord, tailWord_285906, baseEnd_285906] using wordTrace_append hprefix tailTrace_285906
  have hstable : (prefixWord ++ tailWord_285906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285906).length < 2 ^ (prefixWord ++ tailWord_285906).sum := by decide
  have hdescent : baseEnd_285906 < baseStart_285906 := by decide
  rcases family_descends (prefixWord ++ tailWord_285906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285963 : List Nat := [1, 1, 1, 1, 5, 5, 2, 3]
def baseStart_285963 : Nat := 118140960795 + 285963 * 2 ^ 59
def prefixEnd_285963 : Nat := 4983230072969 + 3 ^ 40 * 285963 * 2
def baseEnd_285963 : Nat := 87014203497345127198451

theorem tailTrace_285963 : CollatzResearch.WordTrace tailWord_285963 prefixEnd_285963 87014203497345127198451 := by
  unfold tailWord_285963
  simp only [CollatzResearch.WordTrace]
  refine ⟨10429927463012364437270543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6953284975341576291513695 10429927463012364437270543)
  ·
    refine ⟨15644891194518546655905815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10429927463012364437270543 15644891194518546655905815)
    ·
      refine ⟨23467336791777819983858723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15644891194518546655905815 23467336791777819983858723)
      ·
        refine ⟨35201005187666729975788085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23467336791777819983858723 35201005187666729975788085)
        ·
          refine ⟨3300094236343755935230133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35201005187666729975788085 3300094236343755935230133)
          ·
            refine ⟨309383834657227118927825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3300094236343755935230133 309383834657227118927825)
            ·
              refine ⟨232037875992920339195869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309383834657227118927825 232037875992920339195869)
              ·
                refine ⟨87014203497345127198451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232037875992920339195869 87014203497345127198451)
                ·
                  rfl

theorem cell19_285963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_285963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_285963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_285963 prefixEnd_285963 := by exact prefixLift 285963
  have htrace : WordTrace (prefixWord ++ tailWord_285963) baseStart_285963 baseEnd_285963 := by
    simpa [prefixWord, tailWord_285963, baseEnd_285963] using wordTrace_append hprefix tailTrace_285963
  have hstable : (prefixWord ++ tailWord_285963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285963).length < 2 ^ (prefixWord ++ tailWord_285963).sum := by decide
  have hdescent : baseEnd_285963 < baseStart_285963 := by decide
  rcases family_descends (prefixWord ++ tailWord_285963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286003 : List Nat := [1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_286003 : Nat := 118140960795 + 286003 * 2 ^ 59
def prefixEnd_286003 : Nat := 4983230072969 + 3 ^ 40 * 286003 * 2
def baseEnd_286003 : Nat := 87026374890636886309453

theorem tailTrace_286003 : CollatzResearch.WordTrace tailWord_286003 prefixEnd_286003 87026374890636886309453 := by
  unfold tailWord_286003
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431386382867451268726663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6954257588578300845817775 10431386382867451268726663)
  ·
    refine ⟨15647079574301176903089995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10431386382867451268726663 15647079574301176903089995)
    ·
      refine ⟨23470619361451765354634993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15647079574301176903089995 23470619361451765354634993)
      ·
        refine ⟨17602964521088824015976245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23470619361451765354634993 17602964521088824015976245)
        ·
          refine ⟨1650277923852077251497773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17602964521088824015976245 1650277923852077251497773)
          ·
            refine ⟨618854221444528969311665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1650277923852077251497773 618854221444528969311665)
            ·
              refine ⟨464140666083396726983749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618854221444528969311665 464140666083396726983749)
              ·
                refine ⟨87026374890636886309453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464140666083396726983749 87026374890636886309453)
                ·
                  rfl

theorem cell19_286003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_286003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286003 prefixEnd_286003 := by exact prefixLift 286003
  have htrace : WordTrace (prefixWord ++ tailWord_286003) baseStart_286003 baseEnd_286003 := by
    simpa [prefixWord, tailWord_286003, baseEnd_286003] using wordTrace_append hprefix tailTrace_286003
  have hstable : (prefixWord ++ tailWord_286003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286003).length < 2 ^ (prefixWord ++ tailWord_286003).sum := by decide
  have hdescent : baseEnd_286003 < baseStart_286003 := by decide
  rcases family_descends (prefixWord ++ tailWord_286003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286020 : List Nat := [2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_286020 : Nat := 118140960795 + 286020 * 2 ^ 59
def prefixEnd_286020 : Nat := 4983230072969 + 3 ^ 40 * 286020 * 2
def baseEnd_286020 : Nat := 87031547732785883931629

theorem tailTrace_286020 : CollatzResearch.WordTrace tailWord_286020 prefixEnd_286020 87031547732785883931629 := by
  unfold tailWord_286020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5216003211902931586047757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6954670949203908781397009 5216003211902931586047757)
  ·
    refine ⟨1956001204463599344767909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5216003211902931586047757 1956001204463599344767909)
    ·
      refine ⟨366750225836924877143983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1956001204463599344767909 366750225836924877143983)
      ·
        refine ⟨550125338755387315715975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366750225836924877143983 550125338755387315715975)
        ·
          refine ⟨825188008133080973573963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550125338755387315715975 825188008133080973573963)
          ·
            refine ⟨1237782012199621460360945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825188008133080973573963 1237782012199621460360945)
            ·
              refine ⟨928336509149716095270709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237782012199621460360945 928336509149716095270709)
              ·
                refine ⟨87031547732785883931629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 928336509149716095270709 87031547732785883931629)
                ·
                  rfl

theorem cell19_286020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_286020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286020 prefixEnd_286020 := by exact prefixLift 286020
  have htrace : WordTrace (prefixWord ++ tailWord_286020) baseStart_286020 baseEnd_286020 := by
    simpa [prefixWord, tailWord_286020, baseEnd_286020] using wordTrace_append hprefix tailTrace_286020
  have hstable : (prefixWord ++ tailWord_286020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286020).length < 2 ^ (prefixWord ++ tailWord_286020).sum := by decide
  have hdescent : baseEnd_286020 < baseStart_286020 := by decide
  rcases family_descends (prefixWord ++ tailWord_286020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286056 : List Nat := [2, 1, 4, 2, 4, 1, 1, 4]
def baseStart_286056 : Nat := 118140960795 + 286056 * 2 ^ 59
def prefixEnd_286056 : Nat := 4983230072969 + 3 ^ 40 * 286056 * 2
def baseEnd_286056 : Nat := 87042501986748467131531

theorem tailTrace_286056 : CollatzResearch.WordTrace tailWord_286056 prefixEnd_286056 87042501986748467131531 := by
  unfold tailWord_286056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5216659725837720660203011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6955546301116960880270681 5216659725837720660203011)
  ·
    refine ⟨7824989588756580990304517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5216659725837720660203011 7824989588756580990304517)
    ·
      refine ⟨1467185547891858935682097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7824989588756580990304517 1467185547891858935682097)
      ·
        refine ⟨1100389160918894201761573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1467185547891858935682097 1100389160918894201761573)
        ·
          refine ⟨206322967672292662830295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1100389160918894201761573 206322967672292662830295)
          ·
            refine ⟨309484451508438994245443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206322967672292662830295 309484451508438994245443)
            ·
              refine ⟨464226677262658491368165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309484451508438994245443 464226677262658491368165)
              ·
                refine ⟨87042501986748467131531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464226677262658491368165 87042501986748467131531)
                ·
                  rfl

theorem cell19_286056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_286056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286056 prefixEnd_286056 := by exact prefixLift 286056
  have htrace : WordTrace (prefixWord ++ tailWord_286056) baseStart_286056 baseEnd_286056 := by
    simpa [prefixWord, tailWord_286056, baseEnd_286056] using wordTrace_append hprefix tailTrace_286056
  have hstable : (prefixWord ++ tailWord_286056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286056).length < 2 ^ (prefixWord ++ tailWord_286056).sum := by decide
  have hdescent : baseEnd_286056 < baseStart_286056 := by decide
  rcases family_descends (prefixWord ++ tailWord_286056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286060 : List Nat := [2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_286060 : Nat := 118140960795 + 286060 * 2 ^ 59
def prefixEnd_286060 : Nat := 4983230072969 + 3 ^ 40 * 286060 * 2
def baseEnd_286060 : Nat := 87043719126077643042631

theorem tailTrace_286060 : CollatzResearch.WordTrace tailWord_286060 prefixEnd_286060 87043719126077643042631 := by
  unfold tailWord_286060
  simp only [CollatzResearch.WordTrace]
  refine ⟨5216732671830475001775817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6955643562440633335701089 5216732671830475001775817)
  ·
    refine ⟨3912549503872856251331863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5216732671830475001775817 3912549503872856251331863)
    ·
      refine ⟨5868824255809284376997795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3912549503872856251331863 5868824255809284376997795)
      ·
        refine ⟨8803236383713926565496693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5868824255809284376997795 8803236383713926565496693)
        ·
          refine ⟨825303410973180615515315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8803236383713926565496693 825303410973180615515315)
          ·
            refine ⟨1237955116459770923272973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825303410973180615515315 1237955116459770923272973)
            ·
              refine ⟨464233168672414096227365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1237955116459770923272973 464233168672414096227365)
              ·
                refine ⟨87043719126077643042631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464233168672414096227365 87043719126077643042631)
                ·
                  rfl

theorem cell19_286060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_286060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286060 prefixEnd_286060 := by exact prefixLift 286060
  have htrace : WordTrace (prefixWord ++ tailWord_286060) baseStart_286060 baseEnd_286060 := by
    simpa [prefixWord, tailWord_286060, baseEnd_286060] using wordTrace_append hprefix tailTrace_286060
  have hstable : (prefixWord ++ tailWord_286060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286060).length < 2 ^ (prefixWord ++ tailWord_286060).sum := by decide
  have hdescent : baseEnd_286060 < baseStart_286060 := by decide
  rcases family_descends (prefixWord ++ tailWord_286060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286136 : List Nat := [2, 1, 2, 1, 2, 2, 6, 3]
def baseStart_286136 : Nat := 118140960795 + 286136 * 2 ^ 59
def prefixEnd_286136 : Nat := 4983230072969 + 3 ^ 40 * 286136 * 2
def baseEnd_286136 : Nat := 87066844773331985353535

theorem tailTrace_286136 : CollatzResearch.WordTrace tailWord_286136 prefixEnd_286136 87066844773331985353535 := by
  unfold tailWord_286136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218118645692807491659131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6957491527590409988878841 5218118645692807491659131)
  ·
    refine ⟨7827177968539211237488697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5218118645692807491659131 7827177968539211237488697)
    ·
      refine ⟨5870383476404408428116523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7827177968539211237488697 5870383476404408428116523)
      ·
        refine ⟨8805575214606612642174785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5870383476404408428116523 8805575214606612642174785)
        ·
          refine ⟨6604181410954959481631089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8805575214606612642174785 6604181410954959481631089)
          ·
            refine ⟨4953136058216219611223317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6604181410954959481631089 4953136058216219611223317)
            ·
              refine ⟨232178252728885294276093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4953136058216219611223317 232178252728885294276093)
              ·
                refine ⟨87066844773331985353535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232178252728885294276093 87066844773331985353535)
                ·
                  rfl

theorem cell19_286136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_286136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286136 prefixEnd_286136 := by exact prefixLift 286136
  have htrace : WordTrace (prefixWord ++ tailWord_286136) baseStart_286136 baseEnd_286136 := by
    simpa [prefixWord, tailWord_286136, baseEnd_286136] using wordTrace_append hprefix tailTrace_286136
  have hstable : (prefixWord ++ tailWord_286136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286136).length < 2 ^ (prefixWord ++ tailWord_286136).sum := by decide
  have hdescent : baseEnd_286136 < baseStart_286136 := by decide
  rcases family_descends (prefixWord ++ tailWord_286136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286212 : List Nat := [2, 3, 2, 3, 2, 7]
def baseStart_286212 : Nat := 118140960795 + 286212 * 2 ^ 59
def prefixEnd_286212 : Nat := 4983230072969 + 3 ^ 40 * 286212 * 2
def baseEnd_286212 : Nat := 9676663380065147518271

theorem tailTrace_286212 : CollatzResearch.WordTrace tailWord_286212 prefixEnd_286212 9676663380065147518271 := by
  unfold tailWord_286212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5219504619555139981542445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6959339492740186642056593 5219504619555139981542445)
  ·
    refine ⟨1957314232333177493078417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5219504619555139981542445 1957314232333177493078417)
    ·
      refine ⟨1467985674249883119808813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1957314232333177493078417 1467985674249883119808813)
      ·
        refine ⟨550494627843706169928305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1467985674249883119808813 550494627843706169928305)
        ·
          refine ⟨412870970882779627446229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550494627843706169928305 412870970882779627446229)
          ·
            refine ⟨9676663380065147518271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 412870970882779627446229 9676663380065147518271)
            ·
              rfl

theorem cell19_286212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_286212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286212 prefixEnd_286212 := by exact prefixLift 286212
  have htrace : WordTrace (prefixWord ++ tailWord_286212) baseStart_286212 baseEnd_286212 := by
    simpa [prefixWord, tailWord_286212, baseEnd_286212] using wordTrace_append hprefix tailTrace_286212
  have hstable : (prefixWord ++ tailWord_286212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286212).length < 2 ^ (prefixWord ++ tailWord_286212).sum := by decide
  have hdescent : baseEnd_286212 < baseStart_286212 := by decide
  rcases family_descends (prefixWord ++ tailWord_286212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286269 : List Nat := [1, 4, 1, 3, 3, 1, 6]
def baseStart_286269 : Nat := 118140960795 + 286269 * 2 ^ 59
def prefixEnd_286269 : Nat := 4983230072969 + 3 ^ 40 * 286269 * 2
def baseEnd_286269 : Nat := 29035771552009028132539

theorem tailTrace_286269 : CollatzResearch.WordTrace tailWord_286269 prefixEnd_286269 29035771552009028132539 := by
  unfold tailWord_286269
  simp only [CollatzResearch.WordTrace]
  refine ⟨10441088199903778697909861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6960725466602519131939907 10441088199903778697909861)
  ·
    refine ⟨1957704037481958505858099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10441088199903778697909861 1957704037481958505858099)
    ·
      refine ⟨2936556056222937758787149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957704037481958505858099 2936556056222937758787149)
      ·
        refine ⟨1101208521083601659545181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2936556056222937758787149 1101208521083601659545181)
        ·
          refine ⟨412953195406350622329443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1101208521083601659545181 412953195406350622329443)
          ·
            refine ⟨619429793109525933494165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412953195406350622329443 619429793109525933494165)
            ·
              refine ⟨29035771552009028132539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 619429793109525933494165 29035771552009028132539)
              ·
                rfl

theorem cell19_286269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_286269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286269 prefixEnd_286269 := by exact prefixLift 286269
  have htrace : WordTrace (prefixWord ++ tailWord_286269) baseStart_286269 baseEnd_286269 := by
    simpa [prefixWord, tailWord_286269, baseEnd_286269] using wordTrace_append hprefix tailTrace_286269
  have hstable : (prefixWord ++ tailWord_286269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286269).length < 2 ^ (prefixWord ++ tailWord_286269).sum := by decide
  have hdescent : baseEnd_286269 < baseStart_286269 := by decide
  rcases family_descends (prefixWord ++ tailWord_286269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286271 : List Nat := [1, 1, 2, 2, 3, 4, 6]
def baseStart_286271 : Nat := 118140960795 + 286271 * 2 ^ 59
def prefixEnd_286271 : Nat := 4983230072969 + 3 ^ 40 * 286271 * 2
def baseEnd_286271 : Nat := 29035974408563890784389

theorem tailTrace_286271 : CollatzResearch.WordTrace tailWord_286271 prefixEnd_286271 29035974408563890784389 := by
  unfold tailWord_286271
  simp only [CollatzResearch.WordTrace]
  refine ⟨10441161145896533039482667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6960774097264355359655111 10441161145896533039482667)
  ·
    refine ⟨15661741718844799559224001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10441161145896533039482667 15661741718844799559224001)
    ·
      refine ⟨11746306289133599669418001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15661741718844799559224001 11746306289133599669418001)
      ·
        refine ⟨8809729716850199752063501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11746306289133599669418001 8809729716850199752063501)
        ·
          refine ⟨3303648643818824907023813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8809729716850199752063501 3303648643818824907023813)
          ·
            refine ⟨619434120716029670066965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3303648643818824907023813 619434120716029670066965)
            ·
              refine ⟨29035974408563890784389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 619434120716029670066965 29035974408563890784389)
              ·
                rfl

theorem cell19_286271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_286271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286271 prefixEnd_286271 := by exact prefixLift 286271
  have htrace : WordTrace (prefixWord ++ tailWord_286271) baseStart_286271 baseEnd_286271 := by
    simpa [prefixWord, tailWord_286271, baseEnd_286271] using wordTrace_append hprefix tailTrace_286271
  have hstable : (prefixWord ++ tailWord_286271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286271).length < 2 ^ (prefixWord ++ tailWord_286271).sum := by decide
  have hdescent : baseEnd_286271 < baseStart_286271 := by decide
  rcases family_descends (prefixWord ++ tailWord_286271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286301 : List Nat := [1, 4, 4, 2, 1, 2, 2, 3]
def baseStart_286301 : Nat := 118140960795 + 286301 * 2 ^ 59
def prefixEnd_286301 : Nat := 4983230072969 + 3 ^ 40 * 286301 * 2
def baseEnd_286301 : Nat := 87117051770660491686419

theorem tailTrace_286301 : CollatzResearch.WordTrace tailWord_286301 prefixEnd_286301 87117051770660491686419 := by
  unfold tailWord_286301
  simp only [CollatzResearch.WordTrace]
  refine ⟨10442255335787848163074757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6961503557191898775383171 10442255335787848163074757)
  ·
    refine ⟨1957922875460221530576517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10442255335787848163074757 1957922875460221530576517)
    ·
      refine ⟨367110539148791536983097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1957922875460221530576517 367110539148791536983097)
      ·
        refine ⟨275332904361593652737323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367110539148791536983097 275332904361593652737323)
        ·
          refine ⟨412999356542390479105985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275332904361593652737323 412999356542390479105985)
          ·
            refine ⟨309749517406792859329489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412999356542390479105985 309749517406792859329489)
            ·
              refine ⟨232312138055094644497117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309749517406792859329489 232312138055094644497117)
              ·
                refine ⟨87117051770660491686419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232312138055094644497117 87117051770660491686419)
                ·
                  rfl

theorem cell19_286301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_286301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286301 prefixEnd_286301 := by exact prefixLift 286301
  have htrace : WordTrace (prefixWord ++ tailWord_286301) baseStart_286301 baseEnd_286301 := by
    simpa [prefixWord, tailWord_286301, baseEnd_286301] using wordTrace_append hprefix tailTrace_286301
  have hstable : (prefixWord ++ tailWord_286301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286301).length < 2 ^ (prefixWord ++ tailWord_286301).sum := by decide
  have hdescent : baseEnd_286301 < baseStart_286301 := by decide
  rcases family_descends (prefixWord ++ tailWord_286301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286307 : List Nat := [1, 1, 1, 5, 1, 3, 4, 3]
def baseStart_286307 : Nat := 118140960795 + 286307 * 2 ^ 59
def prefixEnd_286307 : Nat := 4983230072969 + 3 ^ 40 * 286307 * 2
def baseEnd_286307 : Nat := 87118877479654255553069

theorem tailTrace_286307 : CollatzResearch.WordTrace tailWord_286307 prefixEnd_286307 87118877479654255553069 := by
  unfold tailWord_286307
  simp only [CollatzResearch.WordTrace]
  refine ⟨10442474173766111187793175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6961649449177407458528783 10442474173766111187793175)
  ·
    refine ⟨15663711260649166781689763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10442474173766111187793175 15663711260649166781689763)
    ·
      refine ⟨23495566890973750172534645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15663711260649166781689763 23495566890973750172534645)
      ·
        refine ⟨2202709396028789078675123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23495566890973750172534645 2202709396028789078675123)
        ·
          refine ⟨3304064094043183618012685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202709396028789078675123 3304064094043183618012685)
          ·
            refine ⟨1239024035266193856754757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3304064094043183618012685 1239024035266193856754757)
            ·
              refine ⟨232317006612411348141517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1239024035266193856754757 232317006612411348141517)
              ·
                refine ⟨87118877479654255553069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232317006612411348141517 87118877479654255553069)
                ·
                  rfl

theorem cell19_286307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_286307 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286307 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286307 prefixEnd_286307 := by exact prefixLift 286307
  have htrace : WordTrace (prefixWord ++ tailWord_286307) baseStart_286307 baseEnd_286307 := by
    simpa [prefixWord, tailWord_286307, baseEnd_286307] using wordTrace_append hprefix tailTrace_286307
  have hstable : (prefixWord ++ tailWord_286307).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286307).length < 2 ^ (prefixWord ++ tailWord_286307).sum := by decide
  have hdescent : baseEnd_286307 < baseStart_286307 := by decide
  rcases family_descends (prefixWord ++ tailWord_286307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286326 : List Nat := [5, 1, 1, 2, 2, 1, 7]
def baseStart_286326 : Nat := 118140960795 + 286326 * 2 ^ 59
def prefixEnd_286326 : Nat := 4983230072969 + 3 ^ 40 * 286326 * 2
def baseEnd_286326 : Nat := 29041552963822613710265

theorem tailTrace_286326 : CollatzResearch.WordTrace tailWord_286326 prefixEnd_286326 29041552963822613710265 := by
  unfold tailWord_286326
  simp only [CollatzResearch.WordTrace]
  refine ⟨652697947543579839545927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6962111440464851621823221 652697947543579839545927)
  ·
    refine ⟨979046921315369759318891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652697947543579839545927 979046921315369759318891)
    ·
      refine ⟨1468570381973054638978337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 979046921315369759318891 1468570381973054638978337)
      ·
        refine ⟨1101427786479790979233753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1468570381973054638978337 1101427786479790979233753)
        ·
          refine ⟨826070839859843234425315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1101427786479790979233753 826070839859843234425315)
          ·
            refine ⟨1239106259789764851637973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826070839859843234425315 1239106259789764851637973)
            ·
              refine ⟨29041552963822613710265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1239106259789764851637973 29041552963822613710265)
              ·
                rfl

theorem cell19_286326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_286326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286326 prefixEnd_286326 := by exact prefixLift 286326
  have htrace : WordTrace (prefixWord ++ tailWord_286326) baseStart_286326 baseEnd_286326 := by
    simpa [prefixWord, tailWord_286326, baseEnd_286326] using wordTrace_append hprefix tailTrace_286326
  have hstable : (prefixWord ++ tailWord_286326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286326).length < 2 ^ (prefixWord ++ tailWord_286326).sum := by decide
  have hdescent : baseEnd_286326 < baseStart_286326 := by decide
  rcases family_descends (prefixWord ++ tailWord_286326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286347 : List Nat := [1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_286347 : Nat := 118140960795 + 286347 * 2 ^ 59
def prefixEnd_286347 : Nat := 4983230072969 + 3 ^ 40 * 286347 * 2
def baseEnd_286347 : Nat := 87131048872946014664071

theorem tailTrace_286347 : CollatzResearch.WordTrace tailWord_286347 prefixEnd_286347 87131048872946014664071 := by
  unfold tailWord_286347
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443933093621198019249295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6962622062414132012832863 10443933093621198019249295)
  ·
    refine ⟨15665899640431797028873943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10443933093621198019249295 15665899640431797028873943)
    ·
      refine ⟨23498849460647695543310915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15665899640431797028873943 23498849460647695543310915)
      ·
        refine ⟨35248274190971543314966373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23498849460647695543310915 35248274190971543314966373)
        ·
          refine ⟨6609051410807164371556195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35248274190971543314966373 6609051410807164371556195)
          ·
            refine ⟨9913577116210746557334293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609051410807164371556195 9913577116210746557334293)
            ·
              refine ⟨464698927322378744875045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9913577116210746557334293 464698927322378744875045)
              ·
                refine ⟨87131048872946014664071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464698927322378744875045 87131048872946014664071)
                ·
                  rfl

theorem cell19_286347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_286347 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286347 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286347 prefixEnd_286347 := by exact prefixLift 286347
  have htrace : WordTrace (prefixWord ++ tailWord_286347) baseStart_286347 baseEnd_286347 := by
    simpa [prefixWord, tailWord_286347, baseEnd_286347] using wordTrace_append hprefix tailTrace_286347
  have hstable : (prefixWord ++ tailWord_286347).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286347).length < 2 ^ (prefixWord ++ tailWord_286347).sum := by decide
  have hdescent : baseEnd_286347 < baseStart_286347 := by decide
  rcases family_descends (prefixWord ++ tailWord_286347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286470 : List Nat := [6, 2, 2, 1, 1, 1, 1, 5]
def baseStart_286470 : Nat := 118140960795 + 286470 * 2 ^ 59
def prefixEnd_286470 : Nat := 4983230072969 + 3 ^ 40 * 286470 * 2
def baseEnd_286470 : Nat := 87168475907318173930403

theorem tailTrace_286470 : CollatzResearch.WordTrace tailWord_286470 prefixEnd_286470 87168475907318173930403 := by
  unfold tailWord_286470
  simp only [CollatzResearch.WordTrace]
  refine ⟨326513102255487188311777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6965612848117060017317909 326513102255487188311777)
  ·
    refine ⟨244884826691615391233833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 326513102255487188311777 244884826691615391233833)
    ·
      refine ⟨183663620018711543425375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244884826691615391233833 183663620018711543425375)
      ·
        refine ⟨275495430028067315138063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183663620018711543425375 275495430028067315138063)
        ·
          refine ⟨413243145042100972707095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275495430028067315138063 413243145042100972707095)
          ·
            refine ⟨619864717563151459060643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413243145042100972707095 619864717563151459060643)
            ·
              refine ⟨929797076344727188590965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619864717563151459060643 929797076344727188590965)
              ·
                refine ⟨87168475907318173930403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 929797076344727188590965 87168475907318173930403)
                ·
                  rfl

theorem cell19_286470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_286470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286470 prefixEnd_286470 := by exact prefixLift 286470
  have htrace : WordTrace (prefixWord ++ tailWord_286470) baseStart_286470 baseEnd_286470 := by
    simpa [prefixWord, tailWord_286470, baseEnd_286470] using wordTrace_append hprefix tailTrace_286470
  have hstable : (prefixWord ++ tailWord_286470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286470).length < 2 ^ (prefixWord ++ tailWord_286470).sum := by decide
  have hdescent : baseEnd_286470 < baseStart_286470 := by decide
  rcases family_descends (prefixWord ++ tailWord_286470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286478 : List Nat := [4, 1, 1, 2, 1, 1, 6, 3]
def baseStart_286478 : Nat := 118140960795 + 286478 * 2 ^ 59
def prefixEnd_286478 : Nat := 4983230072969 + 3 ^ 40 * 286478 * 2
def baseEnd_286478 : Nat := 87170910185976525752603

theorem tailTrace_286478 : CollatzResearch.WordTrace tailWord_286478 prefixEnd_286478 87170910185976525752603 := by
  unfold tailWord_286478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306088882018325924033511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6965807370764404928178725 1306088882018325924033511)
  ·
    refine ⟨1959133323027488886050267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306088882018325924033511 1959133323027488886050267)
    ·
      refine ⟨2938699984541233329075401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959133323027488886050267 2938699984541233329075401)
      ·
        refine ⟨2204024988405924996806551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2938699984541233329075401 2204024988405924996806551)
        ·
          refine ⟨3306037482608887495209827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204024988405924996806551 3306037482608887495209827)
          ·
            refine ⟨4959056223913331242814741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306037482608887495209827 4959056223913331242814741)
            ·
              refine ⟨232455760495937402006941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4959056223913331242814741 232455760495937402006941)
              ·
                refine ⟨87170910185976525752603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232455760495937402006941 87170910185976525752603)
                ·
                  rfl

theorem cell19_286478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_286478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286478 prefixEnd_286478 := by exact prefixLift 286478
  have htrace : WordTrace (prefixWord ++ tailWord_286478) baseStart_286478 baseEnd_286478 := by
    simpa [prefixWord, tailWord_286478, baseEnd_286478] using wordTrace_append hprefix tailTrace_286478
  have hstable : (prefixWord ++ tailWord_286478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286478).length < 2 ^ (prefixWord ++ tailWord_286478).sum := by decide
  have hdescent : baseEnd_286478 < baseStart_286478 := by decide
  rcases family_descends (prefixWord ++ tailWord_286478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286516 : List Nat := [2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_286516 : Nat := 118140960795 + 286516 * 2 ^ 59
def prefixEnd_286516 : Nat := 4983230072969 + 3 ^ 40 * 286516 * 2
def baseEnd_286516 : Nat := 87182473009603696908055

theorem tailTrace_286516 : CollatzResearch.WordTrace tailWord_286516 prefixEnd_286516 87182473009603696908055 := by
  unfold tailWord_286516
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225048515004469941075701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6966731353339293254767601 5225048515004469941075701)
  ·
    refine ⟨489848298281669056975847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5225048515004469941075701 489848298281669056975847)
    ·
      refine ⟨734772447422503585463771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489848298281669056975847 734772447422503585463771)
      ·
        refine ⟨1102158671133755378195657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734772447422503585463771 1102158671133755378195657)
        ·
          refine ⟨826619003350316533646743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102158671133755378195657 826619003350316533646743)
          ·
            refine ⟨1239928505025474800470115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826619003350316533646743 1239928505025474800470115)
            ·
              refine ⟨1859892757538212200705173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239928505025474800470115 1859892757538212200705173)
              ·
                refine ⟨87182473009603696908055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1859892757538212200705173 87182473009603696908055)
                ·
                  rfl

theorem cell19_286516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_286516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286516 prefixEnd_286516 := by exact prefixLift 286516
  have htrace : WordTrace (prefixWord ++ tailWord_286516) baseStart_286516 baseEnd_286516 := by
    simpa [prefixWord, tailWord_286516, baseEnd_286516] using wordTrace_append hprefix tailTrace_286516
  have hstable : (prefixWord ++ tailWord_286516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286516).length < 2 ^ (prefixWord ++ tailWord_286516).sum := by decide
  have hdescent : baseEnd_286516 < baseStart_286516 := by decide
  rcases family_descends (prefixWord ++ tailWord_286516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286556 : List Nat := [2, 2, 4, 2, 9]
def baseStart_286556 : Nat := 118140960795 + 286556 * 2 ^ 59
def prefixEnd_286556 : Nat := 4983230072969 + 3 ^ 40 * 286556 * 2
def baseEnd_286556 : Nat := 3229431274181313185891

theorem tailTrace_286556 : CollatzResearch.WordTrace tailWord_286556 prefixEnd_286556 3229431274181313185891 := by
  unfold tailWord_286556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225777974932013356803761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6967703966576017809071681 5225777974932013356803761)
  ·
    refine ⟨3919333481199010017602821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5225777974932013356803761 3919333481199010017602821)
    ·
      refine ⟨734875027724814378300529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3919333481199010017602821 734875027724814378300529)
      ·
        refine ⟨551156270793610783725397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 734875027724814378300529 551156270793610783725397)
        ·
          refine ⟨3229431274181313185891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 551156270793610783725397 3229431274181313185891)
          ·
            rfl

theorem cell19_286556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 9].length) (baseStart_286556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286556 prefixEnd_286556 := by exact prefixLift 286556
  have htrace : WordTrace (prefixWord ++ tailWord_286556) baseStart_286556 baseEnd_286556 := by
    simpa [prefixWord, tailWord_286556, baseEnd_286556] using wordTrace_append hprefix tailTrace_286556
  have hstable : (prefixWord ++ tailWord_286556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286556).length < 2 ^ (prefixWord ++ tailWord_286556).sum := by decide
  have hdescent : baseEnd_286556 < baseStart_286556 := by decide
  rcases family_descends (prefixWord ++ tailWord_286556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286672 : List Nat := [2, 1, 1, 1, 1, 2, 11]
def baseStart_286672 : Nat := 118140960795 + 286672 * 2 ^ 59
def prefixEnd_286672 : Nat := 4983230072969 + 3 ^ 40 * 286672 * 2
def baseEnd_286672 : Nat := 29076647147813852480321

theorem tailTrace_286672 : CollatzResearch.WordTrace tailWord_286672 prefixEnd_286672 29076647147813852480321 := by
  unfold tailWord_286672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227893408721889262415135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6970524544962519016553513 5227893408721889262415135)
  ·
    refine ⟨7841840113082833893622703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5227893408721889262415135 7841840113082833893622703)
    ·
      refine ⟨11762760169624250840434055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7841840113082833893622703 11762760169624250840434055)
      ·
        refine ⟨17644140254436376260651083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11762760169624250840434055 17644140254436376260651083)
        ·
          refine ⟨26466210381654564390976625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17644140254436376260651083 26466210381654564390976625)
          ·
            refine ⟨19849657786240923293232469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26466210381654564390976625 19849657786240923293232469)
            ·
              refine ⟨29076647147813852480321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19849657786240923293232469 29076647147813852480321)
              ·
                rfl

theorem cell19_286672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_286672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286672 prefixEnd_286672 := by exact prefixLift 286672
  have htrace : WordTrace (prefixWord ++ tailWord_286672) baseStart_286672 baseEnd_286672 := by
    simpa [prefixWord, tailWord_286672, baseEnd_286672] using wordTrace_append hprefix tailTrace_286672
  have hstable : (prefixWord ++ tailWord_286672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286672).length < 2 ^ (prefixWord ++ tailWord_286672).sum := by decide
  have hdescent : baseEnd_286672 < baseStart_286672 := by decide
  rcases family_descends (prefixWord ++ tailWord_286672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286740 : List Nat := [2, 4, 3, 2, 1, 2, 1, 4]
def baseStart_286740 : Nat := 118140960795 + 286740 * 2 ^ 59
def prefixEnd_286740 : Nat := 4983230072969 + 3 ^ 40 * 286740 * 2
def baseEnd_286740 : Nat := 87250632812037547929667

theorem tailTrace_286740 : CollatzResearch.WordTrace tailWord_286740 prefixEnd_286740 87250632812037547929667 := by
  unfold tailWord_286740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229133490598713069152837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6972177987464950758870449 5229133490598713069152837)
  ·
    refine ⟨980462529487258700466157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5229133490598713069152837 980462529487258700466157)
    ·
      refine ⟨367673448557722012674809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 980462529487258700466157 367673448557722012674809)
      ·
        refine ⟨275755086418291509506107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367673448557722012674809 275755086418291509506107)
        ·
          refine ⟨413632629627437264259161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275755086418291509506107 413632629627437264259161)
          ·
            refine ⟨310224472220577948194371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413632629627437264259161 310224472220577948194371)
            ·
              refine ⟨465336708330866922291557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310224472220577948194371 465336708330866922291557)
              ·
                refine ⟨87250632812037547929667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 465336708330866922291557 87250632812037547929667)
                ·
                  rfl

theorem cell19_286740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_286740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286740 prefixEnd_286740 := by exact prefixLift 286740
  have htrace : WordTrace (prefixWord ++ tailWord_286740) baseStart_286740 baseEnd_286740 := by
    simpa [prefixWord, tailWord_286740, baseEnd_286740] using wordTrace_append hprefix tailTrace_286740
  have hstable : (prefixWord ++ tailWord_286740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286740).length < 2 ^ (prefixWord ++ tailWord_286740).sum := by decide
  have hdescent : baseEnd_286740 < baseStart_286740 := by decide
  rcases family_descends (prefixWord ++ tailWord_286740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286746 : List Nat := [3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_286746 : Nat := 118140960795 + 286746 * 2 ^ 59
def prefixEnd_286746 : Nat := 4983230072969 + 3 ^ 40 * 286746 * 2
def baseEnd_286746 : Nat := 87252458521031311796317

theorem tailTrace_286746 : CollatzResearch.WordTrace tailWord_286746 prefixEnd_286746 87252458521031311796317 := by
  unfold tailWord_286746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614621454793922290756023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6972323879450459442016061 2614621454793922290756023)
  ·
    refine ⟨3921932182190883436134035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2614621454793922290756023 3921932182190883436134035)
    ·
      refine ⟨5882898273286325154201053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3921932182190883436134035 5882898273286325154201053)
      ·
        refine ⟨2206086852482371932825395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5882898273286325154201053 2206086852482371932825395)
        ·
          refine ⟨3309130278723557899238093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206086852482371932825395 3309130278723557899238093)
          ·
            refine ⟨1240923854521334212214285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3309130278723557899238093 1240923854521334212214285)
            ·
              refine ⟨465346445445500329580357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1240923854521334212214285 465346445445500329580357)
              ·
                refine ⟨87252458521031311796317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 465346445445500329580357 87252458521031311796317)
                ·
                  rfl

theorem cell19_286746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_286746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286746 prefixEnd_286746 := by exact prefixLift 286746
  have htrace : WordTrace (prefixWord ++ tailWord_286746) baseStart_286746 baseEnd_286746 := by
    simpa [prefixWord, tailWord_286746, baseEnd_286746] using wordTrace_append hprefix tailTrace_286746
  have hstable : (prefixWord ++ tailWord_286746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286746).length < 2 ^ (prefixWord ++ tailWord_286746).sum := by decide
  have hdescent : baseEnd_286746 < baseStart_286746 := by decide
  rcases family_descends (prefixWord ++ tailWord_286746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286782 : List Nat := [4, 2, 1, 3, 2, 1, 6]
def baseStart_286782 : Nat := 118140960795 + 286782 * 2 ^ 59
def prefixEnd_286782 : Nat := 4983230072969 + 3 ^ 40 * 286782 * 2
def baseEnd_286782 : Nat := 29087804258331298332073

theorem tailTrace_286782 : CollatzResearch.WordTrace tailWord_286782 prefixEnd_286782 29087804258331298332073 := by
  unfold tailWord_286782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307474855880658413916825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6973199231363511540889733 1307474855880658413916825)
  ·
    refine ⟨980606141910493810437619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1307474855880658413916825 980606141910493810437619)
    ·
      refine ⟨1470909212865740715656429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980606141910493810437619 1470909212865740715656429)
      ·
        refine ⟨551590954824652768371161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1470909212865740715656429 551590954824652768371161)
        ·
          refine ⟨413693216118489576278371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551590954824652768371161 413693216118489576278371)
          ·
            refine ⟨620539824177734364417557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413693216118489576278371 620539824177734364417557)
            ·
              refine ⟨29087804258331298332073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 620539824177734364417557 29087804258331298332073)
              ·
                rfl

theorem cell19_286782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_286782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286782 prefixEnd_286782 := by exact prefixLift 286782
  have htrace : WordTrace (prefixWord ++ tailWord_286782) baseStart_286782 baseEnd_286782 := by
    simpa [prefixWord, tailWord_286782, baseEnd_286782] using wordTrace_append hprefix tailTrace_286782
  have hstable : (prefixWord ++ tailWord_286782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286782).length < 2 ^ (prefixWord ++ tailWord_286782).sum := by decide
  have hdescent : baseEnd_286782 < baseStart_286782 := by decide
  rcases family_descends (prefixWord ++ tailWord_286782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286814 : List Nat := [4, 4, 1, 1, 2, 2, 2, 3]
def baseStart_286814 : Nat := 118140960795 + 286814 * 2 ^ 59
def prefixEnd_286814 : Nat := 4983230072969 + 3 ^ 40 * 286814 * 2
def baseEnd_286814 : Nat := 87273149889627302285021

theorem tailTrace_286814 : CollatzResearch.WordTrace tailWord_286814 prefixEnd_286814 87273149889627302285021 := by
  unfold tailWord_286814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307620747866167097062437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6973977321952891184332997 1307620747866167097062437)
  ·
    refine ⟨245178890224906330699207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1307620747866167097062437 245178890224906330699207)
    ·
      refine ⟨367768335337359496048811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245178890224906330699207 367768335337359496048811)
      ·
        refine ⟨551652503006039244073217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367768335337359496048811 551652503006039244073217)
        ·
          refine ⟨413739377254529433054913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551652503006039244073217 413739377254529433054913)
          ·
            refine ⟨310304532940897074791185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413739377254529433054913 310304532940897074791185)
            ·
              refine ⟨232728399705672806093389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310304532940897074791185 232728399705672806093389)
              ·
                refine ⟨87273149889627302285021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232728399705672806093389 87273149889627302285021)
                ·
                  rfl

theorem cell19_286814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_286814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286814 prefixEnd_286814 := by exact prefixLift 286814
  have htrace : WordTrace (prefixWord ++ tailWord_286814) baseStart_286814 baseEnd_286814 := by
    simpa [prefixWord, tailWord_286814, baseEnd_286814] using wordTrace_append hprefix tailTrace_286814
  have hstable : (prefixWord ++ tailWord_286814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286814).length < 2 ^ (prefixWord ++ tailWord_286814).sum := by decide
  have hdescent : baseEnd_286814 < baseStart_286814 := by decide
  rcases family_descends (prefixWord ++ tailWord_286814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286841 : List Nat := [1, 2, 1, 3, 4, 3, 5]
def baseStart_286841 : Nat := 118140960795 + 286841 * 2 ^ 59
def prefixEnd_286841 : Nat := 4983230072969 + 3 ^ 40 * 286841 * 2
def baseEnd_286841 : Nat := 29093788526699746561649

theorem tailTrace_286841 : CollatzResearch.WordTrace tailWord_286841 prefixEnd_286841 29093788526699746561649 := by
  unfold tailWord_286841
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461950753831520387732377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6974633835887680258488251 10461950753831520387732377)
  ·
    refine ⟨7846463065373640290799283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10461950753831520387732377 7846463065373640290799283)
    ·
      refine ⟨11769694598060460436198925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7846463065373640290799283 11769694598060460436198925)
      ·
        refine ⟨4413635474272672663574597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11769694598060460436198925 4413635474272672663574597)
        ·
          refine ⟨827556651426126124420237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4413635474272672663574597 827556651426126124420237)
          ·
            refine ⟨310333744284797296657589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 827556651426126124420237 310333744284797296657589)
            ·
              refine ⟨29093788526699746561649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 310333744284797296657589 29093788526699746561649)
              ·
                rfl

theorem cell19_286841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_286841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286841 prefixEnd_286841 := by exact prefixLift 286841
  have htrace : WordTrace (prefixWord ++ tailWord_286841) baseStart_286841 baseEnd_286841 := by
    simpa [prefixWord, tailWord_286841, baseEnd_286841] using wordTrace_append hprefix tailTrace_286841
  have hstable : (prefixWord ++ tailWord_286841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286841).length < 2 ^ (prefixWord ++ tailWord_286841).sum := by decide
  have hdescent : baseEnd_286841 < baseStart_286841 := by decide
  rcases family_descends (prefixWord ++ tailWord_286841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286879 : List Nat := [1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_286879 : Nat := 118140960795 + 286879 * 2 ^ 59
def prefixEnd_286879 : Nat := 4983230072969 + 3 ^ 40 * 286879 * 2
def baseEnd_286879 : Nat := 87292928403726410840399

theorem tailTrace_286879 : CollatzResearch.WordTrace tailWord_286879 prefixEnd_286879 87292928403726410840399 := by
  unfold tailWord_286879
  simp only [CollatzResearch.WordTrace]
  refine ⟨10463336727693852877615691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6975557818462568585077127 10463336727693852877615691)
  ·
    refine ⟨15695005091540779316423537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10463336727693852877615691 15695005091540779316423537)
    ·
      refine ⟨11771253818655584487317653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15695005091540779316423537 11771253818655584487317653)
      ·
        refine ⟨551777522749480522843015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11771253818655584487317653 551777522749480522843015)
        ·
          refine ⟨827666284124220784264523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551777522749480522843015 827666284124220784264523)
          ·
            refine ⟨1241499426186331176396785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827666284124220784264523 1241499426186331176396785)
            ·
              refine ⟨931124569639748382297589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241499426186331176396785 931124569639748382297589)
              ·
                refine ⟨87292928403726410840399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 931124569639748382297589 87292928403726410840399)
                ·
                  rfl

theorem cell19_286879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_286879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286879 prefixEnd_286879 := by exact prefixLift 286879
  have htrace : WordTrace (prefixWord ++ tailWord_286879) baseStart_286879 baseEnd_286879 := by
    simpa [prefixWord, tailWord_286879, baseEnd_286879] using wordTrace_append hprefix tailTrace_286879
  have hstable : (prefixWord ++ tailWord_286879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286879).length < 2 ^ (prefixWord ++ tailWord_286879).sum := by decide
  have hdescent : baseEnd_286879 < baseStart_286879 := by decide
  rcases family_descends (prefixWord ++ tailWord_286879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286894 : List Nat := [4, 1, 4, 2, 2, 6]
def baseStart_286894 : Nat := 118140960795 + 286894 * 2 ^ 59
def prefixEnd_286894 : Nat := 4983230072969 + 3 ^ 40 * 286894 * 2
def baseEnd_286894 : Nat := 9699721408467868945225

theorem tailTrace_286894 : CollatzResearch.WordTrace tailWord_286894 prefixEnd_286894 9699721408467868945225 := by
  unfold tailWord_286894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307985477829938804926467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6975922548426340292941157 1307985477829938804926467)
  ·
    refine ⟨1961978216744908207389701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1307985477829938804926467 1961978216744908207389701)
    ·
      refine ⟨367870915639670288885569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1961978216744908207389701 367870915639670288885569)
      ·
        refine ⟨275903186729752716664177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367870915639670288885569 275903186729752716664177)
        ·
          refine ⟨206927390047314537498133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275903186729752716664177 206927390047314537498133)
          ·
            refine ⟨9699721408467868945225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206927390047314537498133 9699721408467868945225)
            ·
              rfl

theorem cell19_286894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 6].length) (baseStart_286894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286894 prefixEnd_286894 := by exact prefixLift 286894
  have htrace : WordTrace (prefixWord ++ tailWord_286894) baseStart_286894 baseEnd_286894 := by
    simpa [prefixWord, tailWord_286894, baseEnd_286894] using wordTrace_append hprefix tailTrace_286894
  have hstable : (prefixWord ++ tailWord_286894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286894).length < 2 ^ (prefixWord ++ tailWord_286894).sum := by decide
  have hdescent : baseEnd_286894 < baseStart_286894 := by decide
  rcases family_descends (prefixWord ++ tailWord_286894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286913 : List Nat := [1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_286913 : Nat := 118140960795 + 286913 * 2 ^ 59
def prefixEnd_286913 : Nat := 4983230072969 + 3 ^ 40 * 286913 * 2
def baseEnd_286913 : Nat := 87303274088024406084751

theorem tailTrace_286913 : CollatzResearch.WordTrace tailWord_286913 prefixEnd_286913 87303274088024406084751 := by
  unfold tailWord_286913
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464576809570676684353393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6976384539713784456235595 10464576809570676684353393)
  ·
    refine ⟨7848432607178007513265045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10464576809570676684353393 7848432607178007513265045)
    ·
      refine ⟨367895278461469102184299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7848432607178007513265045 367895278461469102184299)
      ·
        refine ⟨551842917692203653276449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367895278461469102184299 551842917692203653276449)
        ·
          refine ⟨413882188269152739957337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551842917692203653276449 413882188269152739957337)
          ·
            refine ⟨310411641201864554968003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413882188269152739957337 310411641201864554968003)
            ·
              refine ⟨465617461802796832452005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310411641201864554968003 465617461802796832452005)
              ·
                refine ⟨87303274088024406084751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 465617461802796832452005 87303274088024406084751)
                ·
                  rfl

theorem cell19_286913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_286913 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286913 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286913 prefixEnd_286913 := by exact prefixLift 286913
  have htrace : WordTrace (prefixWord ++ tailWord_286913) baseStart_286913 baseEnd_286913 := by
    simpa [prefixWord, tailWord_286913, baseEnd_286913] using wordTrace_append hprefix tailTrace_286913
  have hstable : (prefixWord ++ tailWord_286913).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286913).length < 2 ^ (prefixWord ++ tailWord_286913).sum := by decide
  have hdescent : baseEnd_286913 < baseStart_286913 := by decide
  rcases family_descends (prefixWord ++ tailWord_286913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286938 : List Nat := [3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_286938 : Nat := 118140960795 + 286938 * 2 ^ 59
def prefixEnd_286938 : Nat := 4983230072969 + 3 ^ 40 * 286938 * 2
def baseEnd_286938 : Nat := 87310881208831755529127

theorem tailTrace_286938 : CollatzResearch.WordTrace tailWord_286938 prefixEnd_286938 87310881208831755529127 := by
  unfold tailWord_286938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616372158620026488503367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6976992422986737302675645 2616372158620026488503367)
  ·
    refine ⟨3924558237930039732755051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2616372158620026488503367 3924558237930039732755051)
    ·
      refine ⟨5886837356895059599132577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3924558237930039732755051 5886837356895059599132577)
      ·
        refine ⟨4415128017671294699349433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5886837356895059599132577 4415128017671294699349433)
        ·
          refine ⟨3311346013253471024512075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4415128017671294699349433 3311346013253471024512075)
          ·
            refine ⟨4967019019880206536768113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311346013253471024512075 4967019019880206536768113)
            ·
              refine ⟨3725264264910154902576085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4967019019880206536768113 3725264264910154902576085)
              ·
                refine ⟨87310881208831755529127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3725264264910154902576085 87310881208831755529127)
                ·
                  rfl

theorem cell19_286938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_286938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286938 prefixEnd_286938 := by exact prefixLift 286938
  have htrace : WordTrace (prefixWord ++ tailWord_286938) baseStart_286938 baseEnd_286938 := by
    simpa [prefixWord, tailWord_286938, baseEnd_286938] using wordTrace_append hprefix tailTrace_286938
  have hstable : (prefixWord ++ tailWord_286938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286938).length < 2 ^ (prefixWord ++ tailWord_286938).sum := by decide
  have hdescent : baseEnd_286938 < baseStart_286938 := by decide
  rcases family_descends (prefixWord ++ tailWord_286938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286974 : List Nat := [4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_286974 : Nat := 118140960795 + 286974 * 2 ^ 59
def prefixEnd_286974 : Nat := 4983230072969 + 3 ^ 40 * 286974 * 2
def baseEnd_286974 : Nat := 87321835462794338729029

theorem tailTrace_286974 : CollatzResearch.WordTrace tailWord_286974 prefixEnd_286974 87321835462794338729029 := by
  unfold tailWord_286974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308350207793710512790497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6977867774899789401549317 1308350207793710512790497)
  ·
    refine ⟨981262655845282884592873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1308350207793710512790497 981262655845282884592873)
    ·
      refine ⟨735946991883962163444655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 981262655845282884592873 735946991883962163444655)
      ·
        refine ⟨1103920487825943245166983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735946991883962163444655 1103920487825943245166983)
        ·
          refine ⟨1655880731738914867750475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103920487825943245166983 1655880731738914867750475)
          ·
            refine ⟨2483821097608372301625713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655880731738914867750475 2483821097608372301625713)
            ·
              refine ⟨1862865823206279226219285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2483821097608372301625713 1862865823206279226219285)
              ·
                refine ⟨87321835462794338729029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1862865823206279226219285 87321835462794338729029)
                ·
                  rfl

theorem cell19_286974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_286974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286974 prefixEnd_286974 := by exact prefixLift 286974
  have htrace : WordTrace (prefixWord ++ tailWord_286974) baseStart_286974 baseEnd_286974 := by
    simpa [prefixWord, tailWord_286974, baseEnd_286974] using wordTrace_append hprefix tailTrace_286974
  have hstable : (prefixWord ++ tailWord_286974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286974).length < 2 ^ (prefixWord ++ tailWord_286974).sum := by decide
  have hdescent : baseEnd_286974 < baseStart_286974 := by decide
  rcases family_descends (prefixWord ++ tailWord_286974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286993 : List Nat := [1, 2, 2, 1, 1, 5, 4, 3]
def baseStart_286993 : Nat := 118140960795 + 286993 * 2 ^ 59
def prefixEnd_286993 : Nat := 4983230072969 + 3 ^ 40 * 286993 * 2
def baseEnd_286993 : Nat := 87327616874607924306755

theorem tailTrace_286993 : CollatzResearch.WordTrace tailWord_286993 prefixEnd_286993 87327616874607924306755 := by
  unfold tailWord_286993
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467494649280850347265633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6978329766187233564843755 10467494649280850347265633)
  ·
    refine ⟨7850620986960637760449225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10467494649280850347265633 7850620986960637760449225)
    ·
      refine ⟨5887965740220478320336919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7850620986960637760449225 5887965740220478320336919)
      ·
        refine ⟨8831948610330717480505379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5887965740220478320336919 8831948610330717480505379)
        ·
          refine ⟨13247922915496076220758069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8831948610330717480505379 13247922915496076220758069)
          ·
            refine ⟨1241992773327757145696069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13247922915496076220758069 1241992773327757145696069)
            ·
              refine ⟨232873644998954464818013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1241992773327757145696069 232873644998954464818013)
              ·
                refine ⟨87327616874607924306755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232873644998954464818013 87327616874607924306755)
                ·
                  rfl

theorem cell19_286993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_286993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_286993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_286993 prefixEnd_286993 := by exact prefixLift 286993
  have htrace : WordTrace (prefixWord ++ tailWord_286993) baseStart_286993 baseEnd_286993 := by
    simpa [prefixWord, tailWord_286993, baseEnd_286993] using wordTrace_append hprefix tailTrace_286993
  have hstable : (prefixWord ++ tailWord_286993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286993).length < 2 ^ (prefixWord ++ tailWord_286993).sum := by decide
  have hdescent : baseEnd_286993 < baseStart_286993 := by decide
  rcases family_descends (prefixWord ++ tailWord_286993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287012 : List Nat := [2, 3, 1, 3, 1, 4, 5]
def baseStart_287012 : Nat := 118140960795 + 287012 * 2 ^ 59
def prefixEnd_287012 : Nat := 4983230072969 + 3 ^ 40 * 287012 * 2
def baseEnd_287012 : Nat := 29111132762140503294827

theorem tailTrace_287012 : CollatzResearch.WordTrace tailWord_287012 prefixEnd_287012 29111132762140503294827 := by
  unfold tailWord_287012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234093818106008296103645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6978791757474677728138193 5234093818106008296103645)
  ·
    refine ⟨1962785181789753111038867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5234093818106008296103645 1962785181789753111038867)
    ·
      refine ⟨2944177772684629666558301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1962785181789753111038867 2944177772684629666558301)
      ·
        refine ⟨1104066664756736124959363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2944177772684629666558301 1104066664756736124959363)
        ·
          refine ⟨1656099997135104187439045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104066664756736124959363 1656099997135104187439045)
          ·
            refine ⟨310518749462832035144821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1656099997135104187439045 310518749462832035144821)
            ·
              refine ⟨29111132762140503294827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 310518749462832035144821 29111132762140503294827)
              ·
                rfl

theorem cell19_287012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_287012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287012 prefixEnd_287012 := by exact prefixLift 287012
  have htrace : WordTrace (prefixWord ++ tailWord_287012) baseStart_287012 baseEnd_287012 := by
    simpa [prefixWord, tailWord_287012, baseEnd_287012] using wordTrace_append hprefix tailTrace_287012
  have hstable : (prefixWord ++ tailWord_287012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287012).length < 2 ^ (prefixWord ++ tailWord_287012).sum := by decide
  have hdescent : baseEnd_287012 < baseStart_287012 := by decide
  rcases family_descends (prefixWord ++ tailWord_287012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287052 : List Nat := [2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_287052 : Nat := 118140960795 + 287052 * 2 ^ 59
def prefixEnd_287052 : Nat := 4983230072969 + 3 ^ 40 * 287052 * 2
def baseEnd_287052 : Nat := 87345569679713268995483

theorem tailTrace_287052 : CollatzResearch.WordTrace tailWord_287052 prefixEnd_287052 87345569679713268995483 := by
  unfold tailWord_287052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234823278033551711831705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6979764370711402282442273 5234823278033551711831705)
  ·
    refine ⟨3926117458525163783873779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5234823278033551711831705 3926117458525163783873779)
    ·
      refine ⟨5889176187787745675810669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3926117458525163783873779 5889176187787745675810669)
      ·
        refine ⟨2208441070420404628429001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5889176187787745675810669 2208441070420404628429001)
        ·
          refine ⟨1656330802815303471321751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2208441070420404628429001 1656330802815303471321751)
          ·
            refine ⟨2484496204222955206982627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656330802815303471321751 2484496204222955206982627)
            ·
              refine ⟨3726744306334432810473941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484496204222955206982627 3726744306334432810473941)
              ·
                refine ⟨87345569679713268995483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3726744306334432810473941 87345569679713268995483)
                ·
                  rfl

theorem cell19_287052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_287052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287052 prefixEnd_287052 := by exact prefixLift 287052
  have htrace : WordTrace (prefixWord ++ tailWord_287052) baseStart_287052 baseEnd_287052 := by
    simpa [prefixWord, tailWord_287052, baseEnd_287052] using wordTrace_append hprefix tailTrace_287052
  have hstable : (prefixWord ++ tailWord_287052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287052).length < 2 ^ (prefixWord ++ tailWord_287052).sum := by decide
  have hdescent : baseEnd_287052 < baseStart_287052 := by decide
  rcases family_descends (prefixWord ++ tailWord_287052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287069 : List Nat := [1, 4, 5, 9]
def baseStart_287069 : Nat := 118140960795 + 287069 * 2 ^ 59
def prefixEnd_287069 : Nat := 4983230072969 + 3 ^ 40 * 287069 * 2
def baseEnd_287069 : Nat := 1078404228664966254539

theorem tailTrace_287069 : CollatzResearch.WordTrace tailWord_287069 prefixEnd_287069 1078404228664966254539 := by
  unfold tailWord_287069
  simp only [CollatzResearch.WordTrace]
  refine ⟨10470266597005515327032261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6980177731337010218021507 10470266597005515327032261)
  ·
    refine ⟨1963174986938534123818549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10470266597005515327032261 1963174986938534123818549)
    ·
      refine ⟨184047655025487574107989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1963174986938534123818549 184047655025487574107989)
      ·
        refine ⟨1078404228664966254539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 184047655025487574107989 1078404228664966254539)
        ·
          rfl

theorem cell19_287069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 9].length) (baseStart_287069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287069 prefixEnd_287069 := by exact prefixLift 287069
  have htrace : WordTrace (prefixWord ++ tailWord_287069) baseStart_287069 baseEnd_287069 := by
    simpa [prefixWord, tailWord_287069, baseEnd_287069] using wordTrace_append hprefix tailTrace_287069
  have hstable : (prefixWord ++ tailWord_287069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287069).length < 2 ^ (prefixWord ++ tailWord_287069).sum := by decide
  have hdescent : baseEnd_287069 < baseStart_287069 := by decide
  rcases family_descends (prefixWord ++ tailWord_287069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287088 : List Nat := [2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_287088 : Nat := 118140960795 + 287088 * 2 ^ 59
def prefixEnd_287088 : Nat := 4983230072969 + 3 ^ 40 * 287088 * 2
def baseEnd_287088 : Nat := 87356523933675852195385

theorem tailTrace_287088 : CollatzResearch.WordTrace tailWord_287088 prefixEnd_287088 87356523933675852195385 := by
  unfold tailWord_287088
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235479791968340785986959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6980639722624454381315945 5235479791968340785986959)
  ·
    refine ⟨7853219687952511178980439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5235479791968340785986959 7853219687952511178980439)
    ·
      refine ⟨11779829531928766768470659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7853219687952511178980439 11779829531928766768470659)
      ·
        refine ⟨17669744297893150152705989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11779829531928766768470659 17669744297893150152705989)
        ·
          refine ⟨3313077055854965653632373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17669744297893150152705989 3313077055854965653632373)
          ·
            refine ⟨310600973986403030028035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3313077055854965653632373 310600973986403030028035)
            ·
              refine ⟨465901460979604545042053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310600973986403030028035 465901460979604545042053)
              ·
                refine ⟨87356523933675852195385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 465901460979604545042053 87356523933675852195385)
                ·
                  rfl

theorem cell19_287088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_287088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287088 prefixEnd_287088 := by exact prefixLift 287088
  have htrace : WordTrace (prefixWord ++ tailWord_287088) baseStart_287088 baseEnd_287088 := by
    simpa [prefixWord, tailWord_287088, baseEnd_287088] using wordTrace_append hprefix tailTrace_287088
  have hstable : (prefixWord ++ tailWord_287088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287088).length < 2 ^ (prefixWord ++ tailWord_287088).sum := by decide
  have hdescent : baseEnd_287088 < baseStart_287088 := by decide
  rcases family_descends (prefixWord ++ tailWord_287088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287105 : List Nat := [1, 2, 4, 3, 1, 2, 3, 3]
def baseStart_287105 : Nat := 118140960795 + 287105 * 2 ^ 59
def prefixEnd_287105 : Nat := 4983230072969 + 3 ^ 40 * 287105 * 2
def baseEnd_287105 : Nat := 87361696775824849817561

theorem tailTrace_287105 : CollatzResearch.WordTrace tailWord_287105 prefixEnd_287105 87361696775824849817561 := by
  unfold tailWord_287105
  simp only [CollatzResearch.WordTrace]
  refine ⟨10471579624875093475342769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6981053083250062316895179 10471579624875093475342769)
  ·
    refine ⟨7853684718656320106507077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10471579624875093475342769 7853684718656320106507077)
    ·
      refine ⟨1472565884748060019970077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7853684718656320106507077 1472565884748060019970077)
      ·
        refine ⟨552212206780522507488779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1472565884748060019970077 552212206780522507488779)
        ·
          refine ⟨828318310170783761233169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552212206780522507488779 828318310170783761233169)
          ·
            refine ⟨621238732628087820924877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828318310170783761233169 621238732628087820924877)
            ·
              refine ⟨232964524735532932846829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 621238732628087820924877 232964524735532932846829)
              ·
                refine ⟨87361696775824849817561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232964524735532932846829 87361696775824849817561)
                ·
                  rfl

theorem cell19_287105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_287105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287105 prefixEnd_287105 := by exact prefixLift 287105
  have htrace : WordTrace (prefixWord ++ tailWord_287105) baseStart_287105 baseEnd_287105 := by
    simpa [prefixWord, tailWord_287105, baseEnd_287105] using wordTrace_append hprefix tailTrace_287105
  have hstable : (prefixWord ++ tailWord_287105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287105).length < 2 ^ (prefixWord ++ tailWord_287105).sum := by decide
  have hdescent : baseEnd_287105 < baseStart_287105 := by decide
  rcases family_descends (prefixWord ++ tailWord_287105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287156 : List Nat := [2, 5, 2, 2, 2, 1, 2, 3]
def baseStart_287156 : Nat := 118140960795 + 287156 * 2 ^ 59
def prefixEnd_287156 : Nat := 4983230072969 + 3 ^ 40 * 287156 * 2
def baseEnd_287156 : Nat := 87377215302271842684089

theorem tailTrace_287156 : CollatzResearch.WordTrace tailWord_287156 prefixEnd_287156 87377215302271842684089 := by
  unfold tailWord_287156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236719873845164592724661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6982293165126886123632881 5236719873845164592724661)
  ·
    refine ⟨490942488172984180567937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5236719873845164592724661 490942488172984180567937)
    ·
      refine ⟨368206866129738135425953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 490942488172984180567937 368206866129738135425953)
      ·
        refine ⟨276155149597303601569465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368206866129738135425953 276155149597303601569465)
        ·
          refine ⟨207116362197977701177099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276155149597303601569465 207116362197977701177099)
          ·
            refine ⟨310674543296966551765649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207116362197977701177099 310674543296966551765649)
            ·
              refine ⟨233005907472724913824237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310674543296966551765649 233005907472724913824237)
              ·
                refine ⟨87377215302271842684089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233005907472724913824237 87377215302271842684089)
                ·
                  rfl

theorem cell19_287156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_287156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287156 prefixEnd_287156 := by exact prefixLift 287156
  have htrace : WordTrace (prefixWord ++ tailWord_287156) baseStart_287156 baseEnd_287156 := by
    simpa [prefixWord, tailWord_287156, baseEnd_287156] using wordTrace_append hprefix tailTrace_287156
  have hstable : (prefixWord ++ tailWord_287156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287156).length < 2 ^ (prefixWord ++ tailWord_287156).sum := by decide
  have hdescent : baseEnd_287156 < baseStart_287156 := by decide
  rcases family_descends (prefixWord ++ tailWord_287156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287164 : List Nat := [2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_287164 : Nat := 118140960795 + 287164 * 2 ^ 59
def prefixEnd_287164 : Nat := 4983230072969 + 3 ^ 40 * 287164 * 2
def baseEnd_287164 : Nat := 87379649580930194506289

theorem tailTrace_287164 : CollatzResearch.WordTrace tailWord_287164 prefixEnd_287164 87379649580930194506289 := by
  unfold tailWord_287164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236865765830673275870273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6982487687774231034493697 5236865765830673275870273)
  ·
    refine ⟨3927649324373004956902705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5236865765830673275870273 3927649324373004956902705)
    ·
      refine ⟨2945736993279753717677029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3927649324373004956902705 2945736993279753717677029)
      ·
        refine ⟨552325686239953822064443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2945736993279753717677029 552325686239953822064443)
        ·
          refine ⟨828488529359930733096665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552325686239953822064443 828488529359930733096665)
          ·
            refine ⟨621366397019948049822499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828488529359930733096665 621366397019948049822499)
            ·
              refine ⟨932049595529922074733749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621366397019948049822499 932049595529922074733749)
              ·
                refine ⟨87379649580930194506289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 932049595529922074733749 87379649580930194506289)
                ·
                  rfl

theorem cell19_287164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_287164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287164 prefixEnd_287164 := by exact prefixLift 287164
  have htrace : WordTrace (prefixWord ++ tailWord_287164) baseStart_287164 baseEnd_287164 := by
    simpa [prefixWord, tailWord_287164, baseEnd_287164] using wordTrace_append hprefix tailTrace_287164
  have hstable : (prefixWord ++ tailWord_287164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287164).length < 2 ^ (prefixWord ++ tailWord_287164).sum := by decide
  have hdescent : baseEnd_287164 < baseStart_287164 := by decide
  rcases family_descends (prefixWord ++ tailWord_287164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287255 : List Nat := [1, 1, 3, 6, 2, 1, 1, 4]
def baseStart_287255 : Nat := 118140960795 + 287255 * 2 ^ 59
def prefixEnd_287255 : Nat := 4983230072969 + 3 ^ 40 * 287255 * 2
def baseEnd_287255 : Nat := 87407339500668946483819

theorem tailTrace_287255 : CollatzResearch.WordTrace tailWord_287255 prefixEnd_287255 87407339500668946483819 := by
  unfold tailWord_287255
  simp only [CollatzResearch.WordTrace]
  refine ⟨10477050574331669093303219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6984700382887779395535479 10477050574331669093303219)
  ·
    refine ⟨15715575861497503639954829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10477050574331669093303219 15715575861497503639954829)
    ·
      refine ⟨5893340948061563864983061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15715575861497503639954829 5893340948061563864983061)
      ·
        refine ⟨276250356940385806171081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5893340948061563864983061 276250356940385806171081)
        ·
          refine ⟨207187767705289354628311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276250356940385806171081 207187767705289354628311)
          ·
            refine ⟨310781651557934031942467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207187767705289354628311 310781651557934031942467)
            ·
              refine ⟨466172477336901047913701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310781651557934031942467 466172477336901047913701)
              ·
                refine ⟨87407339500668946483819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466172477336901047913701 87407339500668946483819)
                ·
                  rfl

theorem cell19_287255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_287255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287255 prefixEnd_287255 := by exact prefixLift 287255
  have htrace : WordTrace (prefixWord ++ tailWord_287255) baseStart_287255 baseEnd_287255 := by
    simpa [prefixWord, tailWord_287255, baseEnd_287255] using wordTrace_append hprefix tailTrace_287255
  have hstable : (prefixWord ++ tailWord_287255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287255).length < 2 ^ (prefixWord ++ tailWord_287255).sum := by decide
  have hdescent : baseEnd_287255 < baseStart_287255 := by decide
  rcases family_descends (prefixWord ++ tailWord_287255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287333 : List Nat := [1, 3, 1, 3, 4, 2, 2, 3]
def baseStart_287333 : Nat := 118140960795 + 287333 * 2 ^ 59
def prefixEnd_287333 : Nat := 4983230072969 + 3 ^ 40 * 287333 * 2
def baseEnd_287333 : Nat := 87431073717587876750273

theorem tailTrace_287333 : CollatzResearch.WordTrace tailWord_287333 prefixEnd_287333 87431073717587876750273 := by
  unfold tailWord_287333
  simp only [CollatzResearch.WordTrace]
  refine ⟨10479895468049088414642653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6986596978699392276428435 10479895468049088414642653)
  ·
    refine ⟨3929960800518408155490995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10479895468049088414642653 3929960800518408155490995)
    ·
      refine ⟨5894941200777612233236493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3929960800518408155490995 5894941200777612233236493)
      ·
        refine ⟨2210602950291604587463685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5894941200777612233236493 2210602950291604587463685)
        ·
          refine ⟨414488053179675860149441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2210602950291604587463685 414488053179675860149441)
          ·
            refine ⟨310866039884756895112081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414488053179675860149441 310866039884756895112081)
            ·
              refine ⟨233149529913567671334061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310866039884756895112081 233149529913567671334061)
              ·
                refine ⟨87431073717587876750273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233149529913567671334061 87431073717587876750273)
                ·
                  rfl

theorem cell19_287333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_287333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287333 prefixEnd_287333 := by exact prefixLift 287333
  have htrace : WordTrace (prefixWord ++ tailWord_287333) baseStart_287333 baseEnd_287333 := by
    simpa [prefixWord, tailWord_287333, baseEnd_287333] using wordTrace_append hprefix tailTrace_287333
  have hstable : (prefixWord ++ tailWord_287333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287333).length < 2 ^ (prefixWord ++ tailWord_287333).sum := by decide
  have hdescent : baseEnd_287333 < baseStart_287333 := by decide
  rcases family_descends (prefixWord ++ tailWord_287333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287413 : List Nat := [1, 3, 3, 3, 1, 8]
def baseStart_287413 : Nat := 118140960795 + 287413 * 2 ^ 59
def prefixEnd_287413 : Nat := 4983230072969 + 3 ^ 40 * 287413 * 2
def baseEnd_287413 : Nat := 9717268500463488330253

theorem tailTrace_287413 : CollatzResearch.WordTrace tailWord_287413 prefixEnd_287413 9717268500463488330253 := by
  unfold tailWord_287413
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482813307759262077554893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6988542205172841385036595 10482813307759262077554893)
  ·
    refine ⟨3931054990409723279083085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10482813307759262077554893 3931054990409723279083085)
    ·
      refine ⟨1474145621403646229656157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3931054990409723279083085 1474145621403646229656157)
      ·
        refine ⟨552804608026367336121059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1474145621403646229656157 552804608026367336121059)
        ·
          refine ⟨829206912039551004181589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552804608026367336121059 829206912039551004181589)
          ·
            refine ⟨9717268500463488330253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 829206912039551004181589 9717268500463488330253)
            ·
              rfl

theorem cell19_287413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_287413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287413 prefixEnd_287413 := by exact prefixLift 287413
  have htrace : WordTrace (prefixWord ++ tailWord_287413) baseStart_287413 baseEnd_287413 := by
    simpa [prefixWord, tailWord_287413, baseEnd_287413] using wordTrace_append hprefix tailTrace_287413
  have hstable : (prefixWord ++ tailWord_287413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287413).length < 2 ^ (prefixWord ++ tailWord_287413).sum := by decide
  have hdescent : baseEnd_287413 < baseStart_287413 := by decide
  rcases family_descends (prefixWord ++ tailWord_287413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287415 : List Nat := [1, 1, 3, 1, 13]
def baseStart_287415 : Nat := 118140960795 + 287415 * 2 ^ 59
def prefixEnd_287415 : Nat := 4983230072969 + 3 ^ 40 * 287415 * 2
def baseEnd_287415 : Nat := 3239112039771703071401

theorem tailTrace_287415 : CollatzResearch.WordTrace tailWord_287415 prefixEnd_287415 3239112039771703071401 := by
  unfold tailWord_287415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482886253752016419127699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6988590835834677612751799 10482886253752016419127699)
  ·
    refine ⟨15724329380628024628691549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10482886253752016419127699 15724329380628024628691549)
    ·
      refine ⟨5896623517735509235759331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15724329380628024628691549 5896623517735509235759331)
      ·
        refine ⟨8844935276603263853638997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5896623517735509235759331 8844935276603263853638997)
        ·
          refine ⟨3239112039771703071401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8844935276603263853638997 3239112039771703071401)
          ·
            rfl

theorem cell19_287415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 13].length) (baseStart_287415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287415 prefixEnd_287415 := by exact prefixLift 287415
  have htrace : WordTrace (prefixWord ++ tailWord_287415) baseStart_287415 baseEnd_287415 := by
    simpa [prefixWord, tailWord_287415, baseEnd_287415] using wordTrace_append hprefix tailTrace_287415
  have hstable : (prefixWord ++ tailWord_287415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287415).length < 2 ^ (prefixWord ++ tailWord_287415).sum := by decide
  have hdescent : baseEnd_287415 < baseStart_287415 := by decide
  rcases family_descends (prefixWord ++ tailWord_287415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287432 : List Nat := [2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_287432 : Nat := 118140960795 + 287432 * 2 ^ 59
def prefixEnd_287432 : Nat := 4983230072969 + 3 ^ 40 * 287432 * 2
def baseEnd_287432 : Nat := 87461197915984980550003

theorem tailTrace_287432 : CollatzResearch.WordTrace tailWord_287432 prefixEnd_287432 87461197915984980550003 := by
  unfold tailWord_287432
  simp only [CollatzResearch.WordTrace]
  refine ⟨5241753147345214161248275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6989004196460285548331033 5241753147345214161248275)
  ·
    refine ⟨7862629721017821241872413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5241753147345214161248275 7862629721017821241872413)
    ·
      refine ⟨2948486145381682965702155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7862629721017821241872413 2948486145381682965702155)
      ·
        refine ⟨4422729218072524448553233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948486145381682965702155 4422729218072524448553233)
        ·
          refine ⟨3317046913554393336414925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4422729218072524448553233 3317046913554393336414925)
          ·
            refine ⟨1243892592582897501155597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3317046913554393336414925 1243892592582897501155597)
            ·
              refine ⟨466459722218586562933349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243892592582897501155597 466459722218586562933349)
              ·
                refine ⟨87461197915984980550003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466459722218586562933349 87461197915984980550003)
                ·
                  rfl

theorem cell19_287432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_287432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287432 prefixEnd_287432 := by exact prefixLift 287432
  have htrace : WordTrace (prefixWord ++ tailWord_287432) baseStart_287432 baseEnd_287432 := by
    simpa [prefixWord, tailWord_287432, baseEnd_287432] using wordTrace_append hprefix tailTrace_287432
  have hstable : (prefixWord ++ tailWord_287432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287432).length < 2 ^ (prefixWord ++ tailWord_287432).sum := by decide
  have hdescent : baseEnd_287432 < baseStart_287432 := by decide
  rcases family_descends (prefixWord ++ tailWord_287432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287470 : List Nat := [4, 1, 2, 1, 1, 4, 6]
def baseStart_287470 : Nat := 118140960795 + 287470 * 2 ^ 59
def prefixEnd_287470 : Nat := 4983230072969 + 3 ^ 40 * 287470 * 2
def baseEnd_287470 : Nat := 29157586913204050568485

theorem tailTrace_287470 : CollatzResearch.WordTrace tailWord_287470 prefixEnd_287470 29157586913204050568485 := by
  unfold tailWord_287470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310611533569095101547483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6989928179035173874919909 1310611533569095101547483)
  ·
    refine ⟨1965917300353642652321225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1310611533569095101547483 1965917300353642652321225)
    ·
      refine ⟨1474437975265231989240919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1965917300353642652321225 1474437975265231989240919)
      ·
        refine ⟨2211656962897847983861379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474437975265231989240919 2211656962897847983861379)
        ·
          refine ⟨3317485444346771975792069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211656962897847983861379 3317485444346771975792069)
          ·
            refine ⟨622028520815019745461013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3317485444346771975792069 622028520815019745461013)
            ·
              refine ⟨29157586913204050568485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 622028520815019745461013 29157586913204050568485)
              ·
                rfl

theorem cell19_287470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_287470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287470 prefixEnd_287470 := by exact prefixLift 287470
  have htrace : WordTrace (prefixWord ++ tailWord_287470) baseStart_287470 baseEnd_287470 := by
    simpa [prefixWord, tailWord_287470, baseEnd_287470] using wordTrace_append hprefix tailTrace_287470
  have hstable : (prefixWord ++ tailWord_287470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287470).length < 2 ^ (prefixWord ++ tailWord_287470).sum := by decide
  have hdescent : baseEnd_287470 < baseStart_287470 := by decide
  rcases family_descends (prefixWord ++ tailWord_287470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287472 : List Nat := [2, 1, 1, 1, 3, 1, 10]
def baseStart_287472 : Nat := 118140960795 + 287472 * 2 ^ 59
def prefixEnd_287472 : Nat := 4983230072969 + 3 ^ 40 * 287472 * 2
def baseEnd_287472 : Nat := 29157789769758913220335

theorem tailTrace_287472 : CollatzResearch.WordTrace tailWord_287472 prefixEnd_287472 29157789769758913220335 := by
  unfold tailWord_287472
  simp only [CollatzResearch.WordTrace]
  refine ⟨5242482607272757576976335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6989976809697010102635113 5242482607272757576976335)
  ·
    refine ⟨7863723910909136365464503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5242482607272757576976335 7863723910909136365464503)
    ·
      refine ⟨11795585866363704548196755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7863723910909136365464503 11795585866363704548196755)
      ·
        refine ⟨17693378799545556822295133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11795585866363704548196755 17693378799545556822295133)
        ·
          refine ⟨6635017049829583808360675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17693378799545556822295133 6635017049829583808360675)
          ·
            refine ⟨9952525574744375712541013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6635017049829583808360675 9952525574744375712541013)
            ·
              refine ⟨29157789769758913220335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9952525574744375712541013 29157789769758913220335)
              ·
                rfl

theorem cell19_287472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_287472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287472 prefixEnd_287472 := by exact prefixLift 287472
  have htrace : WordTrace (prefixWord ++ tailWord_287472) baseStart_287472 baseEnd_287472 := by
    simpa [prefixWord, tailWord_287472, baseEnd_287472] using wordTrace_append hprefix tailTrace_287472
  have hstable : (prefixWord ++ tailWord_287472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287472).length < 2 ^ (prefixWord ++ tailWord_287472).sum := by decide
  have hdescent : baseEnd_287472 < baseStart_287472 := by decide
  rcases family_descends (prefixWord ++ tailWord_287472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287491 : List Nat := [1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_287491 : Nat := 118140960795 + 287491 * 2 ^ 59
def prefixEnd_287491 : Nat := 4983230072969 + 3 ^ 40 * 287491 * 2
def baseEnd_287491 : Nat := 87479150721090325238731

theorem tailTrace_287491 : CollatzResearch.WordTrace tailWord_287491 prefixEnd_287491 87479150721090325238731 := by
  unfold tailWord_287491
  simp only [CollatzResearch.WordTrace]
  refine ⟨10485658201476681398894327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6990438800984454265929551 10485658201476681398894327)
  ·
    refine ⟨15728487302215022098341491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10485658201476681398894327 15728487302215022098341491)
    ·
      refine ⟨23592730953322533147512237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15728487302215022098341491 23592730953322533147512237)
      ·
        refine ⟨8847274107495949930317089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23592730953322533147512237 8847274107495949930317089)
        ·
          refine ⟨6635455580621962447737817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8847274107495949930317089 6635455580621962447737817)
          ·
            refine ⟨4976591685466471835803363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6635455580621962447737817 4976591685466471835803363)
            ·
              refine ⟨7464887528199707753705045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976591685466471835803363 7464887528199707753705045)
              ·
                refine ⟨87479150721090325238731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7464887528199707753705045 87479150721090325238731)
                ·
                  rfl

theorem cell19_287491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_287491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287491 prefixEnd_287491 := by exact prefixLift 287491
  have htrace : WordTrace (prefixWord ++ tailWord_287491) baseStart_287491 baseEnd_287491 := by
    simpa [prefixWord, tailWord_287491, baseEnd_287491] using wordTrace_append hprefix tailTrace_287491
  have hstable : (prefixWord ++ tailWord_287491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287491).length < 2 ^ (prefixWord ++ tailWord_287491).sum := by decide
  have hdescent : baseEnd_287491 < baseStart_287491 := by decide
  rcases family_descends (prefixWord ++ tailWord_287491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287542 : List Nat := [5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_287542 : Nat := 118140960795 + 287542 * 2 ^ 59
def prefixEnd_287542 : Nat := 4983230072969 + 3 ^ 40 * 287542 * 2
def baseEnd_287542 : Nat := 87494669247537318105259

theorem tailTrace_287542 : CollatzResearch.WordTrace tailWord_287542 prefixEnd_287542 87494669247537318105259 := by
  unfold tailWord_287542
  simp only [CollatzResearch.WordTrace]
  refine ⟨655469895268244819312555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6991678882861278072667253 655469895268244819312555)
  ·
    refine ⟨983204842902367228968833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655469895268244819312555 983204842902367228968833)
    ·
      refine ⟨737403632176775421726625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 983204842902367228968833 737403632176775421726625)
      ·
        refine ⟨553052724132581566294969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 737403632176775421726625 553052724132581566294969)
        ·
          refine ⟨414789543099436174721227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553052724132581566294969 414789543099436174721227)
          ·
            refine ⟨622184314649154262081841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414789543099436174721227 622184314649154262081841)
            ·
              refine ⟨466638235986865696561381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622184314649154262081841 466638235986865696561381)
              ·
                refine ⟨87494669247537318105259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466638235986865696561381 87494669247537318105259)
                ·
                  rfl

theorem cell19_287542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_287542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287542 prefixEnd_287542 := by exact prefixLift 287542
  have htrace : WordTrace (prefixWord ++ tailWord_287542) baseStart_287542 baseEnd_287542 := by
    simpa [prefixWord, tailWord_287542, baseEnd_287542] using wordTrace_append hprefix tailTrace_287542
  have hstable : (prefixWord ++ tailWord_287542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287542).length < 2 ^ (prefixWord ++ tailWord_287542).sum := by decide
  have hdescent : baseEnd_287542 < baseStart_287542 := by decide
  rcases family_descends (prefixWord ++ tailWord_287542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287698 : List Nat := [3, 2, 2, 3, 1, 1, 7]
def baseStart_287698 : Nat := 118140960795 + 287698 * 2 ^ 59
def prefixEnd_287698 : Nat := 4983230072969 + 3 ^ 40 * 287698 * 2
def baseEnd_287698 : Nat := 29180712560458392879389

theorem tailTrace_287698 : CollatzResearch.WordTrace tailWord_287698 prefixEnd_287698 29180712560458392879389 := by
  unfold tailWord_287698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623302027931688937919937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6995472074484503834453165 2623302027931688937919937)
  ·
    refine ⟨1967476520948766703439953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2623302027931688937919937 1967476520948766703439953)
    ·
      refine ⟨1475607390711575027579965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1967476520948766703439953 1475607390711575027579965)
      ·
        refine ⟨553352771516840635342487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1475607390711575027579965 553352771516840635342487)
        ·
          refine ⟨830029157275260953013731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553352771516840635342487 830029157275260953013731)
          ·
            refine ⟨1245043735912891429520597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830029157275260953013731 1245043735912891429520597)
            ·
              refine ⟨29180712560458392879389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1245043735912891429520597 29180712560458392879389)
              ·
                rfl

theorem cell19_287698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_287698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287698 prefixEnd_287698 := by exact prefixLift 287698
  have htrace : WordTrace (prefixWord ++ tailWord_287698) baseStart_287698 baseEnd_287698 := by
    simpa [prefixWord, tailWord_287698, baseEnd_287698] using wordTrace_append hprefix tailTrace_287698
  have hstable : (prefixWord ++ tailWord_287698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287698).length < 2 ^ (prefixWord ++ tailWord_287698).sum := by decide
  have hdescent : baseEnd_287698 < baseStart_287698 := by decide
  rcases family_descends (prefixWord ++ tailWord_287698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287772 : List Nat := [2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_287772 : Nat := 118140960795 + 287772 * 2 ^ 59
def prefixEnd_287772 : Nat := 4983230072969 + 3 ^ 40 * 287772 * 2
def baseEnd_287772 : Nat := 87564654758964932993521

theorem tailTrace_287772 : CollatzResearch.WordTrace tailWord_287772 prefixEnd_287772 87564654758964932993521 := by
  unfold tailWord_287772
  simp only [CollatzResearch.WordTrace]
  refine ⟨5247953556729333194936785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6997271408972444259915713 5247953556729333194936785)
  ·
    refine ⟨3935965167546999896202589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5247953556729333194936785 3935965167546999896202589)
    ·
      refine ⟨1475986937830124961075971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3935965167546999896202589 1475986937830124961075971)
      ·
        refine ⟨2213980406745187441613957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475986937830124961075971 2213980406745187441613957)
        ·
          refine ⟨415121326264722645302617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2213980406745187441613957 415121326264722645302617)
          ·
            refine ⟨311340994698541983976963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415121326264722645302617 311340994698541983976963)
            ·
              refine ⟨467011492047812975965445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311340994698541983976963 467011492047812975965445)
              ·
                refine ⟨87564654758964932993521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467011492047812975965445 87564654758964932993521)
                ·
                  rfl

theorem cell19_287772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_287772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287772 prefixEnd_287772 := by exact prefixLift 287772
  have htrace : WordTrace (prefixWord ++ tailWord_287772) baseStart_287772 baseEnd_287772 := by
    simpa [prefixWord, tailWord_287772, baseEnd_287772] using wordTrace_append hprefix tailTrace_287772
  have hstable : (prefixWord ++ tailWord_287772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287772).length < 2 ^ (prefixWord ++ tailWord_287772).sum := by decide
  have hdescent : baseEnd_287772 < baseStart_287772 := by decide
  rcases family_descends (prefixWord ++ tailWord_287772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287793 : List Nat := [1, 2, 2, 3, 1, 2, 5, 3]
def baseStart_287793 : Nat := 118140960795 + 287793 * 2 ^ 59
def prefixEnd_287793 : Nat := 4983230072969 + 3 ^ 40 * 287793 * 2
def baseEnd_287793 : Nat := 87571044740443106526797

theorem tailTrace_287793 : CollatzResearch.WordTrace tailWord_287793 prefixEnd_287793 87571044740443106526797 := by
  unfold tailWord_287793
  simp only [CollatzResearch.WordTrace]
  refine ⟨10496673046382586976388033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6997782030921724650925355 10496673046382586976388033)
  ·
    refine ⟨7872504784786940232291025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10496673046382586976388033 7872504784786940232291025)
    ·
      refine ⟨5904378588590205174218269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7872504784786940232291025 5904378588590205174218269)
      ·
        refine ⟨2214141970721326940331851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5904378588590205174218269 2214141970721326940331851)
        ·
          refine ⟨3321212956081990410497777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214141970721326940331851 3321212956081990410497777)
          ·
            refine ⟨2490909717061492807873333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3321212956081990410497777 2490909717061492807873333)
            ·
              refine ⟨233522785974514950738125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2490909717061492807873333 233522785974514950738125)
              ·
                refine ⟨87571044740443106526797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233522785974514950738125 87571044740443106526797)
                ·
                  rfl

theorem cell19_287793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_287793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287793 prefixEnd_287793 := by exact prefixLift 287793
  have htrace : WordTrace (prefixWord ++ tailWord_287793) baseStart_287793 baseEnd_287793 := by
    simpa [prefixWord, tailWord_287793, baseEnd_287793] using wordTrace_append hprefix tailTrace_287793
  have hstable : (prefixWord ++ tailWord_287793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287793).length < 2 ^ (prefixWord ++ tailWord_287793).sum := by decide
  have hdescent : baseEnd_287793 < baseStart_287793 := by decide
  rcases family_descends (prefixWord ++ tailWord_287793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287848 : List Nat := [2, 1, 4, 4, 1, 1, 1, 5]
def baseStart_287848 : Nat := 118140960795 + 287848 * 2 ^ 59
def prefixEnd_287848 : Nat := 4983230072969 + 3 ^ 40 * 287848 * 2
def baseEnd_287848 : Nat := 87587780406219275304425

theorem tailTrace_287848 : CollatzResearch.WordTrace tailWord_287848 prefixEnd_287848 87587780406219275304425 := by
  unfold tailWord_287848
  simp only [CollatzResearch.WordTrace]
  refine ⟨5249339530591665684820099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6999119374122220913093465 5249339530591665684820099)
  ·
    refine ⟨7874009295887498527230149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5249339530591665684820099 7874009295887498527230149)
    ·
      refine ⟨1476376742978905973855653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7874009295887498527230149 1476376742978905973855653)
      ·
        refine ⟨276820639308544870097935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1476376742978905973855653 276820639308544870097935)
        ·
          refine ⟨415230958962817305146903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276820639308544870097935 415230958962817305146903)
          ·
            refine ⟨622846438444225957720355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415230958962817305146903 622846438444225957720355)
            ·
              refine ⟨934269657666338936580533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622846438444225957720355 934269657666338936580533)
              ·
                refine ⟨87587780406219275304425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 934269657666338936580533 87587780406219275304425)
                ·
                  rfl

theorem cell19_287848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_287848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287848 prefixEnd_287848 := by exact prefixLift 287848
  have htrace : WordTrace (prefixWord ++ tailWord_287848) baseStart_287848 baseEnd_287848 := by
    simpa [prefixWord, tailWord_287848, baseEnd_287848] using wordTrace_append hprefix tailTrace_287848
  have hstable : (prefixWord ++ tailWord_287848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287848).length < 2 ^ (prefixWord ++ tailWord_287848).sum := by decide
  have hdescent : baseEnd_287848 < baseStart_287848 := by decide
  rcases family_descends (prefixWord ++ tailWord_287848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287850 : List Nat := [3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_287850 : Nat := 118140960795 + 287850 * 2 ^ 59
def prefixEnd_287850 : Nat := 4983230072969 + 3 ^ 40 * 287850 * 2
def baseEnd_287850 : Nat := 87588388975883863259975

theorem tailTrace_287850 : CollatzResearch.WordTrace tailWord_287850 prefixEnd_287850 87588388975883863259975 := by
  unfold tailWord_287850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624688001794021427803251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6999168004784057140808669 2624688001794021427803251)
  ·
    refine ⟨3937032002691032141704877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2624688001794021427803251 3937032002691032141704877)
    ·
      refine ⟨1476387001009137053139329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3937032002691032141704877 1476387001009137053139329)
      ·
        refine ⟨1107290250756852789854497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1476387001009137053139329 1107290250756852789854497)
        ·
          refine ⟨830467688067639592390873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1107290250756852789854497 830467688067639592390873)
          ·
            refine ⟨622850766050729694293155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830467688067639592390873 622850766050729694293155)
            ·
              refine ⟨934276149076094541439733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622850766050729694293155 934276149076094541439733)
              ·
                refine ⟨87588388975883863259975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 934276149076094541439733 87588388975883863259975)
                ·
                  rfl

theorem cell19_287850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_287850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287850 prefixEnd_287850 := by exact prefixLift 287850
  have htrace : WordTrace (prefixWord ++ tailWord_287850) baseStart_287850 baseEnd_287850 := by
    simpa [prefixWord, tailWord_287850, baseEnd_287850] using wordTrace_append hprefix tailTrace_287850
  have hstable : (prefixWord ++ tailWord_287850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287850).length < 2 ^ (prefixWord ++ tailWord_287850).sum := by decide
  have hdescent : baseEnd_287850 < baseStart_287850 := by decide
  rcases family_descends (prefixWord ++ tailWord_287850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287852 : List Nat := [2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_287852 : Nat := 118140960795 + 287852 * 2 ^ 59
def prefixEnd_287852 : Nat := 4983230072969 + 3 ^ 40 * 287852 * 2
def baseEnd_287852 : Nat := 87588997545548451215525

theorem tailTrace_287852 : CollatzResearch.WordTrace tailWord_287852 prefixEnd_287852 87588997545548451215525 := by
  unfold tailWord_287852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5249412476584420026392905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6999216635445893368523873 5249412476584420026392905)
  ·
    refine ⟨3937059357438315019794679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5249412476584420026392905 3937059357438315019794679)
    ·
      refine ⟨5905589036157472529692019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3937059357438315019794679 5905589036157472529692019)
      ·
        refine ⟨8858383554236208794538029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5905589036157472529692019 8858383554236208794538029)
        ·
          refine ⟨3321893832838578297951761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8858383554236208794538029 3321893832838578297951761)
          ·
            refine ⟨2491420374628933723463821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3321893832838578297951761 2491420374628933723463821)
            ·
              refine ⟨934282640485850146298933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2491420374628933723463821 934282640485850146298933)
              ·
                refine ⟨87588997545548451215525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 934282640485850146298933 87588997545548451215525)
                ·
                  rfl

theorem cell19_287852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_287852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287852 prefixEnd_287852 := by exact prefixLift 287852
  have htrace : WordTrace (prefixWord ++ tailWord_287852) baseStart_287852 baseEnd_287852 := by
    simpa [prefixWord, tailWord_287852, baseEnd_287852] using wordTrace_append hprefix tailTrace_287852
  have hstable : (prefixWord ++ tailWord_287852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287852).length < 2 ^ (prefixWord ++ tailWord_287852).sum := by decide
  have hdescent : baseEnd_287852 < baseStart_287852 := by decide
  rcases family_descends (prefixWord ++ tailWord_287852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287909 : List Nat := [1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_287909 : Nat := 118140960795 + 287909 * 2 ^ 59
def prefixEnd_287909 : Nat := 4983230072969 + 3 ^ 40 * 287909 * 2
def baseEnd_287909 : Nat := 87606341780989207948703

theorem tailTrace_287909 : CollatzResearch.WordTrace tailWord_287909 prefixEnd_287909 87606341780989207948703 := by
  unfold tailWord_287909
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500903913962338787610781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7000602609308225858407187 10500903913962338787610781)
  ·
    refine ⟨3937838967735877045354043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10500903913962338787610781 3937838967735877045354043)
    ·
      refine ⟨5906758451603815568031065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3937838967735877045354043 5906758451603815568031065)
      ·
        refine ⟨4430068838702861676023299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5906758451603815568031065 4430068838702861676023299)
        ·
          refine ⟨6645103258054292514034949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4430068838702861676023299 6645103258054292514034949)
          ·
            refine ⟨1245956860885179846381553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6645103258054292514034949 1245956860885179846381553)
            ·
              refine ⟨934467645663884884786165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245956860885179846381553 934467645663884884786165)
              ·
                refine ⟨87606341780989207948703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 934467645663884884786165 87606341780989207948703)
                ·
                  rfl

theorem cell19_287909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_287909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_287909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_287909 prefixEnd_287909 := by exact prefixLift 287909
  have htrace : WordTrace (prefixWord ++ tailWord_287909) baseStart_287909 baseEnd_287909 := by
    simpa [prefixWord, tailWord_287909, baseEnd_287909] using wordTrace_append hprefix tailTrace_287909
  have hstable : (prefixWord ++ tailWord_287909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287909).length < 2 ^ (prefixWord ++ tailWord_287909).sum := by decide
  have hdescent : baseEnd_287909 < baseStart_287909 := by decide
  rcases family_descends (prefixWord ++ tailWord_287909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288023 : List Nat := [1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_288023 : Nat := 118140960795 + 288023 * 2 ^ 59
def prefixEnd_288023 : Nat := 4983230072969 + 3 ^ 40 * 288023 * 2
def baseEnd_288023 : Nat := 87641030251870721415059

theorem tailTrace_288023 : CollatzResearch.WordTrace tailWord_288023 prefixEnd_288023 87641030251870721415059 := by
  unfold tailWord_288023
  simp only [CollatzResearch.WordTrace]
  refine ⟨10505061835549336257260723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7003374557032890838173815 10505061835549336257260723)
  ·
    refine ⟨15757592753324004385891085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10505061835549336257260723 15757592753324004385891085)
    ·
      refine ⟨5909097282496501644709157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15757592753324004385891085 5909097282496501644709157)
      ·
        refine ⟨1107955740468094058382967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5909097282496501644709157 1107955740468094058382967)
        ·
          refine ⟨1661933610702141087574451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107955740468094058382967 1661933610702141087574451)
          ·
            refine ⟨2492900416053211631361677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661933610702141087574451 2492900416053211631361677)
            ·
              refine ⟨934837656019954361760629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2492900416053211631361677 934837656019954361760629)
              ·
                refine ⟨87641030251870721415059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 934837656019954361760629 87641030251870721415059)
                ·
                  rfl

theorem cell19_288023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_288023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288023 prefixEnd_288023 := by exact prefixLift 288023
  have htrace : WordTrace (prefixWord ++ tailWord_288023) baseStart_288023 baseEnd_288023 := by
    simpa [prefixWord, tailWord_288023, baseEnd_288023] using wordTrace_append hprefix tailTrace_288023
  have hstable : (prefixWord ++ tailWord_288023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288023).length < 2 ^ (prefixWord ++ tailWord_288023).sum := by decide
  have hdescent : baseEnd_288023 < baseStart_288023 := by decide
  rcases family_descends (prefixWord ++ tailWord_288023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288040 : List Nat := [2, 1, 5, 1, 2, 3, 5]
def baseStart_288040 : Nat := 118140960795 + 288040 * 2 ^ 59
def prefixEnd_288040 : Nat := 4983230072969 + 3 ^ 40 * 288040 * 2
def baseEnd_288040 : Nat := 29215401031339906345745

theorem tailTrace_288040 : CollatzResearch.WordTrace tailWord_288040 prefixEnd_288040 29215401031339906345745 := by
  unfold tailWord_288040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5252840938243874080314787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7003787917658498773753049 5252840938243874080314787)
  ·
    refine ⟨7879261407365811120472181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5252840938243874080314787 7879261407365811120472181)
    ·
      refine ⟨738680756940544792544267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7879261407365811120472181 738680756940544792544267)
      ·
        refine ⟨1108021135410817188816401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738680756940544792544267 1108021135410817188816401)
        ·
          refine ⟨831015851558112891612301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1108021135410817188816401 831015851558112891612301)
          ·
            refine ⟨311630944334292334354613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 831015851558112891612301 311630944334292334354613)
            ·
              refine ⟨29215401031339906345745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 311630944334292334354613 29215401031339906345745)
              ·
                rfl

theorem cell19_288040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_288040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288040 prefixEnd_288040 := by exact prefixLift 288040
  have htrace : WordTrace (prefixWord ++ tailWord_288040) baseStart_288040 baseEnd_288040 := by
    simpa [prefixWord, tailWord_288040, baseEnd_288040] using wordTrace_append hprefix tailTrace_288040
  have hstable : (prefixWord ++ tailWord_288040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288040).length < 2 ^ (prefixWord ++ tailWord_288040).sum := by decide
  have hdescent : baseEnd_288040 < baseStart_288040 := by decide
  rcases family_descends (prefixWord ++ tailWord_288040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288093 : List Nat := [1, 4, 5, 1, 2, 6]
def baseStart_288093 : Nat := 118140960795 + 288093 * 2 ^ 59
def prefixEnd_288093 : Nat := 4983230072969 + 3 ^ 40 * 288093 * 2
def baseEnd_288093 : Nat := 9740258910014588873257

theorem tailTrace_288093 : CollatzResearch.WordTrace tailWord_288093 prefixEnd_288093 9740258910014588873257 := by
  unfold tailWord_288093
  simp only [CollatzResearch.WordTrace]
  refine ⟨10507614945295738212308933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7005076630197158808205955 10507614945295738212308933)
  ·
    refine ⟨1970177802242950914807925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10507614945295738212308933 1970177802242950914807925)
    ·
      refine ⟨184704168960276648263243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1970177802242950914807925 184704168960276648263243)
      ·
        refine ⟨277056253440414972394865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184704168960276648263243 277056253440414972394865)
        ·
          refine ⟨207792190080311229296149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277056253440414972394865 207792190080311229296149)
          ·
            refine ⟨9740258910014588873257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 207792190080311229296149 9740258910014588873257)
            ·
              rfl

theorem cell19_288093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 6].length) (baseStart_288093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288093 prefixEnd_288093 := by exact prefixLift 288093
  have htrace : WordTrace (prefixWord ++ tailWord_288093) baseStart_288093 baseEnd_288093 := by
    simpa [prefixWord, tailWord_288093, baseEnd_288093] using wordTrace_append hprefix tailTrace_288093
  have hstable : (prefixWord ++ tailWord_288093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288093).length < 2 ^ (prefixWord ++ tailWord_288093).sum := by decide
  have hdescent : baseEnd_288093 < baseStart_288093 := by decide
  rcases family_descends (prefixWord ++ tailWord_288093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288135 : List Nat := [1, 1, 4, 2, 2, 3, 3, 3]
def baseStart_288135 : Nat := 118140960795 + 288135 * 2 ^ 59
def prefixEnd_288135 : Nat := 4983230072969 + 3 ^ 40 * 288135 * 2
def baseEnd_288135 : Nat := 87675110153087646925865

theorem tailTrace_288135 : CollatzResearch.WordTrace tailWord_288135 prefixEnd_288135 87675110153087646925865 := by
  unfold tailWord_288135
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509146811143579385337859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7006097874095719590225239 10509146811143579385337859)
  ·
    refine ⟨15763720216715369078006789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10509146811143579385337859 15763720216715369078006789)
    ·
      refine ⟨2955697540634131702126273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15763720216715369078006789 2955697540634131702126273)
      ·
        refine ⟨2216773155475598776594705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2955697540634131702126273 2216773155475598776594705)
        ·
          refine ⟨1662579866606699082446029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2216773155475598776594705 1662579866606699082446029)
          ·
            refine ⟨623467449977512155917261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1662579866606699082446029 623467449977512155917261)
            ·
              refine ⟨233800293741567058468973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623467449977512155917261 233800293741567058468973)
              ·
                refine ⟨87675110153087646925865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233800293741567058468973 87675110153087646925865)
                ·
                  rfl

theorem cell19_288135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_288135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288135 prefixEnd_288135 := by exact prefixLift 288135
  have htrace : WordTrace (prefixWord ++ tailWord_288135) baseStart_288135 baseEnd_288135 := by
    simpa [prefixWord, tailWord_288135, baseEnd_288135] using wordTrace_append hprefix tailTrace_288135
  have hstable : (prefixWord ++ tailWord_288135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288135).length < 2 ^ (prefixWord ++ tailWord_288135).sum := by decide
  have hdescent : baseEnd_288135 < baseStart_288135 := by decide
  rcases family_descends (prefixWord ++ tailWord_288135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288188 : List Nat := [2, 2, 2, 4, 3, 1, 2, 3]
def baseStart_288188 : Nat := 118140960795 + 288188 * 2 ^ 59
def prefixEnd_288188 : Nat := 4983230072969 + 3 ^ 40 * 288188 * 2
def baseEnd_288188 : Nat := 87691237249199227747943

theorem tailTrace_288188 : CollatzResearch.WordTrace tailWord_288188 prefixEnd_288188 87691237249199227747943 := by
  unfold tailWord_288188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255539939975784718508609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7007386586634379624678145 5255539939975784718508609)
  ·
    refine ⟨3941654954981838538881457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5255539939975784718508609 3941654954981838538881457)
    ·
      refine ⟨2956241216236378904161093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3941654954981838538881457 2956241216236378904161093)
      ·
        refine ⟨554295228044321044530205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2956241216236378904161093 554295228044321044530205)
        ·
          refine ⟨207860710516620391698827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 554295228044321044530205 207860710516620391698827)
          ·
            refine ⟨311791065774930587548241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207860710516620391698827 311791065774930587548241)
            ·
              refine ⟨233843299331197940661181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311791065774930587548241 233843299331197940661181)
              ·
                refine ⟨87691237249199227747943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233843299331197940661181 87691237249199227747943)
                ·
                  rfl

theorem cell19_288188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_288188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288188 prefixEnd_288188 := by exact prefixLift 288188
  have htrace : WordTrace (prefixWord ++ tailWord_288188) baseStart_288188 baseEnd_288188 := by
    simpa [prefixWord, tailWord_288188, baseEnd_288188] using wordTrace_append hprefix tailTrace_288188
  have hstable : (prefixWord ++ tailWord_288188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288188).length < 2 ^ (prefixWord ++ tailWord_288188).sum := by decide
  have hdescent : baseEnd_288188 < baseStart_288188 := by decide
  rcases family_descends (prefixWord ++ tailWord_288188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288232 : List Nat := [2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_288232 : Nat := 118140960795 + 288232 * 2 ^ 59
def prefixEnd_288232 : Nat := 4983230072969 + 3 ^ 40 * 288232 * 2
def baseEnd_288232 : Nat := 87704625781820162770045

theorem tailTrace_288232 : CollatzResearch.WordTrace tailWord_288232 prefixEnd_288232 87704625781820162770045 := by
  unfold tailWord_288232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5256342345896082475809475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7008456461194776634412633 5256342345896082475809475)
  ·
    refine ⟨7884513518844123713714213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5256342345896082475809475 7884513518844123713714213)
    ·
      refine ⟨1478346284783273196321415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7884513518844123713714213 1478346284783273196321415)
      ·
        refine ⟨2217519427174909794482123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478346284783273196321415 2217519427174909794482123)
        ·
          refine ⟨3326279140762364691723185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217519427174909794482123 3326279140762364691723185)
          ·
            refine ⟨2494709355571773518792389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3326279140762364691723185 2494709355571773518792389)
            ·
              refine ⟨467758004169707534773573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2494709355571773518792389 467758004169707534773573)
              ·
                refine ⟨87704625781820162770045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467758004169707534773573 87704625781820162770045)
                ·
                  rfl

theorem cell19_288232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_288232 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288232 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288232 prefixEnd_288232 := by exact prefixLift 288232
  have htrace : WordTrace (prefixWord ++ tailWord_288232) baseStart_288232 baseEnd_288232 := by
    simpa [prefixWord, tailWord_288232, baseEnd_288232] using wordTrace_append hprefix tailTrace_288232
  have hstable : (prefixWord ++ tailWord_288232).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288232).length < 2 ^ (prefixWord ++ tailWord_288232).sum := by decide
  have hdescent : baseEnd_288232 < baseStart_288232 := by decide
  rcases family_descends (prefixWord ++ tailWord_288232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288270 : List Nat := [4, 1, 1, 2, 4, 7]
def baseStart_288270 : Nat := 118140960795 + 288270 * 2 ^ 59
def prefixEnd_288270 : Nat := 4983230072969 + 3 ^ 40 * 288270 * 2
def baseEnd_288270 : Nat := 9746243178383037102833

theorem tailTrace_288270 : CollatzResearch.WordTrace tailWord_288270 prefixEnd_288270 9746243178383037102833 := by
  unfold tailWord_288270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314258833206812180187783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7009380443769664961001509 1314258833206812180187783)
  ·
    refine ⟨1971388249810218270281675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1314258833206812180187783 1971388249810218270281675)
    ·
      refine ⟨2957082374715327405422513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971388249810218270281675 2957082374715327405422513)
      ·
        refine ⟨2217811781036495554066885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2957082374715327405422513 2217811781036495554066885)
        ·
          refine ⟨415839708944342916387541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2217811781036495554066885 415839708944342916387541)
          ·
            refine ⟨9746243178383037102833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 415839708944342916387541 9746243178383037102833)
            ·
              rfl

theorem cell19_288270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_288270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288270 prefixEnd_288270 := by exact prefixLift 288270
  have htrace : WordTrace (prefixWord ++ tailWord_288270) baseStart_288270 baseEnd_288270 := by
    simpa [prefixWord, tailWord_288270, baseEnd_288270] using wordTrace_append hprefix tailTrace_288270
  have hstable : (prefixWord ++ tailWord_288270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288270).length < 2 ^ (prefixWord ++ tailWord_288270).sum := by decide
  have hdescent : baseEnd_288270 < baseStart_288270 := by decide
  rcases family_descends (prefixWord ++ tailWord_288270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288289 : List Nat := [1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_288289 : Nat := 118140960795 + 288289 * 2 ^ 59
def prefixEnd_288289 : Nat := 4983230072969 + 3 ^ 40 * 288289 * 2
def baseEnd_288289 : Nat := 87721970017260919503223

theorem tailTrace_288289 : CollatzResearch.WordTrace tailWord_288289 prefixEnd_288289 87721970017260919503223 := by
  unfold tailWord_288289
  simp only [CollatzResearch.WordTrace]
  refine ⟨10514763652585663686443921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7009842435057109124295947 10514763652585663686443921)
  ·
    refine ⟨7886072739439247764832941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10514763652585663686443921 7886072739439247764832941)
    ·
      refine ⟨2957277277289717911812353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7886072739439247764832941 2957277277289717911812353)
      ·
        refine ⟨2217957957967288433859265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2957277277289717911812353 2217957957967288433859265)
        ·
          refine ⟨1663468468475466325394449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2217957957967288433859265 1663468468475466325394449)
          ·
            refine ⟨1247601351356599744045837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663468468475466325394449 1247601351356599744045837)
            ·
              refine ⟨467850506758724904017189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1247601351356599744045837 467850506758724904017189)
              ·
                refine ⟨87721970017260919503223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467850506758724904017189 87721970017260919503223)
                ·
                  rfl

theorem cell19_288289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_288289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288289 prefixEnd_288289 := by exact prefixLift 288289
  have htrace : WordTrace (prefixWord ++ tailWord_288289) baseStart_288289 baseEnd_288289 := by
    simpa [prefixWord, tailWord_288289, baseEnd_288289] using wordTrace_append hprefix tailTrace_288289
  have hstable : (prefixWord ++ tailWord_288289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288289).length < 2 ^ (prefixWord ++ tailWord_288289).sum := by decide
  have hdescent : baseEnd_288289 < baseStart_288289 := by decide
  rcases family_descends (prefixWord ++ tailWord_288289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288327 : List Nat := [1, 1, 4, 1, 5, 1, 6]
def baseStart_288327 : Nat := 118140960795 + 288327 * 2 ^ 59
def prefixEnd_288327 : Nat := 4983230072969 + 3 ^ 40 * 288327 * 2
def baseEnd_288327 : Nat := 29244510946962696886225

theorem tailTrace_288327 : CollatzResearch.WordTrace tailWord_288327 prefixEnd_288327 29244510946962696886225 := by
  unfold tailWord_288327
  simp only [CollatzResearch.WordTrace]
  refine ⟨10516149626447996176327235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7010766417631997450884823 10516149626447996176327235)
  ·
    refine ⟨15774224439671994264490853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10516149626447996176327235 15774224439671994264490853)
    ·
      refine ⟨2957667082438498924592035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15774224439671994264490853 2957667082438498924592035)
      ·
        refine ⟨4436500623657748386888053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957667082438498924592035 4436500623657748386888053)
        ·
          refine ⟨415921933467913911270755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4436500623657748386888053 415921933467913911270755)
          ·
            refine ⟨623882900201870866906133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415921933467913911270755 623882900201870866906133)
            ·
              refine ⟨29244510946962696886225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 623882900201870866906133 29244510946962696886225)
              ·
                rfl

theorem cell19_288327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_288327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288327 prefixEnd_288327 := by exact prefixLift 288327
  have htrace : WordTrace (prefixWord ++ tailWord_288327) baseStart_288327 baseEnd_288327 := by
    simpa [prefixWord, tailWord_288327, baseEnd_288327] using wordTrace_append hprefix tailTrace_288327
  have hstable : (prefixWord ++ tailWord_288327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288327).length < 2 ^ (prefixWord ++ tailWord_288327).sum := by decide
  have hdescent : baseEnd_288327 < baseStart_288327 := by decide
  rcases family_descends (prefixWord ++ tailWord_288327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288454 : List Nat := [6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_288454 : Nat := 118140960795 + 288454 * 2 ^ 59
def prefixEnd_288454 : Nat := 4983230072969 + 3 ^ 40 * 288454 * 2
def baseEnd_288454 : Nat := 87772177014589425836107

theorem tailTrace_288454 : CollatzResearch.WordTrace tailWord_288454 prefixEnd_288454 87772177014589425836107 := by
  unfold tailWord_288454
  simp only [CollatzResearch.WordTrace]
  refine ⟨328774428030871777068763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7013854464658597910800277 328774428030871777068763)
  ·
    refine ⟨493161642046307665603145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328774428030871777068763 493161642046307665603145)
    ·
      refine ⟨369871231534730749202359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 493161642046307665603145 369871231534730749202359)
      ·
        refine ⟨554806847302096123803539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369871231534730749202359 554806847302096123803539)
        ·
          refine ⟨832210270953144185705309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554806847302096123803539 832210270953144185705309)
          ·
            refine ⟨312078851607429069639491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 832210270953144185705309 312078851607429069639491)
            ·
              refine ⟨468118277411143604459237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312078851607429069639491 468118277411143604459237)
              ·
                refine ⟨87772177014589425836107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468118277411143604459237 87772177014589425836107)
                ·
                  rfl

theorem cell19_288454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_288454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288454 prefixEnd_288454 := by exact prefixLift 288454
  have htrace : WordTrace (prefixWord ++ tailWord_288454) baseStart_288454 baseEnd_288454 := by
    simpa [prefixWord, tailWord_288454, baseEnd_288454] using wordTrace_append hprefix tailTrace_288454
  have hstable : (prefixWord ++ tailWord_288454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288454).length < 2 ^ (prefixWord ++ tailWord_288454).sum := by decide
  have hdescent : baseEnd_288454 < baseStart_288454 := by decide
  rcases family_descends (prefixWord ++ tailWord_288454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288458 : List Nat := [3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_288458 : Nat := 118140960795 + 288458 * 2 ^ 59
def prefixEnd_288458 : Nat := 4983230072969 + 3 ^ 40 * 288458 * 2
def baseEnd_288458 : Nat := 87773394153918601747207

theorem tailTrace_288458 : CollatzResearch.WordTrace tailWord_288458 prefixEnd_288458 87773394153918601747207 := by
  unfold tailWord_288458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2630231897243351387336507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7013951725982270366230685 2630231897243351387336507)
  ·
    refine ⟨3945347845865027081004761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2630231897243351387336507 3945347845865027081004761)
    ·
      refine ⟨2959010884398770310753571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3945347845865027081004761 2959010884398770310753571)
      ·
        refine ⟨4438516326598155466130357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959010884398770310753571 4438516326598155466130357)
        ·
          refine ⟨416110905618577074949721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4438516326598155466130357 416110905618577074949721)
          ·
            refine ⟨312083179213932806212291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416110905618577074949721 312083179213932806212291)
            ·
              refine ⟨468124768820899209318437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312083179213932806212291 468124768820899209318437)
              ·
                refine ⟨87773394153918601747207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468124768820899209318437 87773394153918601747207)
                ·
                  rfl

theorem cell19_288458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_288458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288458 prefixEnd_288458 := by exact prefixLift 288458
  have htrace : WordTrace (prefixWord ++ tailWord_288458) baseStart_288458 baseEnd_288458 := by
    simpa [prefixWord, tailWord_288458, baseEnd_288458] using wordTrace_append hprefix tailTrace_288458
  have hstable : (prefixWord ++ tailWord_288458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288458).length < 2 ^ (prefixWord ++ tailWord_288458).sum := by decide
  have hdescent : baseEnd_288458 < baseStart_288458 := by decide
  rcases family_descends (prefixWord ++ tailWord_288458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288479 : List Nat := [1, 1, 2, 3, 2, 2, 5, 3]
def baseStart_288479 : Nat := 118140960795 + 288479 * 2 ^ 59
def prefixEnd_288479 : Nat := 4983230072969 + 3 ^ 40 * 288479 * 2
def baseEnd_288479 : Nat := 87779784135396775280483

theorem tailTrace_288479 : CollatzResearch.WordTrace tailWord_288479 prefixEnd_288479 87779784135396775280483 := by
  unfold tailWord_288479
  simp only [CollatzResearch.WordTrace]
  refine ⟨10521693521897326135860491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7014462347931550757240327 10521693521897326135860491)
  ·
    refine ⟨15782540282845989203790737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10521693521897326135860491 15782540282845989203790737)
    ·
      refine ⟨11836905212134491902843053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15782540282845989203790737 11836905212134491902843053)
      ·
        refine ⟨4438839454550434463566145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11836905212134491902843053 4438839454550434463566145)
        ·
          refine ⟨3329129590912825847674609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4438839454550434463566145 3329129590912825847674609)
          ·
            refine ⟨2496847193184619385755957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3329129590912825847674609 2496847193184619385755957)
            ·
              refine ⟨234079424361058067414621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2496847193184619385755957 234079424361058067414621)
              ·
                refine ⟨87779784135396775280483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234079424361058067414621 87779784135396775280483)
                ·
                  rfl

theorem cell19_288479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_288479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288479 prefixEnd_288479 := by exact prefixLift 288479
  have htrace : WordTrace (prefixWord ++ tailWord_288479) baseStart_288479 baseEnd_288479 := by
    simpa [prefixWord, tailWord_288479, baseEnd_288479] using wordTrace_append hprefix tailTrace_288479
  have hstable : (prefixWord ++ tailWord_288479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288479).length < 2 ^ (prefixWord ++ tailWord_288479).sum := by decide
  have hdescent : baseEnd_288479 < baseStart_288479 := by decide
  rcases family_descends (prefixWord ++ tailWord_288479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288536 : List Nat := [2, 1, 2, 3, 1, 1, 6, 3]
def baseStart_288536 : Nat := 118140960795 + 288536 * 2 ^ 59
def prefixEnd_288536 : Nat := 4983230072969 + 3 ^ 40 * 288536 * 2
def baseEnd_288536 : Nat := 87797128370837532013661

theorem tailTrace_288536 : CollatzResearch.WordTrace tailWord_288536 prefixEnd_288536 87797128370837532013661 := by
  unfold tailWord_288536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5261886241345412435342731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7015848321793883247123641 5261886241345412435342731)
  ·
    refine ⟨7892829362018118653014097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5261886241345412435342731 7892829362018118653014097)
    ·
      refine ⟨5919622021513588989760573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7892829362018118653014097 5919622021513588989760573)
      ·
        refine ⟨2219858258067595871160215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5919622021513588989760573 2219858258067595871160215)
        ·
          refine ⟨3329787387101393806740323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219858258067595871160215 3329787387101393806740323)
          ·
            refine ⟨4994681080652090710110485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329787387101393806740323 4994681080652090710110485)
            ·
              refine ⟨234125675655566752036429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4994681080652090710110485 234125675655566752036429)
              ·
                refine ⟨87797128370837532013661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234125675655566752036429 87797128370837532013661)
                ·
                  rfl

theorem cell19_288536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_288536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288536 prefixEnd_288536 := by exact prefixLift 288536
  have htrace : WordTrace (prefixWord ++ tailWord_288536) baseStart_288536 baseEnd_288536 := by
    simpa [prefixWord, tailWord_288536, baseEnd_288536] using wordTrace_append hprefix tailTrace_288536
  have hstable : (prefixWord ++ tailWord_288536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288536).length < 2 ^ (prefixWord ++ tailWord_288536).sum := by decide
  have hdescent : baseEnd_288536 < baseStart_288536 := by decide
  rcases family_descends (prefixWord ++ tailWord_288536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288574 : List Nat := [4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_288574 : Nat := 118140960795 + 288574 * 2 ^ 59
def prefixEnd_288574 : Nat := 4983230072969 + 3 ^ 40 * 288574 * 2
def baseEnd_288574 : Nat := 87808691194464703169113

theorem tailTrace_288574 : CollatzResearch.WordTrace tailWord_288574 prefixEnd_288574 87808691194464703169113 := by
  unfold tailWord_288574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315644807069144670071097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7016772304368771573712517 1315644807069144670071097)
  ·
    refine ⟨986733605301858502553323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1315644807069144670071097 986733605301858502553323)
    ·
      refine ⟨1480100407952787753829985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986733605301858502553323 1480100407952787753829985)
      ·
        refine ⟨1110075305964590815372489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1480100407952787753829985 1110075305964590815372489)
        ·
          refine ⟨832556479473443111529367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110075305964590815372489 832556479473443111529367)
          ·
            refine ⟨1248834719210164667294051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832556479473443111529367 1248834719210164667294051)
            ·
              refine ⟨1873252078815247000941077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248834719210164667294051 1873252078815247000941077)
              ·
                refine ⟨87808691194464703169113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1873252078815247000941077 87808691194464703169113)
                ·
                  rfl

theorem cell19_288574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_288574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288574 prefixEnd_288574 := by exact prefixLift 288574
  have htrace : WordTrace (prefixWord ++ tailWord_288574) baseStart_288574 baseEnd_288574 := by
    simpa [prefixWord, tailWord_288574, baseEnd_288574] using wordTrace_append hprefix tailTrace_288574
  have hstable : (prefixWord ++ tailWord_288574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288574).length < 2 ^ (prefixWord ++ tailWord_288574).sum := by decide
  have hdescent : baseEnd_288574 < baseStart_288574 := by decide
  rcases family_descends (prefixWord ++ tailWord_288574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288612 : List Nat := [2, 3, 1, 1, 6, 6]
def baseStart_288612 : Nat := 118140960795 + 288612 * 2 ^ 59
def prefixEnd_288612 : Nat := 4983230072969 + 3 ^ 40 * 288612 * 2
def baseEnd_288612 : Nat := 9757806002010208258285

theorem tailTrace_288612 : CollatzResearch.WordTrace tailWord_288612 prefixEnd_288612 9757806002010208258285 := by
  unfold tailWord_288612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5263272215207744925226045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7017696286943659900301393 5263272215207744925226045)
  ·
    refine ⟨1973727080702904346959767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5263272215207744925226045 1973727080702904346959767)
    ·
      refine ⟨2960590621054356520439651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973727080702904346959767 2960590621054356520439651)
      ·
        refine ⟨4440885931581534780659477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960590621054356520439651 4440885931581534780659477)
        ·
          refine ⟨208166528042884442843413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4440885931581534780659477 208166528042884442843413)
          ·
            refine ⟨9757806002010208258285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 208166528042884442843413 9757806002010208258285)
            ·
              rfl

theorem cell19_288612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 6].length) (baseStart_288612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288612 prefixEnd_288612 := by exact prefixLift 288612
  have htrace : WordTrace (prefixWord ++ tailWord_288612) baseStart_288612 baseEnd_288612 := by
    simpa [prefixWord, tailWord_288612, baseEnd_288612] using wordTrace_append hprefix tailTrace_288612
  have hstable : (prefixWord ++ tailWord_288612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288612).length < 2 ^ (prefixWord ++ tailWord_288612).sum := by decide
  have hdescent : baseEnd_288612 < baseStart_288612 := by decide
  rcases family_descends (prefixWord ++ tailWord_288612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288648 : List Nat := [2, 1, 3, 3, 3, 1, 3, 3]
def baseStart_288648 : Nat := 118140960795 + 288648 * 2 ^ 59
def prefixEnd_288648 : Nat := 4983230072969 + 3 ^ 40 * 288648 * 2
def baseEnd_288648 : Nat := 87831208272054457524467

theorem tailTrace_288648 : CollatzResearch.WordTrace tailWord_288648 prefixEnd_288648 87831208272054457524467 := by
  unfold tailWord_288648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5263928729142533999381299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7018571638856711999175065 5263928729142533999381299)
  ·
    refine ⟨7895893093713800999071949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5263928729142533999381299 7895893093713800999071949)
    ·
      refine ⟨2960959910142675374651981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7895893093713800999071949 2960959910142675374651981)
      ·
        refine ⟨1110359966303503265494493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2960959910142675374651981 1110359966303503265494493)
        ·
          refine ⟨416384987363813724560435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1110359966303503265494493 416384987363813724560435)
          ·
            refine ⟨624577481045720586840653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416384987363813724560435 624577481045720586840653)
            ·
              refine ⟨234216555392145220065245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 624577481045720586840653 234216555392145220065245)
              ·
                refine ⟨87831208272054457524467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234216555392145220065245 87831208272054457524467)
                ·
                  rfl

theorem cell19_288648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_288648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288648 prefixEnd_288648 := by exact prefixLift 288648
  have htrace : WordTrace (prefixWord ++ tailWord_288648) baseStart_288648 baseEnd_288648 := by
    simpa [prefixWord, tailWord_288648, baseEnd_288648] using wordTrace_append hprefix tailTrace_288648
  have hstable : (prefixWord ++ tailWord_288648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288648).length < 2 ^ (prefixWord ++ tailWord_288648).sum := by decide
  have hdescent : baseEnd_288648 < baseStart_288648 := by decide
  rcases family_descends (prefixWord ++ tailWord_288648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288781 : List Nat := [1, 7, 1, 2, 8]
def baseStart_288781 : Nat := 118140960795 + 288781 * 2 ^ 59
def prefixEnd_288781 : Nat := 4983230072969 + 3 ^ 40 * 288781 * 2
def baseEnd_288781 : Nat := 3254506598324057650687

theorem tailTrace_288781 : CollatzResearch.WordTrace tailWord_288781 prefixEnd_288781 3254506598324057650687 := by
  unfold tailWord_288781
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532708366803231713354197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7021805577868821142236131 10532708366803231713354197)
  ·
    refine ⟨246860352346950743281739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10532708366803231713354197 246860352346950743281739)
    ·
      refine ⟨370290528520426114922609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246860352346950743281739 370290528520426114922609)
      ·
        refine ⟨277717896390319586191957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370290528520426114922609 277717896390319586191957)
        ·
          refine ⟨3254506598324057650687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 277717896390319586191957 3254506598324057650687)
          ·
            rfl

theorem cell19_288781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 8].length) (baseStart_288781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288781 prefixEnd_288781 := by exact prefixLift 288781
  have htrace : WordTrace (prefixWord ++ tailWord_288781) baseStart_288781 baseEnd_288781 := by
    simpa [prefixWord, tailWord_288781, baseEnd_288781] using wordTrace_append hprefix tailTrace_288781
  have hstable : (prefixWord ++ tailWord_288781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288781).length < 2 ^ (prefixWord ++ tailWord_288781).sum := by decide
  have hdescent : baseEnd_288781 < baseStart_288781 := by decide
  rcases family_descends (prefixWord ++ tailWord_288781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288874 : List Nat := [3, 1, 3, 2, 4, 1, 2, 3]
def baseStart_288874 : Nat := 118140960795 + 288874 * 2 ^ 59
def prefixEnd_288874 : Nat := 4983230072969 + 3 ^ 40 * 288874 * 2
def baseEnd_288874 : Nat := 87899976644152896501629

theorem tailTrace_288874 : CollatzResearch.WordTrace tailWord_288874 prefixEnd_288874 87899976644152896501629 := by
  unfold tailWord_288874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634025088866577149122419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7024066903644205730993117 2634025088866577149122419)
  ·
    refine ⟨3951037633299865723683629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2634025088866577149122419 3951037633299865723683629)
    ·
      refine ⟨1481639112487449646381361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3951037633299865723683629 1481639112487449646381361)
      ·
        refine ⟨1111229334365587234786021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1481639112487449646381361 1111229334365587234786021)
        ·
          refine ⟨208355500193547606522379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1111229334365587234786021 208355500193547606522379)
          ·
            refine ⟨312533250290321409783569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208355500193547606522379 312533250290321409783569)
            ·
              refine ⟨234399937717741057337677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312533250290321409783569 234399937717741057337677)
              ·
                refine ⟨87899976644152896501629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234399937717741057337677 87899976644152896501629)
                ·
                  rfl

theorem cell19_288874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_288874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288874 prefixEnd_288874 := by exact prefixLift 288874
  have htrace : WordTrace (prefixWord ++ tailWord_288874) baseStart_288874 baseEnd_288874 := by
    simpa [prefixWord, tailWord_288874, baseEnd_288874] using wordTrace_append hprefix tailTrace_288874
  have hstable : (prefixWord ++ tailWord_288874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288874).length < 2 ^ (prefixWord ++ tailWord_288874).sum := by decide
  have hdescent : baseEnd_288874 < baseStart_288874 := by decide
  rcases family_descends (prefixWord ++ tailWord_288874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288880 : List Nat := [2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_288880 : Nat := 118140960795 + 288880 * 2 ^ 59
def prefixEnd_288880 : Nat := 4983230072969 + 3 ^ 40 * 288880 * 2
def baseEnd_288880 : Nat := 87901802353146660368279

theorem tailTrace_288880 : CollatzResearch.WordTrace tailWord_288880 prefixEnd_288880 87901802353146660368279 := by
  unfold tailWord_288880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268159596722285810604047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7024212795629714414138729 5268159596722285810604047)
  ·
    refine ⟨7902239395083428715906071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5268159596722285810604047 7902239395083428715906071)
    ·
      refine ⟨11853359092625143073859107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902239395083428715906071 11853359092625143073859107)
      ·
        refine ⟨17780038638937714610788661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853359092625143073859107 17780038638937714610788661)
        ·
          refine ⟨1666878622400410744761437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17780038638937714610788661 1666878622400410744761437)
          ·
            refine ⟨625079483400154029285539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1666878622400410744761437 625079483400154029285539)
            ·
              refine ⟨937619225100231043928309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625079483400154029285539 937619225100231043928309)
              ·
                refine ⟨87901802353146660368279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 937619225100231043928309 87901802353146660368279)
                ·
                  rfl

theorem cell19_288880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_288880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288880 prefixEnd_288880 := by exact prefixLift 288880
  have htrace : WordTrace (prefixWord ++ tailWord_288880) baseStart_288880 baseEnd_288880 := by
    simpa [prefixWord, tailWord_288880, baseEnd_288880] using wordTrace_append hprefix tailTrace_288880
  have hstable : (prefixWord ++ tailWord_288880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288880).length < 2 ^ (prefixWord ++ tailWord_288880).sum := by decide
  have hdescent : baseEnd_288880 < baseStart_288880 := by decide
  rcases family_descends (prefixWord ++ tailWord_288880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288897 : List Nat := [1, 2, 4, 2, 3, 2, 5]
def baseStart_288897 : Nat := 118140960795 + 288897 * 2 ^ 59
def prefixEnd_288897 : Nat := 4983230072969 + 3 ^ 40 * 288897 * 2
def baseEnd_288897 : Nat := 29302325065098552663485

theorem tailTrace_288897 : CollatzResearch.WordTrace tailWord_288897 prefixEnd_288897 29302325065098552663485 := by
  unfold tailWord_288897
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536939234382983524576945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7024626156255322349717963 10536939234382983524576945)
  ·
    refine ⟨7902704425787237643432709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10536939234382983524576945 7902704425787237643432709)
    ·
      refine ⟨1481757079835107058143633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7902704425787237643432709 1481757079835107058143633)
      ·
        refine ⟨1111317809876330293607725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1481757079835107058143633 1111317809876330293607725)
        ·
          refine ⟨416744178703623860102897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1111317809876330293607725 416744178703623860102897)
          ·
            refine ⟨312558134027717895077173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416744178703623860102897 312558134027717895077173)
            ·
              refine ⟨29302325065098552663485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 312558134027717895077173 29302325065098552663485)
              ·
                rfl

theorem cell19_288897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_288897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288897 prefixEnd_288897 := by exact prefixLift 288897
  have htrace : WordTrace (prefixWord ++ tailWord_288897) baseStart_288897 baseEnd_288897 := by
    simpa [prefixWord, tailWord_288897, baseEnd_288897] using wordTrace_append hprefix tailTrace_288897
  have hstable : (prefixWord ++ tailWord_288897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288897).length < 2 ^ (prefixWord ++ tailWord_288897).sum := by decide
  have hdescent : baseEnd_288897 < baseStart_288897 := by decide
  rcases family_descends (prefixWord ++ tailWord_288897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288899 : List Nat := [1, 1, 1, 3, 3, 5, 5]
def baseStart_288899 : Nat := 118140960795 + 288899 * 2 ^ 59
def prefixEnd_288899 : Nat := 4983230072969 + 3 ^ 40 * 288899 * 2
def baseEnd_288899 : Nat := 29302527921653415315335

theorem tailTrace_288899 : CollatzResearch.WordTrace tailWord_288899 prefixEnd_288899 29302527921653415315335 := by
  unfold tailWord_288899
  simp only [CollatzResearch.WordTrace]
  refine ⟨10537012180375737866149751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7024674786917158577433167 10537012180375737866149751)
  ·
    refine ⟨15805518270563606799224627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10537012180375737866149751 15805518270563606799224627)
    ·
      refine ⟨23708277405845410198836941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15805518270563606799224627 23708277405845410198836941)
      ·
        refine ⟨8890604027192028824563853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23708277405845410198836941 8890604027192028824563853)
        ·
          refine ⟨3333976510197010809211445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8890604027192028824563853 3333976510197010809211445)
          ·
            refine ⟨312560297830969763363573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3333976510197010809211445 312560297830969763363573)
            ·
              refine ⟨29302527921653415315335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 312560297830969763363573 29302527921653415315335)
              ·
                rfl

theorem cell19_288899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_288899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288899 prefixEnd_288899 := by exact prefixLift 288899
  have htrace : WordTrace (prefixWord ++ tailWord_288899) baseStart_288899 baseEnd_288899 := by
    simpa [prefixWord, tailWord_288899, baseEnd_288899] using wordTrace_append hprefix tailTrace_288899
  have hstable : (prefixWord ++ tailWord_288899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288899).length < 2 ^ (prefixWord ++ tailWord_288899).sum := by decide
  have hdescent : baseEnd_288899 < baseStart_288899 := by decide
  rcases family_descends (prefixWord ++ tailWord_288899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288956 : List Nat := [2, 2, 2, 3, 3, 7]
def baseStart_288956 : Nat := 118140960795 + 288956 * 2 ^ 59
def prefixEnd_288956 : Nat := 4983230072969 + 3 ^ 40 * 288956 * 2
def baseEnd_288956 : Nat := 9769436444489000297687

theorem tailTrace_288956 : CollatzResearch.WordTrace tailWord_288956 prefixEnd_288956 9769436444489000297687 := by
  unfold tailWord_288956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5269545570584618300487361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7026060760779491067316481 5269545570584618300487361)
  ·
    refine ⟨3952159177938463725365521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5269545570584618300487361 3952159177938463725365521)
    ·
      refine ⟨2964119383453847794024141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3952159177938463725365521 2964119383453847794024141)
      ·
        refine ⟨1111544768795192922759053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2964119383453847794024141 1111544768795192922759053)
        ·
          refine ⟨416829288298197346034645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1111544768795192922759053 416829288298197346034645)
          ·
            refine ⟨9769436444489000297687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 416829288298197346034645 9769436444489000297687)
            ·
              rfl

theorem cell19_288956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_288956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288956 prefixEnd_288956 := by exact prefixLift 288956
  have htrace : WordTrace (prefixWord ++ tailWord_288956) baseStart_288956 baseEnd_288956 := by
    simpa [prefixWord, tailWord_288956, baseEnd_288956] using wordTrace_append hprefix tailTrace_288956
  have hstable : (prefixWord ++ tailWord_288956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288956).length < 2 ^ (prefixWord ++ tailWord_288956).sum := by decide
  have hdescent : baseEnd_288956 < baseStart_288956 := by decide
  rcases family_descends (prefixWord ++ tailWord_288956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288988 : List Nat := [2, 2, 5, 2, 1, 1, 3, 3]
def baseStart_288988 : Nat := 118140960795 + 288988 * 2 ^ 59
def prefixEnd_288988 : Nat := 4983230072969 + 3 ^ 40 * 288988 * 2
def baseEnd_288988 : Nat := 87934665115034409967985

theorem tailTrace_288988 : CollatzResearch.WordTrace tailWord_288988 prefixEnd_288988 87934665115034409967985 := by
  unfold tailWord_288988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270129138526653033069809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7026838851368870710759745 5270129138526653033069809)
  ·
    refine ⟨3952596853894989774802357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5270129138526653033069809 3952596853894989774802357)
    ·
      refine ⟨370555955052655291387721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3952596853894989774802357 370555955052655291387721)
      ·
        refine ⟨277916966289491468540791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370555955052655291387721 277916966289491468540791)
        ·
          refine ⟨416875449434237202811187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277916966289491468540791 416875449434237202811187)
          ·
            refine ⟨625313174151355804216781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416875449434237202811187 625313174151355804216781)
            ·
              refine ⟨234492440306758426581293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625313174151355804216781 234492440306758426581293)
              ·
                refine ⟨87934665115034409967985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234492440306758426581293 87934665115034409967985)
                ·
                  rfl

theorem cell19_288988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_288988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_288988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_288988 prefixEnd_288988 := by exact prefixLift 288988
  have htrace : WordTrace (prefixWord ++ tailWord_288988) baseStart_288988 baseEnd_288988 := by
    simpa [prefixWord, tailWord_288988, baseEnd_288988] using wordTrace_append hprefix tailTrace_288988
  have hstable : (prefixWord ++ tailWord_288988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288988).length < 2 ^ (prefixWord ++ tailWord_288988).sum := by decide
  have hdescent : baseEnd_288988 < baseStart_288988 := by decide
  rcases family_descends (prefixWord ++ tailWord_288988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289051 : List Nat := [1, 1, 1, 1, 1, 1, 10, 3]
def baseStart_289051 : Nat := 118140960795 + 289051 * 2 ^ 59
def prefixEnd_289051 : Nat := 4983230072969 + 3 ^ 40 * 289051 * 2
def baseEnd_289051 : Nat := 87953835059468930567813

theorem tailTrace_289051 : CollatzResearch.WordTrace tailWord_289051 prefixEnd_289051 87953835059468930567813 := by
  unfold tailWord_289051
  simp only [CollatzResearch.WordTrace]
  refine ⟨10542556075825067825683007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7028370717216711883788671 10542556075825067825683007)
  ·
    refine ⟨15813834113737601738524511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10542556075825067825683007 15813834113737601738524511)
    ·
      refine ⟨23720751170606402607786767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15813834113737601738524511 23720751170606402607786767)
      ·
        refine ⟨35581126755909603911680151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23720751170606402607786767 35581126755909603911680151)
        ·
          refine ⟨53371690133864405867520227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35581126755909603911680151 53371690133864405867520227)
          ·
            refine ⟨80057535200796608801280341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53371690133864405867520227 80057535200796608801280341)
            ·
              refine ⟨234543560158583814847501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 80057535200796608801280341 234543560158583814847501)
              ·
                refine ⟨87953835059468930567813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234543560158583814847501 87953835059468930567813)
                ·
                  rfl

theorem cell19_289051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_289051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289051 prefixEnd_289051 := by exact prefixLift 289051
  have htrace : WordTrace (prefixWord ++ tailWord_289051) baseStart_289051 baseEnd_289051 := by
    simpa [prefixWord, tailWord_289051, baseEnd_289051] using wordTrace_append hprefix tailTrace_289051
  have hstable : (prefixWord ++ tailWord_289051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289051).length < 2 ^ (prefixWord ++ tailWord_289051).sum := by decide
  have hdescent : baseEnd_289051 < baseStart_289051 := by decide
  rcases family_descends (prefixWord ++ tailWord_289051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289066 : List Nat := [3, 1, 4, 2, 3, 1, 5]
def baseStart_289066 : Nat := 118140960795 + 289066 * 2 ^ 59
def prefixEnd_289066 : Nat := 4983230072969 + 3 ^ 40 * 289066 * 2
def baseEnd_289066 : Nat := 29319466443984446744813

theorem tailTrace_289066 : CollatzResearch.WordTrace tailWord_289066 prefixEnd_289066 29319466443984446744813 := by
  unfold tailWord_289066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635775792692681346869763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7028735447180483591652701 2635775792692681346869763)
  ·
    refine ⟨3953663689039022020304645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635775792692681346869763 3953663689039022020304645)
    ·
      refine ⟨741311941694816628807121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3953663689039022020304645 741311941694816628807121)
      ·
        refine ⟨555983956271112471605341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 741311941694816628807121 555983956271112471605341)
        ·
          refine ⟨208493983601667176852003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 555983956271112471605341 208493983601667176852003)
          ·
            refine ⟨312740975402500765278005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208493983601667176852003 312740975402500765278005)
            ·
              refine ⟨29319466443984446744813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 312740975402500765278005 29319466443984446744813)
              ·
                rfl

theorem cell19_289066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_289066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289066 prefixEnd_289066 := by exact prefixLift 289066
  have htrace : WordTrace (prefixWord ++ tailWord_289066) baseStart_289066 baseEnd_289066 := by
    simpa [prefixWord, tailWord_289066, baseEnd_289066] using wordTrace_append hprefix tailTrace_289066
  have hstable : (prefixWord ++ tailWord_289066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289066).length < 2 ^ (prefixWord ++ tailWord_289066).sum := by decide
  have hdescent : baseEnd_289066 < baseStart_289066 := by decide
  rcases family_descends (prefixWord ++ tailWord_289066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289091 : List Nat := [1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_289091 : Nat := 118140960795 + 289091 * 2 ^ 59
def prefixEnd_289091 : Nat := 4983230072969 + 3 ^ 40 * 289091 * 2
def baseEnd_289091 : Nat := 87966006452760689678815

theorem tailTrace_289091 : CollatzResearch.WordTrace tailWord_289091 prefixEnd_289091 87966006452760689678815 := by
  unfold tailWord_289091
  simp only [CollatzResearch.WordTrace]
  refine ⟨10544014995680154657139127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7029343330453436438092751 10544014995680154657139127)
  ·
    refine ⟨15816022493520231985708691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10544014995680154657139127 15816022493520231985708691)
    ·
      refine ⟨23724033740280347978563037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15816022493520231985708691 23724033740280347978563037)
      ·
        refine ⟨8896512652605130491961139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23724033740280347978563037 8896512652605130491961139)
        ·
          refine ⟨13344768978907695737941709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8896512652605130491961139 13344768978907695737941709)
          ·
            refine ⟨5004288367090385901728141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13344768978907695737941709 5004288367090385901728141)
            ·
              refine ⟨1876608137658894713148053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5004288367090385901728141 1876608137658894713148053)
              ·
                refine ⟨87966006452760689678815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1876608137658894713148053 87966006452760689678815)
                ·
                  rfl

theorem cell19_289091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_289091 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289091 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289091 prefixEnd_289091 := by exact prefixLift 289091
  have htrace : WordTrace (prefixWord ++ tailWord_289091) baseStart_289091 baseEnd_289091 := by
    simpa [prefixWord, tailWord_289091, baseEnd_289091] using wordTrace_append hprefix tailTrace_289091
  have hstable : (prefixWord ++ tailWord_289091).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289091).length < 2 ^ (prefixWord ++ tailWord_289091).sum := by decide
  have hdescent : baseEnd_289091 < baseStart_289091 := by decide
  rcases family_descends (prefixWord ++ tailWord_289091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289108 : List Nat := [2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_289108 : Nat := 118140960795 + 289108 * 2 ^ 59
def prefixEnd_289108 : Nat := 4983230072969 + 3 ^ 40 * 289108 * 2
def baseEnd_289108 : Nat := 87971179294909687300991

theorem tailTrace_289108 : CollatzResearch.WordTrace tailWord_289108 prefixEnd_289108 87971179294909687300991 := by
  unfold tailWord_289108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272317518309283280253989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7029756691079044373671985 5272317518309283280253989)
  ·
    refine ⟨988559534682990615047623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5272317518309283280253989 988559534682990615047623)
    ·
      refine ⟨1482839302024485922571435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988559534682990615047623 1482839302024485922571435)
      ·
        refine ⟨2224258953036728883857153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482839302024485922571435 2224258953036728883857153)
        ·
          refine ⟨1668194214777546662892865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224258953036728883857153 1668194214777546662892865)
          ·
            refine ⟨1251145661083159997169649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1668194214777546662892865 1251145661083159997169649)
            ·
              refine ⟨938359245812369997877237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251145661083159997169649 938359245812369997877237)
              ·
                refine ⟨87971179294909687300991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 938359245812369997877237 87971179294909687300991)
                ·
                  rfl

theorem cell19_289108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_289108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289108 prefixEnd_289108 := by exact prefixLift 289108
  have htrace : WordTrace (prefixWord ++ tailWord_289108) baseStart_289108 baseEnd_289108 := by
    simpa [prefixWord, tailWord_289108, baseEnd_289108] using wordTrace_append hprefix tailTrace_289108
  have hstable : (prefixWord ++ tailWord_289108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289108).length < 2 ^ (prefixWord ++ tailWord_289108).sum := by decide
  have hdescent : baseEnd_289108 < baseStart_289108 := by decide
  rcases family_descends (prefixWord ++ tailWord_289108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289148 : List Nat := [2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_289148 : Nat := 118140960795 + 289148 * 2 ^ 59
def prefixEnd_289148 : Nat := 4983230072969 + 3 ^ 40 * 289148 * 2
def baseEnd_289148 : Nat := 87983350688201446411993

theorem tailTrace_289148 : CollatzResearch.WordTrace tailWord_289148 prefixEnd_289148 87983350688201446411993 := by
  unfold tailWord_289148
  simp only [CollatzResearch.WordTrace]
  refine ⟨5273046978236826695982049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7030729304315768927976065 5273046978236826695982049)
  ·
    refine ⟨3954785233677620021986537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5273046978236826695982049 3954785233677620021986537)
    ·
      refine ⟨2966088925258215016489903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3954785233677620021986537 2966088925258215016489903)
      ·
        refine ⟨4449133387887322524734855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2966088925258215016489903 4449133387887322524734855)
        ·
          refine ⟨6673700081830983787102283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4449133387887322524734855 6673700081830983787102283)
          ·
            refine ⟨10010550122746475680653425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6673700081830983787102283 10010550122746475680653425)
            ·
              refine ⟨7507912592059856760490069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10010550122746475680653425 7507912592059856760490069)
              ·
                refine ⟨87983350688201446411993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7507912592059856760490069 87983350688201446411993)
                ·
                  rfl

theorem cell19_289148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_289148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289148 prefixEnd_289148 := by exact prefixLift 289148
  have htrace : WordTrace (prefixWord ++ tailWord_289148) baseStart_289148 baseEnd_289148 := by
    simpa [prefixWord, tailWord_289148, baseEnd_289148] using wordTrace_append hprefix tailTrace_289148
  have hstable : (prefixWord ++ tailWord_289148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289148).length < 2 ^ (prefixWord ++ tailWord_289148).sum := by decide
  have hdescent : baseEnd_289148 < baseStart_289148 := by decide
  rcases family_descends (prefixWord ++ tailWord_289148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289182 : List Nat := [4, 3, 1, 2, 1, 2, 6]
def baseStart_289182 : Nat := 118140960795 + 289182 * 2 ^ 59
def prefixEnd_289182 : Nat := 4983230072969 + 3 ^ 40 * 289182 * 2
def baseEnd_289182 : Nat := 29331232124166480552115

theorem tailTrace_289182 : CollatzResearch.WordTrace tailWord_289182 prefixEnd_289182 29331232124166480552115 := by
  unfold tailWord_289182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318416754793809649837725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7031556025566984799134533 1318416754793809649837725)
  ·
    refine ⟨494406283047678618689147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1318416754793809649837725 494406283047678618689147)
    ·
      refine ⟨741609424571517928033721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494406283047678618689147 741609424571517928033721)
      ·
        refine ⟨556207068428638446025291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 741609424571517928033721 556207068428638446025291)
        ·
          refine ⟨834310602642957669037937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556207068428638446025291 834310602642957669037937)
          ·
            refine ⟨625732951982218251778453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834310602642957669037937 625732951982218251778453)
            ·
              refine ⟨29331232124166480552115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 625732951982218251778453 29331232124166480552115)
              ·
                rfl

theorem cell19_289182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_289182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289182 prefixEnd_289182 := by exact prefixLift 289182
  have htrace : WordTrace (prefixWord ++ tailWord_289182) baseStart_289182 baseEnd_289182 := by
    simpa [prefixWord, tailWord_289182, baseEnd_289182] using wordTrace_append hprefix tailTrace_289182
  have hstable : (prefixWord ++ tailWord_289182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289182).length < 2 ^ (prefixWord ++ tailWord_289182).sum := by decide
  have hdescent : baseEnd_289182 < baseStart_289182 := by decide
  rcases family_descends (prefixWord ++ tailWord_289182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289220 : List Nat := [2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_289220 : Nat := 118140960795 + 289220 * 2 ^ 59
def prefixEnd_289220 : Nat := 4983230072969 + 3 ^ 40 * 289220 * 2
def baseEnd_289220 : Nat := 88005259196126612811797

theorem tailTrace_289220 : CollatzResearch.WordTrace tailWord_289220 prefixEnd_289220 88005259196126612811797 := by
  unfold tailWord_289220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5274360006106404844292557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7032480008141873125723409 5274360006106404844292557)
  ·
    refine ⟨1977885002289901816609709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5274360006106404844292557 1977885002289901816609709)
    ·
      refine ⟨741706875858713181228641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1977885002289901816609709 741706875858713181228641)
      ·
        refine ⟨556280156894034885921481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 741706875858713181228641 556280156894034885921481)
        ·
          refine ⟨417210117670526164441111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 556280156894034885921481 417210117670526164441111)
          ·
            refine ⟨625815176505789246661667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417210117670526164441111 625815176505789246661667)
            ·
              refine ⟨938722764758683869992501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625815176505789246661667 938722764758683869992501)
              ·
                refine ⟨88005259196126612811797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 938722764758683869992501 88005259196126612811797)
                ·
                  rfl

theorem cell19_289220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_289220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289220 prefixEnd_289220 := by exact prefixLift 289220
  have htrace : WordTrace (prefixWord ++ tailWord_289220) baseStart_289220 baseEnd_289220 := by
    simpa [prefixWord, tailWord_289220, baseEnd_289220] using wordTrace_append hprefix tailTrace_289220
  have hstable : (prefixWord ++ tailWord_289220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289220).length < 2 ^ (prefixWord ++ tailWord_289220).sum := by decide
  have hdescent : baseEnd_289220 < baseStart_289220 := by decide
  rcases family_descends (prefixWord ++ tailWord_289220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289336 : List Nat := [2, 1, 2, 1, 4, 1, 5, 3]
def baseStart_289336 : Nat := 118140960795 + 289336 * 2 ^ 59
def prefixEnd_289336 : Nat := 4983230072969 + 3 ^ 40 * 289336 * 2
def baseEnd_289336 : Nat := 88040556236672714233703

theorem tailTrace_289336 : CollatzResearch.WordTrace tailWord_289336 prefixEnd_289336 88040556236672714233703 := by
  unfold tailWord_289336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5276475439896280749903931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7035300586528374333205241 5276475439896280749903931)
  ·
    refine ⟨7914713159844421124855897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5276475439896280749903931 7914713159844421124855897)
    ·
      refine ⟨5936034869883315843641923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7914713159844421124855897 5936034869883315843641923)
      ·
        refine ⟨8904052304824973765462885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5936034869883315843641923 8904052304824973765462885)
        ·
          refine ⟨1669509807154682581024291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8904052304824973765462885 1669509807154682581024291)
          ·
            refine ⟨2504264710732023871536437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669509807154682581024291 2504264710732023871536437)
            ·
              refine ⟨234774816631127237956541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2504264710732023871536437 234774816631127237956541)
              ·
                refine ⟨88040556236672714233703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234774816631127237956541 88040556236672714233703)
                ·
                  rfl

theorem cell19_289336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_289336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289336 prefixEnd_289336 := by exact prefixLift 289336
  have htrace : WordTrace (prefixWord ++ tailWord_289336) baseStart_289336 baseEnd_289336 := by
    simpa [prefixWord, tailWord_289336, baseEnd_289336] using wordTrace_append hprefix tailTrace_289336
  have hstable : (prefixWord ++ tailWord_289336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289336).length < 2 ^ (prefixWord ++ tailWord_289336).sum := by decide
  have hdescent : baseEnd_289336 < baseStart_289336 := by decide
  rcases family_descends (prefixWord ++ tailWord_289336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289412 : List Nat := [2, 3, 2, 1, 3, 3, 5]
def baseStart_289412 : Nat := 118140960795 + 289412 * 2 ^ 59
def prefixEnd_289412 : Nat := 4983230072969 + 3 ^ 40 * 289412 * 2
def baseEnd_289412 : Nat := 29354560627975685514869

theorem tailTrace_289412 : CollatzResearch.WordTrace tailWord_289412 prefixEnd_289412 29354560627975685514869 := by
  unfold tailWord_289412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277861413758613239787245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7037148551678150986382993 5277861413758613239787245)
  ·
    refine ⟨1979198030159479964920217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5277861413758613239787245 1979198030159479964920217)
    ·
      refine ⟨1484398522619609973690163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1979198030159479964920217 1484398522619609973690163)
      ·
        refine ⟨2226597783929414960535245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484398522619609973690163 2226597783929414960535245)
        ·
          refine ⟨834974168973530610200717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2226597783929414960535245 834974168973530610200717)
          ·
            refine ⟨313115313365073978825269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 834974168973530610200717 313115313365073978825269)
            ·
              refine ⟨29354560627975685514869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 313115313365073978825269 29354560627975685514869)
              ·
                rfl

theorem cell19_289412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_289412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289412 prefixEnd_289412 := by exact prefixLift 289412
  have htrace : WordTrace (prefixWord ++ tailWord_289412) baseStart_289412 baseEnd_289412 := by
    simpa [prefixWord, tailWord_289412, baseEnd_289412] using wordTrace_append hprefix tailTrace_289412
  have hstable : (prefixWord ++ tailWord_289412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289412).length < 2 ^ (prefixWord ++ tailWord_289412).sum := by decide
  have hdescent : baseEnd_289412 < baseStart_289412 := by decide
  rcases family_descends (prefixWord ++ tailWord_289412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289433 : List Nat := [1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_289433 : Nat := 118140960795 + 289433 * 2 ^ 59
def prefixEnd_289433 : Nat := 4983230072969 + 3 ^ 40 * 289433 * 2
def baseEnd_289433 : Nat := 88070071865405230077883

theorem tailTrace_289433 : CollatzResearch.WordTrace tailWord_289433 prefixEnd_289433 88070071865405230077883 := by
  unfold tailWord_289433
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556488760441147066088953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7037659173627431377392635 10556488760441147066088953)
  ·
    refine ⟨7917366570330860299566715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10556488760441147066088953 7917366570330860299566715)
    ·
      refine ⟨11876049855496290449350073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7917366570330860299566715 11876049855496290449350073)
      ·
        refine ⟨8907037391622217837012555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11876049855496290449350073 8907037391622217837012555)
        ·
          refine ⟨13360556087433326755518833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8907037391622217837012555 13360556087433326755518833)
          ·
            refine ⟨10020417065574995066639125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13360556087433326755518833 10020417065574995066639125)
            ·
              refine ⟨469707049948827893748709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10020417065574995066639125 469707049948827893748709)
              ·
                refine ⟨88070071865405230077883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469707049948827893748709 88070071865405230077883)
                ·
                  rfl

theorem cell19_289433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_289433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289433 prefixEnd_289433 := by exact prefixLift 289433
  have htrace : WordTrace (prefixWord ++ tailWord_289433) baseStart_289433 baseEnd_289433 := by
    simpa [prefixWord, tailWord_289433, baseEnd_289433] using wordTrace_append hprefix tailTrace_289433
  have hstable : (prefixWord ++ tailWord_289433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289433).length < 2 ^ (prefixWord ++ tailWord_289433).sum := by decide
  have hdescent : baseEnd_289433 < baseStart_289433 := by decide
  rcases family_descends (prefixWord ++ tailWord_289433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289564 : List Nat := [2, 2, 3, 1, 1, 3, 4, 3]
def baseStart_289564 : Nat := 118140960795 + 289564 * 2 ^ 59
def prefixEnd_289564 : Nat := 4983230072969 + 3 ^ 40 * 289564 * 2
def baseEnd_289564 : Nat := 88109933178435741166415

theorem tailTrace_289564 : CollatzResearch.WordTrace tailWord_289564 prefixEnd_289564 88109933178435741166415 := by
  unfold tailWord_289564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280633361483278219553873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7040844481977704292738497 5280633361483278219553873)
  ·
    refine ⟨3960475021112458664665405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5280633361483278219553873 3960475021112458664665405)
    ·
      refine ⟨1485178132917171999249527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3960475021112458664665405 1485178132917171999249527)
      ·
        refine ⟨2227767199375757998874291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485178132917171999249527 2227767199375757998874291)
        ·
          refine ⟨3341650799063636998311437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227767199375757998874291 3341650799063636998311437)
          ·
            refine ⟨1253119049648863874366789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3341650799063636998311437 1253119049648863874366789)
            ·
              refine ⟨234959821809161976443773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1253119049648863874366789 234959821809161976443773)
              ·
                refine ⟨88109933178435741166415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234959821809161976443773 88109933178435741166415)
                ·
                  rfl

theorem cell19_289564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_289564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289564 prefixEnd_289564 := by exact prefixLift 289564
  have htrace : WordTrace (prefixWord ++ tailWord_289564) baseStart_289564 baseEnd_289564 := by
    simpa [prefixWord, tailWord_289564, baseEnd_289564] using wordTrace_append hprefix tailTrace_289564
  have hstable : (prefixWord ++ tailWord_289564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289564).length < 2 ^ (prefixWord ++ tailWord_289564).sum := by decide
  have hdescent : baseEnd_289564 < baseStart_289564 := by decide
  rcases family_descends (prefixWord ++ tailWord_289564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289623 : List Nat := [1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_289623 : Nat := 118140960795 + 289623 * 2 ^ 59
def prefixEnd_289623 : Nat := 4983230072969 + 3 ^ 40 * 289623 * 2
def baseEnd_289623 : Nat := 88127885983541085855143

theorem tailTrace_289623 : CollatzResearch.WordTrace tailWord_289623 prefixEnd_289623 88127885983541085855143 := by
  unfold tailWord_289623
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563418629752809515505523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7042279086501873010337015 10563418629752809515505523)
  ·
    refine ⟨15845127944629214273258285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10563418629752809515505523 15845127944629214273258285)
    ·
      refine ⟨5941922979235955352471857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15845127944629214273258285 5941922979235955352471857)
      ·
        refine ⟨4456442234426966514353893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5941922979235955352471857 4456442234426966514353893)
        ·
          refine ⟨835582918955056221441355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4456442234426966514353893 835582918955056221441355)
          ·
            refine ⟨1253374378432584332162033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835582918955056221441355 1253374378432584332162033)
            ·
              refine ⟨940030783824438249121525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253374378432584332162033 940030783824438249121525)
              ·
                refine ⟨88127885983541085855143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 940030783824438249121525 88127885983541085855143)
                ·
                  rfl

theorem cell19_289623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_289623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289623 prefixEnd_289623 := by exact prefixLift 289623
  have htrace : WordTrace (prefixWord ++ tailWord_289623) baseStart_289623 baseEnd_289623 := by
    simpa [prefixWord, tailWord_289623, baseEnd_289623] using wordTrace_append hprefix tailTrace_289623
  have hstable : (prefixWord ++ tailWord_289623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289623).length < 2 ^ (prefixWord ++ tailWord_289623).sum := by decide
  have hdescent : baseEnd_289623 < baseStart_289623 := by decide
  rcases family_descends (prefixWord ++ tailWord_289623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289661 : List Nat := [1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_289661 : Nat := 118140960795 + 289661 * 2 ^ 59
def prefixEnd_289661 : Nat := 4983230072969 + 3 ^ 40 * 289661 * 2
def baseEnd_289661 : Nat := 88139448807168257010595

theorem tailTrace_289661 : CollatzResearch.WordTrace tailWord_289661 prefixEnd_289661 88139448807168257010595 := by
  unfold tailWord_289661
  simp only [CollatzResearch.WordTrace]
  refine ⟨10564804603615142005388837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7043203069076761336925891 10564804603615142005388837)
  ·
    refine ⟨1980900863177839126010407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10564804603615142005388837 1980900863177839126010407)
    ·
      refine ⟨2971351294766758689015611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980900863177839126010407 2971351294766758689015611)
      ·
        refine ⟨4457026942150138033523417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971351294766758689015611 4457026942150138033523417)
        ·
          refine ⟨3342770206612603525142563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4457026942150138033523417 3342770206612603525142563)
          ·
            refine ⟨5014155309918905287713845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3342770206612603525142563 5014155309918905287713845)
            ·
              refine ⟨470077060304897370723173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5014155309918905287713845 470077060304897370723173)
              ·
                refine ⟨88139448807168257010595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470077060304897370723173 88139448807168257010595)
                ·
                  rfl

theorem cell19_289661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_289661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289661 prefixEnd_289661 := by exact prefixLift 289661
  have htrace : WordTrace (prefixWord ++ tailWord_289661) baseStart_289661 baseEnd_289661 := by
    simpa [prefixWord, tailWord_289661, baseEnd_289661] using wordTrace_append hprefix tailTrace_289661
  have hstable : (prefixWord ++ tailWord_289661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289661).length < 2 ^ (prefixWord ++ tailWord_289661).sum := by decide
  have hdescent : baseEnd_289661 < baseStart_289661 := by decide
  rcases family_descends (prefixWord ++ tailWord_289661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289775 : List Nat := [1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_289775 : Nat := 118140960795 + 289775 * 2 ^ 59
def prefixEnd_289775 : Nat := 4983230072969 + 3 ^ 40 * 289775 * 2
def baseEnd_289775 : Nat := 88174137278049770476951

theorem tailTrace_289775 : CollatzResearch.WordTrace tailWord_289775 prefixEnd_289775 88174137278049770476951 := by
  unfold tailWord_289775
  simp only [CollatzResearch.WordTrace]
  refine ⟨10568962525202139475038779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7045975016801426316692519 10568962525202139475038779)
  ·
    refine ⟨15853443787803209212558169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10568962525202139475038779 15853443787803209212558169)
    ·
      refine ⟨11890082840852406909418627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15853443787803209212558169 11890082840852406909418627)
      ·
        refine ⟨17835124261278610364127941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11890082840852406909418627 17835124261278610364127941)
        ·
          refine ⟨3344085798989739443273989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17835124261278610364127941 3344085798989739443273989)
          ·
            refine ⟨627016087310576145613873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3344085798989739443273989 627016087310576145613873)
            ·
              refine ⟨470262065482932109210405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627016087310576145613873 470262065482932109210405)
              ·
                refine ⟨88174137278049770476951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470262065482932109210405 88174137278049770476951)
                ·
                  rfl

theorem cell19_289775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_289775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289775 prefixEnd_289775 := by exact prefixLift 289775
  have htrace : WordTrace (prefixWord ++ tailWord_289775) baseStart_289775 baseEnd_289775 := by
    simpa [prefixWord, tailWord_289775, baseEnd_289775] using wordTrace_append hprefix tailTrace_289775
  have hstable : (prefixWord ++ tailWord_289775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289775).length < 2 ^ (prefixWord ++ tailWord_289775).sum := by decide
  have hdescent : baseEnd_289775 < baseStart_289775 := by decide
  rcases family_descends (prefixWord ++ tailWord_289775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289849 : List Nat := [1, 2, 1, 5, 2, 2, 3, 3]
def baseStart_289849 : Nat := 118140960795 + 289849 * 2 ^ 59
def prefixEnd_289849 : Nat := 4983230072969 + 3 ^ 40 * 289849 * 2
def baseEnd_289849 : Nat := 88196654355639524832305

theorem tailTrace_289849 : CollatzResearch.WordTrace tailWord_289849 prefixEnd_289849 88196654355639524832305 := by
  unfold tailWord_289849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10571661526934050113232601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7047774351289366742155067 10571661526934050113232601)
  ·
    refine ⟨7928746145200537584924451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10571661526934050113232601 7928746145200537584924451)
    ·
      refine ⟨11893119217800806377386677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7928746145200537584924451 11893119217800806377386677)
      ·
        refine ⟨1114979926668825597880001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11893119217800806377386677 1114979926668825597880001)
        ·
          refine ⟨836234945001619198410001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114979926668825597880001 836234945001619198410001)
          ·
            refine ⟨627176208751214398807501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836234945001619198410001 627176208751214398807501)
            ·
              refine ⟨235191078281705399552813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 627176208751214398807501 235191078281705399552813)
              ·
                refine ⟨88196654355639524832305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235191078281705399552813 88196654355639524832305)
                ·
                  rfl

theorem cell19_289849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_289849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289849 prefixEnd_289849 := by exact prefixLift 289849
  have htrace : WordTrace (prefixWord ++ tailWord_289849) baseStart_289849 baseEnd_289849 := by
    simpa [prefixWord, tailWord_289849, baseEnd_289849] using wordTrace_append hprefix tailTrace_289849
  have hstable : (prefixWord ++ tailWord_289849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289849).length < 2 ^ (prefixWord ++ tailWord_289849).sum := by decide
  have hdescent : baseEnd_289849 < baseStart_289849 := by decide
  rcases family_descends (prefixWord ++ tailWord_289849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289891 : List Nat := [1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_289891 : Nat := 118140960795 + 289891 * 2 ^ 59
def prefixEnd_289891 : Nat := 4983230072969 + 3 ^ 40 * 289891 * 2
def baseEnd_289891 : Nat := 88209434318595871898857

theorem tailTrace_289891 : CollatzResearch.WordTrace tailWord_289891 prefixEnd_289891 88209434318595871898857 := by
  unfold tailWord_289891
  simp only [CollatzResearch.WordTrace]
  refine ⟨10573193392781891286261527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7048795595187927524174351 10573193392781891286261527)
  ·
    refine ⟨15859790089172836929392291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10573193392781891286261527 15859790089172836929392291)
    ·
      refine ⟨23789685133759255394088437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15859790089172836929392291 23789685133759255394088437)
      ·
        refine ⟨2230282981289930193195791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23789685133759255394088437 2230282981289930193195791)
        ·
          refine ⟨3345424471934895289793687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2230282981289930193195791 3345424471934895289793687)
          ·
            refine ⟨5018136707902342934690531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345424471934895289793687 5018136707902342934690531)
            ·
              refine ⟨7527205061853514402035797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5018136707902342934690531 7527205061853514402035797)
              ·
                refine ⟨88209434318595871898857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7527205061853514402035797 88209434318595871898857)
                ·
                  rfl

theorem cell19_289891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_289891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289891 prefixEnd_289891 := by exact prefixLift 289891
  have htrace : WordTrace (prefixWord ++ tailWord_289891) baseStart_289891 baseEnd_289891 := by
    simpa [prefixWord, tailWord_289891, baseEnd_289891] using wordTrace_append hprefix tailTrace_289891
  have hstable : (prefixWord ++ tailWord_289891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289891).length < 2 ^ (prefixWord ++ tailWord_289891).sum := by decide
  have hdescent : baseEnd_289891 < baseStart_289891 := by decide
  rcases family_descends (prefixWord ++ tailWord_289891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289925 : List Nat := [1, 3, 1, 1, 7, 1, 5]
def baseStart_289925 : Nat := 118140960795 + 289925 * 2 ^ 59
def prefixEnd_289925 : Nat := 4983230072969 + 3 ^ 40 * 289925 * 2
def baseEnd_289925 : Nat := 29406593334297955714403

theorem tailTrace_289925 : CollatzResearch.WordTrace tailWord_289925 prefixEnd_289925 29406593334297955714403 := by
  unfold tailWord_289925
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574433474658715092999229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7049622316439143395332819 10574433474658715092999229)
  ·
    refine ⟨3965412552997018159874711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10574433474658715092999229 3965412552997018159874711)
    ·
      refine ⟨5948118829495527239812067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3965412552997018159874711 5948118829495527239812067)
      ·
        refine ⟨8922178244243290859718101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5948118829495527239812067 8922178244243290859718101)
        ·
          refine ⟨209113552599452129524643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8922178244243290859718101 209113552599452129524643)
          ·
            refine ⟨313670328899178194286965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209113552599452129524643 313670328899178194286965)
            ·
              refine ⟨29406593334297955714403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 313670328899178194286965 29406593334297955714403)
              ·
                rfl

theorem cell19_289925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_289925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289925 prefixEnd_289925 := by exact prefixLift 289925
  have htrace : WordTrace (prefixWord ++ tailWord_289925) baseStart_289925 baseEnd_289925 := by
    simpa [prefixWord, tailWord_289925, baseEnd_289925] using wordTrace_append hprefix tailTrace_289925
  have hstable : (prefixWord ++ tailWord_289925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289925).length < 2 ^ (prefixWord ++ tailWord_289925).sum := by decide
  have hdescent : baseEnd_289925 < baseStart_289925 := by decide
  rcases family_descends (prefixWord ++ tailWord_289925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289929 : List Nat := [1, 2, 1, 1, 4, 3, 7]
def baseStart_289929 : Nat := 118140960795 + 289929 * 2 ^ 59
def prefixEnd_289929 : Nat := 4983230072969 + 3 ^ 40 * 289929 * 2
def baseEnd_289929 : Nat := 29406999047407681018103

theorem tailTrace_289929 : CollatzResearch.WordTrace tailWord_289929 prefixEnd_289929 29406999047407681018103 := by
  unfold tailWord_289929
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574579366644223776144841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7049719577762815850763227 10574579366644223776144841)
  ·
    refine ⟨7930934524983167832108631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10574579366644223776144841 7930934524983167832108631)
    ·
      refine ⟨11896401787474751748162947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7930934524983167832108631 11896401787474751748162947)
      ·
        refine ⟨17844602681212127622244421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11896401787474751748162947 17844602681212127622244421)
        ·
          refine ⟨3345863002727273929170829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17844602681212127622244421 3345863002727273929170829)
          ·
            refine ⟨1254698626022727723439061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3345863002727273929170829 1254698626022727723439061)
            ·
              refine ⟨29406999047407681018103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1254698626022727723439061 29406999047407681018103)
              ·
                rfl

theorem cell19_289929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_289929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289929 prefixEnd_289929 := by exact prefixLift 289929
  have htrace : WordTrace (prefixWord ++ tailWord_289929) baseStart_289929 baseEnd_289929 := by
    simpa [prefixWord, tailWord_289929, baseEnd_289929] using wordTrace_append hprefix tailTrace_289929
  have hstable : (prefixWord ++ tailWord_289929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289929).length < 2 ^ (prefixWord ++ tailWord_289929).sum := by decide
  have hdescent : baseEnd_289929 < baseStart_289929 := by decide
  rcases family_descends (prefixWord ++ tailWord_289929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289946 : List Nat := [3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_289946 : Nat := 118140960795 + 289946 * 2 ^ 59
def prefixEnd_289946 : Nat := 4983230072969 + 3 ^ 40 * 289946 * 2
def baseEnd_289946 : Nat := 88226169984372040676485

theorem tailTrace_289946 : CollatzResearch.WordTrace tailWord_289946 prefixEnd_289946 88226169984372040676485 := by
  unfold tailWord_289946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643799851895658919878423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7050132938388423786342461 2643799851895658919878423)
  ·
    refine ⟨3965699777843488379817635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2643799851895658919878423 3965699777843488379817635)
    ·
      refine ⟨5948549666765232569726453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3965699777843488379817635 5948549666765232569726453)
      ·
        refine ⟨557676531259240553411855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5948549666765232569726453 557676531259240553411855)
        ·
          refine ⟨836514796888860830117783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557676531259240553411855 836514796888860830117783)
          ·
            refine ⟨1254772195333291245176675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836514796888860830117783 1254772195333291245176675)
            ·
              refine ⟨1882158292999936867765013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254772195333291245176675 1882158292999936867765013)
              ·
                refine ⟨88226169984372040676485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1882158292999936867765013 88226169984372040676485)
                ·
                  rfl

theorem cell19_289946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_289946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289946 prefixEnd_289946 := by exact prefixLift 289946
  have htrace : WordTrace (prefixWord ++ tailWord_289946) baseStart_289946 baseEnd_289946 := by
    simpa [prefixWord, tailWord_289946, baseEnd_289946] using wordTrace_append hprefix tailTrace_289946
  have hstable : (prefixWord ++ tailWord_289946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289946).length < 2 ^ (prefixWord ++ tailWord_289946).sum := by decide
  have hdescent : baseEnd_289946 < baseStart_289946 := by decide
  rcases family_descends (prefixWord ++ tailWord_289946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289967 : List Nat := [1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_289967 : Nat := 118140960795 + 289967 * 2 ^ 59
def prefixEnd_289967 : Nat := 4983230072969 + 3 ^ 40 * 289967 * 2
def baseEnd_289967 : Nat := 88232559965850214209761

theorem tailTrace_289967 : CollatzResearch.WordTrace tailWord_289967 prefixEnd_289967 88232559965850214209761 := by
  unfold tailWord_289967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10575965340506556266028155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7050643560337704177352103 10575965340506556266028155)
  ·
    refine ⟨15863948010759834399042233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10575965340506556266028155 15863948010759834399042233)
    ·
      refine ⟨11897961008069875799281675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15863948010759834399042233 11897961008069875799281675)
      ·
        refine ⟨17846941512104813698922513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11897961008069875799281675 17846941512104813698922513)
        ·
          refine ⟨13385206134078610274191885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17846941512104813698922513 13385206134078610274191885)
          ·
            refine ⟨5019452300279478852821957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13385206134078610274191885 5019452300279478852821957)
            ·
              refine ⟨941147306302402284904117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5019452300279478852821957 941147306302402284904117)
              ·
                refine ⟨88232559965850214209761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 941147306302402284904117 88232559965850214209761)
                ·
                  rfl

theorem cell19_289967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_289967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289967 prefixEnd_289967 := by exact prefixLift 289967
  have htrace : WordTrace (prefixWord ++ tailWord_289967) baseStart_289967 baseEnd_289967 := by
    simpa [prefixWord, tailWord_289967, baseEnd_289967] using wordTrace_append hprefix tailTrace_289967
  have hstable : (prefixWord ++ tailWord_289967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289967).length < 2 ^ (prefixWord ++ tailWord_289967).sum := by decide
  have hdescent : baseEnd_289967 < baseStart_289967 := by decide
  rcases family_descends (prefixWord ++ tailWord_289967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289984 : List Nat := [2, 1, 1, 2, 7, 6]
def baseStart_289984 : Nat := 118140960795 + 289984 * 2 ^ 59
def prefixEnd_289984 : Nat := 4983230072969 + 3 ^ 40 * 289984 * 2
def baseEnd_289984 : Nat := 9804192534222134647993

theorem tailTrace_289984 : CollatzResearch.WordTrace tailWord_289984 prefixEnd_289984 9804192534222134647993 := by
  unfold tailWord_289984
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288292690722484084698503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7051056920963312112931337 5288292690722484084698503)
  ·
    refine ⟨7932439036083726127047755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5288292690722484084698503 7932439036083726127047755)
    ·
      refine ⟨11898658554125589190571633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7932439036083726127047755 11898658554125589190571633)
      ·
        refine ⟨8923993915594191892928725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11898658554125589190571633 8923993915594191892928725)
        ·
          refine ⟨209156107396738872490517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8923993915594191892928725 209156107396738872490517)
          ·
            refine ⟨9804192534222134647993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 209156107396738872490517 9804192534222134647993)
            ·
              rfl

theorem cell19_289984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 6].length) (baseStart_289984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289984 prefixEnd_289984 := by exact prefixLift 289984
  have htrace : WordTrace (prefixWord ++ tailWord_289984) baseStart_289984 baseEnd_289984 := by
    simpa [prefixWord, tailWord_289984, baseEnd_289984] using wordTrace_append hprefix tailTrace_289984
  have hstable : (prefixWord ++ tailWord_289984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289984).length < 2 ^ (prefixWord ++ tailWord_289984).sum := by decide
  have hdescent : baseEnd_289984 < baseStart_289984 := by decide
  rcases family_descends (prefixWord ++ tailWord_289984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289997 : List Nat := [1, 6, 2, 2, 1, 2, 1, 4]
def baseStart_289997 : Nat := 118140960795 + 289997 * 2 ^ 59
def prefixEnd_289997 : Nat := 4983230072969 + 3 ^ 40 * 289997 * 2
def baseEnd_289997 : Nat := 88241688510819033543013

theorem tailTrace_289997 : CollatzResearch.WordTrace tailWord_289997 prefixEnd_289997 88241688510819033543013 := by
  unfold tailWord_289997
  simp only [CollatzResearch.WordTrace]
  refine ⟨10577059530397871389620245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7051373020265247593080163 10577059530397871389620245)
  ·
    refine ⟨495799665487400221388449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10577059530397871389620245 495799665487400221388449)
    ·
      refine ⟨371849749115550166041337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 495799665487400221388449 371849749115550166041337)
      ·
        refine ⟨278887311836662624531003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371849749115550166041337 278887311836662624531003)
        ·
          refine ⟨418330967754993936796505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278887311836662624531003 418330967754993936796505)
          ·
            refine ⟨313748225816245452597379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418330967754993936796505 313748225816245452597379)
            ·
              refine ⟨470622338724368178896069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313748225816245452597379 470622338724368178896069)
              ·
                refine ⟨88241688510819033543013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470622338724368178896069 88241688510819033543013)
                ·
                  rfl

theorem cell19_289997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_289997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_289997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_289997 prefixEnd_289997 := by exact prefixLift 289997
  have htrace : WordTrace (prefixWord ++ tailWord_289997) baseStart_289997 baseEnd_289997 := by
    simpa [prefixWord, tailWord_289997, baseEnd_289997] using wordTrace_append hprefix tailTrace_289997
  have hstable : (prefixWord ++ tailWord_289997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289997).length < 2 ^ (prefixWord ++ tailWord_289997).sum := by decide
  have hdescent : baseEnd_289997 < baseStart_289997 := by decide
  rcases family_descends (prefixWord ++ tailWord_289997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290077 : List Nat := [1, 4, 2, 3, 1, 1, 4, 3]
def baseStart_290077 : Nat := 118140960795 + 290077 * 2 ^ 59
def prefixEnd_290077 : Nat := 4983230072969 + 3 ^ 40 * 290077 * 2
def baseEnd_290077 : Nat := 88266031297402551765017

theorem tailTrace_290077 : CollatzResearch.WordTrace tailWord_290077 prefixEnd_290077 88266031297402551765017 := by
  unfold tailWord_290077
  simp only [CollatzResearch.WordTrace]
  refine ⟨10579977370108045052532485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7053318246738696701688323 10579977370108045052532485)
  ·
    refine ⟨1983745756895258447349841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10579977370108045052532485 1983745756895258447349841)
    ·
      refine ⟨1487809317671443835512381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1983745756895258447349841 1487809317671443835512381)
      ·
        refine ⟨557928494126791438317143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1487809317671443835512381 557928494126791438317143)
        ·
          refine ⟨836892741190187157475715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557928494126791438317143 836892741190187157475715)
          ·
            refine ⟨1255339111785280736213573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836892741190187157475715 1255339111785280736213573)
            ·
              refine ⟨235376083459740138040045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1255339111785280736213573 235376083459740138040045)
              ·
                refine ⟨88266031297402551765017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235376083459740138040045 88266031297402551765017)
                ·
                  rfl

theorem cell19_290077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_290077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290077 prefixEnd_290077 := by exact prefixLift 290077
  have htrace : WordTrace (prefixWord ++ tailWord_290077) baseStart_290077 baseEnd_290077 := by
    simpa [prefixWord, tailWord_290077, baseEnd_290077] using wordTrace_append hprefix tailTrace_290077
  have hstable : (prefixWord ++ tailWord_290077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290077).length < 2 ^ (prefixWord ++ tailWord_290077).sum := by decide
  have hdescent : baseEnd_290077 < baseStart_290077 := by decide
  rcases family_descends (prefixWord ++ tailWord_290077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290079 : List Nat := [1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_290079 : Nat := 118140960795 + 290079 * 2 ^ 59
def prefixEnd_290079 : Nat := 4983230072969 + 3 ^ 40 * 290079 * 2
def baseEnd_290079 : Nat := 88266639867067139720567

theorem tailTrace_290079 : CollatzResearch.WordTrace tailWord_290079 prefixEnd_290079 88266639867067139720567 := by
  unfold tailWord_290079
  simp only [CollatzResearch.WordTrace]
  refine ⟨10580050316100799394105291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7053366877400532929403527 10580050316100799394105291)
  ·
    refine ⟨15870075474151199091157937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10580050316100799394105291 15870075474151199091157937)
    ·
      refine ⟨11902556605613399318368453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15870075474151199091157937 11902556605613399318368453)
      ·
        refine ⟨2231729363552512372194085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11902556605613399318368453 2231729363552512372194085)
        ·
          refine ⟨418449255666096069786391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2231729363552512372194085 418449255666096069786391)
          ·
            refine ⟨627673883499144104679587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418449255666096069786391 627673883499144104679587)
            ·
              refine ⟨941510825248716157019381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627673883499144104679587 941510825248716157019381)
              ·
                refine ⟨88266639867067139720567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 941510825248716157019381 88266639867067139720567)
                ·
                  rfl

theorem cell19_290079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_290079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290079 prefixEnd_290079 := by exact prefixLift 290079
  have htrace : WordTrace (prefixWord ++ tailWord_290079) baseStart_290079 baseEnd_290079 := by
    simpa [prefixWord, tailWord_290079, baseEnd_290079] using wordTrace_append hprefix tailTrace_290079
  have hstable : (prefixWord ++ tailWord_290079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290079).length < 2 ^ (prefixWord ++ tailWord_290079).sum := by decide
  have hdescent : baseEnd_290079 < baseStart_290079 := by decide
  rcases family_descends (prefixWord ++ tailWord_290079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290098 : List Nat := [3, 2, 1, 1, 4, 3, 5]
def baseStart_290098 : Nat := 118140960795 + 290098 * 2 ^ 59
def prefixEnd_290098 : Nat := 4983230072969 + 3 ^ 40 * 290098 * 2
def baseEnd_290098 : Nat := 29424140426293575099431

theorem tailTrace_290098 : CollatzResearch.WordTrace tailWord_290098 prefixEnd_290098 29424140426293575099431 := by
  unfold tailWord_290098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645185825757991409761737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7053828868687977092697965 2645185825757991409761737)
  ·
    refine ⟨1983889369318493557321303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2645185825757991409761737 1983889369318493557321303)
    ·
      refine ⟨2975834053977740335981955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983889369318493557321303 2975834053977740335981955)
      ·
        refine ⟨4463751080966610503972933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975834053977740335981955 4463751080966610503972933)
        ·
          refine ⟨836953327681239469494925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4463751080966610503972933 836953327681239469494925)
          ·
            refine ⟨313857497880464801060597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 836953327681239469494925 313857497880464801060597)
            ·
              refine ⟨29424140426293575099431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 313857497880464801060597 29424140426293575099431)
              ·
                rfl

theorem cell19_290098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_290098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290098 prefixEnd_290098 := by exact prefixLift 290098
  have htrace : WordTrace (prefixWord ++ tailWord_290098) baseStart_290098 baseEnd_290098 := by
    simpa [prefixWord, tailWord_290098, baseEnd_290098] using wordTrace_append hprefix tailTrace_290098
  have hstable : (prefixWord ++ tailWord_290098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290098).length < 2 ^ (prefixWord ++ tailWord_290098).sum := by decide
  have hdescent : baseEnd_290098 < baseStart_290098 := by decide
  rcases family_descends (prefixWord ++ tailWord_290098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290119 : List Nat := [1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_290119 : Nat := 118140960795 + 290119 * 2 ^ 59
def prefixEnd_290119 : Nat := 4983230072969 + 3 ^ 40 * 290119 * 2
def baseEnd_290119 : Nat := 88278811260358898831569

theorem tailTrace_290119 : CollatzResearch.WordTrace tailWord_290119 prefixEnd_290119 88278811260358898831569 := by
  unfold tailWord_290119
  simp only [CollatzResearch.WordTrace]
  refine ⟨10581509235955886225561411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7054339490637257483707607 10581509235955886225561411)
  ·
    refine ⟨15872263853933829338342117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10581509235955886225561411 15872263853933829338342117)
    ·
      refine ⟨2976049472612593000939147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15872263853933829338342117 2976049472612593000939147)
      ·
        refine ⟨4464074208918889501408721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2976049472612593000939147 4464074208918889501408721)
        ·
          refine ⟨3348055656689167126056541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4464074208918889501408721 3348055656689167126056541)
          ·
            refine ⟨1255520871258437672271203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3348055656689167126056541 1255520871258437672271203)
            ·
              refine ⟨1883281306887656508406805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255520871258437672271203 1883281306887656508406805)
              ·
                refine ⟨88278811260358898831569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1883281306887656508406805 88278811260358898831569)
                ·
                  rfl

theorem cell19_290119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_290119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290119 prefixEnd_290119 := by exact prefixLift 290119
  have htrace : WordTrace (prefixWord ++ tailWord_290119) baseStart_290119 baseEnd_290119 := by
    simpa [prefixWord, tailWord_290119, baseEnd_290119] using wordTrace_append hprefix tailTrace_290119
  have hstable : (prefixWord ++ tailWord_290119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290119).length < 2 ^ (prefixWord ++ tailWord_290119).sum := by decide
  have hdescent : baseEnd_290119 < baseStart_290119 := by decide
  rcases family_descends (prefixWord ++ tailWord_290119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290138 : List Nat := [3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_290138 : Nat := 118140960795 + 290138 * 2 ^ 59
def prefixEnd_290138 : Nat := 4983230072969 + 3 ^ 40 * 290138 * 2
def baseEnd_290138 : Nat := 88284592672172484409295

theorem tailTrace_290138 : CollatzResearch.WordTrace tailWord_290138 prefixEnd_290138 88284592672172484409295 := by
  unfold tailWord_290138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645550555721763117625767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7054801481924701647002045 2645550555721763117625767)
  ·
    refine ⟨3968325833582644676438651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2645550555721763117625767 3968325833582644676438651)
    ·
      refine ⟨5952488750373967014657977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3968325833582644676438651 5952488750373967014657977)
      ·
        refine ⟨4464366562780475260993483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5952488750373967014657977 4464366562780475260993483)
        ·
          refine ⟨6696549844170712891490225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464366562780475260993483 6696549844170712891490225)
          ·
            refine ⟨5022412383128034668617669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6696549844170712891490225 5022412383128034668617669)
            ·
              refine ⟨941702321836506500365813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5022412383128034668617669 941702321836506500365813)
              ·
                refine ⟨88284592672172484409295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 941702321836506500365813 88284592672172484409295)
                ·
                  rfl

theorem cell19_290138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_290138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290138 prefixEnd_290138 := by exact prefixLift 290138
  have htrace : WordTrace (prefixWord ++ tailWord_290138) baseStart_290138 baseEnd_290138 := by
    simpa [prefixWord, tailWord_290138, baseEnd_290138] using wordTrace_append hprefix tailTrace_290138
  have hstable : (prefixWord ++ tailWord_290138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290138).length < 2 ^ (prefixWord ++ tailWord_290138).sum := by decide
  have hdescent : baseEnd_290138 < baseStart_290138 := by decide
  rcases family_descends (prefixWord ++ tailWord_290138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290157 : List Nat := [1, 5, 1, 1, 1, 10]
def baseStart_290157 : Nat := 118140960795 + 290157 * 2 ^ 59
def prefixEnd_290157 : Nat := 4983230072969 + 3 ^ 40 * 290157 * 2
def baseEnd_290157 : Nat := 9810041564887341109669

theorem tailTrace_290157 : CollatzResearch.WordTrace tailWord_290157 prefixEnd_290157 9810041564887341109669 := by
  unfold tailWord_290157
  simp only [CollatzResearch.WordTrace]
  refine ⟨10582895209818218715444725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7055263473212145810296483 10582895209818218715444725)
  ·
    refine ⟨992146425920458004572943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10582895209818218715444725 992146425920458004572943)
    ·
      refine ⟨1488219638880687006859415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992146425920458004572943 1488219638880687006859415)
      ·
        refine ⟨2232329458321030510289123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488219638880687006859415 2232329458321030510289123)
        ·
          refine ⟨3348494187481545765433685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232329458321030510289123 3348494187481545765433685)
          ·
            refine ⟨9810041564887341109669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3348494187481545765433685 9810041564887341109669)
            ·
              rfl

theorem cell19_290157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_290157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290157 prefixEnd_290157 := by exact prefixLift 290157
  have htrace : WordTrace (prefixWord ++ tailWord_290157) baseStart_290157 baseEnd_290157 := by
    simpa [prefixWord, tailWord_290157, baseEnd_290157] using wordTrace_append hprefix tailTrace_290157
  have hstable : (prefixWord ++ tailWord_290157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290157).length < 2 ^ (prefixWord ++ tailWord_290157).sum := by decide
  have hdescent : baseEnd_290157 < baseStart_290157 := by decide
  rcases family_descends (prefixWord ++ tailWord_290157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290250 : List Nat := [3, 1, 2, 1, 2, 3, 4, 3]
def baseStart_290250 : Nat := 118140960795 + 290250 * 2 ^ 59
def prefixEnd_290250 : Nat := 4983230072969 + 3 ^ 40 * 290250 * 2
def baseEnd_290250 : Nat := 88318672573389409920101

theorem tailTrace_290250 : CollatzResearch.WordTrace tailWord_290250 prefixEnd_290250 88318672573389409920101 := by
  unfold tailWord_290250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646571799620323899645051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7057524798987530399053469 2646571799620323899645051)
  ·
    refine ⟨3969857699430485849467577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2646571799620323899645051 3969857699430485849467577)
    ·
      refine ⟨2977393274572864387100683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3969857699430485849467577 2977393274572864387100683)
      ·
        refine ⟨4466089911859296580651025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2977393274572864387100683 4466089911859296580651025)
        ·
          refine ⟨3349567433894472435488269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4466089911859296580651025 3349567433894472435488269)
          ·
            refine ⟨1256087787710427163308101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3349567433894472435488269 1256087787710427163308101)
            ·
              refine ⟨235516460195705093120269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1256087787710427163308101 235516460195705093120269)
              ·
                refine ⟨88318672573389409920101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235516460195705093120269 88318672573389409920101)
                ·
                  rfl

theorem cell19_290250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_290250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290250 prefixEnd_290250 := by exact prefixLift 290250
  have htrace : WordTrace (prefixWord ++ tailWord_290250) baseStart_290250 baseEnd_290250 := by
    simpa [prefixWord, tailWord_290250, baseEnd_290250] using wordTrace_append hprefix tailTrace_290250
  have hstable : (prefixWord ++ tailWord_290250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290250).length < 2 ^ (prefixWord ++ tailWord_290250).sum := by decide
  have hdescent : baseEnd_290250 < baseStart_290250 := by decide
  rcases family_descends (prefixWord ++ tailWord_290250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290269 : List Nat := [1, 4, 3, 1, 1, 4, 5]
def baseStart_290269 : Nat := 118140960795 + 290269 * 2 ^ 59
def prefixEnd_290269 : Nat := 4983230072969 + 3 ^ 40 * 290269 * 2
def baseEnd_290269 : Nat := 29441484661734331832609

theorem tailTrace_290269 : CollatzResearch.WordTrace tailWord_290269 prefixEnd_290269 29441484661734331832609 := by
  unfold tailWord_290269
  simp only [CollatzResearch.WordTrace]
  refine ⟨10586980185412461843521861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7057986790274974562347907 10586980185412461843521861)
  ·
    refine ⟨1985058784764836595660349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10586980185412461843521861 1985058784764836595660349)
    ·
      refine ⟨744397044286813723372631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1985058784764836595660349 744397044286813723372631)
      ·
        refine ⟨1116595566430220585058947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744397044286813723372631 1116595566430220585058947)
        ·
          refine ⟨1674893349645330877588421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116595566430220585058947 1674893349645330877588421)
          ·
            refine ⟨314042503058499539547829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1674893349645330877588421 314042503058499539547829)
            ·
              refine ⟨29441484661734331832609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 314042503058499539547829 29441484661734331832609)
              ·
                rfl

theorem cell19_290269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_290269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290269 prefixEnd_290269 := by exact prefixLift 290269
  have htrace : WordTrace (prefixWord ++ tailWord_290269) baseStart_290269 baseEnd_290269 := by
    simpa [prefixWord, tailWord_290269, baseEnd_290269] using wordTrace_append hprefix tailTrace_290269
  have hstable : (prefixWord ++ tailWord_290269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290269).length < 2 ^ (prefixWord ++ tailWord_290269).sum := by decide
  have hdescent : baseEnd_290269 < baseStart_290269 := by decide
  rcases family_descends (prefixWord ++ tailWord_290269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290324 : List Nat := [2, 4, 3, 1, 3, 6]
def baseStart_290324 : Nat := 118140960795 + 290324 * 2 ^ 59
def prefixEnd_290324 : Nat := 4983230072969 + 3 ^ 40 * 290324 * 2
def baseEnd_290324 : Nat := 9815687738997684919495

theorem tailTrace_290324 : CollatzResearch.WordTrace tailWord_290324 prefixEnd_290324 9815687738997684919495 := by
  unfold tailWord_290324
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294493100106603118387013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7059324133475470824516017 5294493100106603118387013)
  ·
    refine ⟨992717456269988084697565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5294493100106603118387013 992717456269988084697565)
    ·
      refine ⟨372269046101245531761587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 992717456269988084697565 372269046101245531761587)
      ·
        refine ⟨558403569151868297642381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372269046101245531761587 558403569151868297642381)
        ·
          refine ⟨209401338431950611615893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 558403569151868297642381 209401338431950611615893)
          ·
            refine ⟨9815687738997684919495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 209401338431950611615893 9815687738997684919495)
            ·
              rfl

theorem cell19_290324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 6].length) (baseStart_290324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290324 prefixEnd_290324 := by exact prefixLift 290324
  have htrace : WordTrace (prefixWord ++ tailWord_290324) baseStart_290324 baseEnd_290324 := by
    simpa [prefixWord, tailWord_290324, baseEnd_290324] using wordTrace_append hprefix tailTrace_290324
  have hstable : (prefixWord ++ tailWord_290324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290324).length < 2 ^ (prefixWord ++ tailWord_290324).sum := by decide
  have hdescent : baseEnd_290324 < baseStart_290324 := by decide
  rcases family_descends (prefixWord ++ tailWord_290324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290328 : List Nat := [2, 1, 2, 3, 4, 7]
def baseStart_290328 : Nat := 118140960795 + 290328 * 2 ^ 59
def prefixEnd_290328 : Nat := 4983230072969 + 3 ^ 40 * 290328 * 2
def baseEnd_290328 : Nat := 9815822976700926687395

theorem tailTrace_290328 : CollatzResearch.WordTrace tailWord_290328 prefixEnd_290328 9815822976700926687395 := by
  unfold tailWord_290328
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294566046099357459959819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7059421394799143279946425 5294566046099357459959819)
  ·
    refine ⟨7941849069149036189939729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5294566046099357459959819 7941849069149036189939729)
    ·
      refine ⟨5956386801861777142454797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7941849069149036189939729 5956386801861777142454797)
      ·
        refine ⟨2233645050698166428420549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5956386801861777142454797 2233645050698166428420549)
        ·
          refine ⟨418808447005906205328853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2233645050698166428420549 418808447005906205328853)
          ·
            refine ⟨9815822976700926687395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 418808447005906205328853 9815822976700926687395)
            ·
              rfl

theorem cell19_290328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_290328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290328 prefixEnd_290328 := by exact prefixLift 290328
  have htrace : WordTrace (prefixWord ++ tailWord_290328) baseStart_290328 baseEnd_290328 := by
    simpa [prefixWord, tailWord_290328, baseEnd_290328] using wordTrace_append hprefix tailTrace_290328
  have hstable : (prefixWord ++ tailWord_290328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290328).length < 2 ^ (prefixWord ++ tailWord_290328).sum := by decide
  have hdescent : baseEnd_290328 < baseStart_290328 := by decide
  rcases family_descends (prefixWord ++ tailWord_290328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290421 : List Nat := [1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_290421 : Nat := 118140960795 + 290421 * 2 ^ 59
def prefixEnd_290421 : Nat := 4983230072969 + 3 ^ 40 * 290421 * 2
def baseEnd_290421 : Nat := 88370705279711680119635

theorem tailTrace_290421 : CollatzResearch.WordTrace tailWord_290421 prefixEnd_290421 88370705279711680119635 := by
  unfold tailWord_290421
  simp only [CollatzResearch.WordTrace]
  refine ⟨10592524080861791803055117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7061682720574527868703411 10592524080861791803055117)
  ·
    refine ⟨3972196530323171926145669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10592524080861791803055117 3972196530323171926145669)
    ·
      refine ⟨744786849435594736152313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3972196530323171926145669 744786849435594736152313)
      ·
        refine ⟨558590137076696052114235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 744786849435594736152313 558590137076696052114235)
        ·
          refine ⟨837885205615044078171353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558590137076696052114235 837885205615044078171353)
          ·
            refine ⟨628413904211283058628515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837885205615044078171353 628413904211283058628515)
            ·
              refine ⟨942620856316924587942773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628413904211283058628515 942620856316924587942773)
              ·
                refine ⟨88370705279711680119635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 942620856316924587942773 88370705279711680119635)
                ·
                  rfl

theorem cell19_290421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_290421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290421 prefixEnd_290421 := by exact prefixLift 290421
  have htrace : WordTrace (prefixWord ++ tailWord_290421) baseStart_290421 baseEnd_290421 := by
    simpa [prefixWord, tailWord_290421, baseEnd_290421] using wordTrace_append hprefix tailTrace_290421
  have hstable : (prefixWord ++ tailWord_290421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290421).length < 2 ^ (prefixWord ++ tailWord_290421).sum := by decide
  have hdescent : baseEnd_290421 < baseStart_290421 := by decide
  rcases family_descends (prefixWord ++ tailWord_290421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290442 : List Nat := [3, 1, 2, 3, 2, 1, 7]
def baseStart_290442 : Nat := 118140960795 + 290442 * 2 ^ 59
def prefixEnd_290442 : Nat := 4983230072969 + 3 ^ 40 * 290442 * 2
def baseEnd_290442 : Nat := 29459031753729951217637

theorem tailTrace_290442 : CollatzResearch.WordTrace tailWord_290442 prefixEnd_290442 29459031753729951217637 := by
  unfold tailWord_290442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648322503446428097392395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7062193342523808259713053 2648322503446428097392395)
  ·
    refine ⟨3972483755169642146088593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2648322503446428097392395 3972483755169642146088593)
    ·
      refine ⟨2979362816377231609566445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3972483755169642146088593 2979362816377231609566445)
      ·
        refine ⟨1117261056141461853587417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2979362816377231609566445 1117261056141461853587417)
        ·
          refine ⟨837945792106096390190563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117261056141461853587417 837945792106096390190563)
          ·
            refine ⟨1256918688159144585285845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837945792106096390190563 1256918688159144585285845)
            ·
              refine ⟨29459031753729951217637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1256918688159144585285845 29459031753729951217637)
              ·
                rfl

theorem cell19_290442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_290442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290442 prefixEnd_290442 := by exact prefixLift 290442
  have htrace : WordTrace (prefixWord ++ tailWord_290442) baseStart_290442 baseEnd_290442 := by
    simpa [prefixWord, tailWord_290442, baseEnd_290442] using wordTrace_append hprefix tailTrace_290442
  have hstable : (prefixWord ++ tailWord_290442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290442).length < 2 ^ (prefixWord ++ tailWord_290442).sum := by decide
  have hdescent : baseEnd_290442 < baseStart_290442 := by decide
  rcases family_descends (prefixWord ++ tailWord_290442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290516 : List Nat := [2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_290516 : Nat := 118140960795 + 290516 * 2 ^ 59
def prefixEnd_290516 : Nat := 4983230072969 + 3 ^ 40 * 290516 * 2
def baseEnd_290516 : Nat := 88399612338779608008265

theorem tailTrace_290516 : CollatzResearch.WordTrace tailWord_290516 prefixEnd_290516 88399612338779608008265 := by
  unfold tailWord_290516
  simp only [CollatzResearch.WordTrace]
  refine ⟨5297994507758811513881701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7063992677011748685175601 5297994507758811513881701)
  ·
    refine ⟨993373970204777158852819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5297994507758811513881701 993373970204777158852819)
    ·
      refine ⟨1490060955307165738279229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993373970204777158852819 1490060955307165738279229)
      ·
        refine ⟨558772858240187151854711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1490060955307165738279229 558772858240187151854711)
        ·
          refine ⟨838159287360280727782067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558772858240187151854711 838159287360280727782067)
          ·
            refine ⟨1257238931040421091673101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838159287360280727782067 1257238931040421091673101)
            ·
              refine ⟨471464599140157909377413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1257238931040421091673101 471464599140157909377413)
              ·
                refine ⟨88399612338779608008265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 471464599140157909377413 88399612338779608008265)
                ·
                  rfl

theorem cell19_290516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_290516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290516 prefixEnd_290516 := by exact prefixLift 290516
  have htrace : WordTrace (prefixWord ++ tailWord_290516) baseStart_290516 baseEnd_290516 := by
    simpa [prefixWord, tailWord_290516, baseEnd_290516] using wordTrace_append hprefix tailTrace_290516
  have hstable : (prefixWord ++ tailWord_290516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290516).length < 2 ^ (prefixWord ++ tailWord_290516).sum := by decide
  have hdescent : baseEnd_290516 < baseStart_290516 := by decide
  rcases family_descends (prefixWord ++ tailWord_290516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290539 : List Nat := [1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_290539 : Nat := 118140960795 + 290539 * 2 ^ 59
def prefixEnd_290539 : Nat := 4983230072969 + 3 ^ 40 * 290539 * 2
def baseEnd_290539 : Nat := 88406610889922369497091

theorem tailTrace_290539 : CollatzResearch.WordTrace tailWord_290539 prefixEnd_290539 88406610889922369497091 := by
  unfold tailWord_290539
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596827894434297955850671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7064551929622865303900447 10596827894434297955850671)
  ·
    refine ⟨15895241841651446933776007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10596827894434297955850671 15895241841651446933776007)
    ·
      refine ⟨23842862762477170400664011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15895241841651446933776007 23842862762477170400664011)
      ·
        refine ⟨35764294143715755600996017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23842862762477170400664011 35764294143715755600996017)
        ·
          refine ⟨26823220607786816700747013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35764294143715755600996017 26823220607786816700747013)
          ·
            refine ⟨5029353863960028131390065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26823220607786816700747013 5029353863960028131390065)
            ·
              refine ⟨3772015397970021098542549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029353863960028131390065 3772015397970021098542549)
              ·
                refine ⟨88406610889922369497091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3772015397970021098542549 88406610889922369497091)
                ·
                  rfl

theorem cell19_290539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_290539 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290539 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290539 prefixEnd_290539 := by exact prefixLift 290539
  have htrace : WordTrace (prefixWord ++ tailWord_290539) baseStart_290539 baseEnd_290539 := by
    simpa [prefixWord, tailWord_290539, baseEnd_290539] using wordTrace_append hprefix tailTrace_290539
  have hstable : (prefixWord ++ tailWord_290539).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290539).length < 2 ^ (prefixWord ++ tailWord_290539).sum := by decide
  have hdescent : baseEnd_290539 < baseStart_290539 := by decide
  rcases family_descends (prefixWord ++ tailWord_290539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290577 : List Nat := [1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_290577 : Nat := 118140960795 + 290577 * 2 ^ 59
def prefixEnd_290577 : Nat := 4983230072969 + 3 ^ 40 * 290577 * 2
def baseEnd_290577 : Nat := 88418173713549540652543

theorem tailTrace_290577 : CollatzResearch.WordTrace tailWord_290577 prefixEnd_290577 88418173713549540652543 := by
  unfold tailWord_290577
  simp only [CollatzResearch.WordTrace]
  refine ⟨10598213868296630445733985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7065475912197753630489323 10598213868296630445733985)
  ·
    refine ⟨7948660401222472834300489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10598213868296630445733985 7948660401222472834300489)
    ·
      refine ⟨5961495300916854625725367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7948660401222472834300489 5961495300916854625725367)
      ·
        refine ⟨8942242951375281938588051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5961495300916854625725367 8942242951375281938588051)
        ·
          refine ⟨13413364427062922907882077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8942242951375281938588051 13413364427062922907882077)
          ·
            refine ⟨5030011660148596090455779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13413364427062922907882077 5030011660148596090455779)
            ·
              refine ⟨7545017490222894135683669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5030011660148596090455779 7545017490222894135683669)
              ·
                refine ⟨88418173713549540652543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7545017490222894135683669 88418173713549540652543)
                ·
                  rfl

theorem cell19_290577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_290577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290577 prefixEnd_290577 := by exact prefixLift 290577
  have htrace : WordTrace (prefixWord ++ tailWord_290577) baseStart_290577 baseEnd_290577 := by
    simpa [prefixWord, tailWord_290577, baseEnd_290577] using wordTrace_append hprefix tailTrace_290577
  have hstable : (prefixWord ++ tailWord_290577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290577).length < 2 ^ (prefixWord ++ tailWord_290577).sum := by decide
  have hdescent : baseEnd_290577 < baseStart_290577 := by decide
  rcases family_descends (prefixWord ++ tailWord_290577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290594 : List Nat := [3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_290594 : Nat := 118140960795 + 290594 * 2 ^ 59
def prefixEnd_290594 : Nat := 4983230072969 + 3 ^ 40 * 290594 * 2
def baseEnd_290594 : Nat := 88423346555698538274719

theorem tailTrace_290594 : CollatzResearch.WordTrace tailWord_290594 prefixEnd_290594 88423346555698538274719 := by
  unfold tailWord_290594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649708477308760587275709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7065889272823361566068557 2649708477308760587275709)
  ·
    refine ⟨993640678990785220228391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2649708477308760587275709 993640678990785220228391)
    ·
      refine ⟨1490461018486177830342587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993640678990785220228391 1490461018486177830342587)
      ·
        refine ⟨2235691527729266745513881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490461018486177830342587 2235691527729266745513881)
        ·
          refine ⟨1676768645796950059135411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235691527729266745513881 1676768645796950059135411)
          ·
            refine ⟨2515152968695425088703117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676768645796950059135411 2515152968695425088703117)
            ·
              refine ⟨943182363260784408263669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2515152968695425088703117 943182363260784408263669)
              ·
                refine ⟨88423346555698538274719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 943182363260784408263669 88423346555698538274719)
                ·
                  rfl

theorem cell19_290594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_290594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290594 prefixEnd_290594 := by exact prefixLift 290594
  have htrace : WordTrace (prefixWord ++ tailWord_290594) baseStart_290594 baseEnd_290594 := by
    simpa [prefixWord, tailWord_290594, baseEnd_290594] using wordTrace_append hprefix tailTrace_290594
  have hstable : (prefixWord ++ tailWord_290594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290594).length < 2 ^ (prefixWord ++ tailWord_290594).sum := by decide
  have hdescent : baseEnd_290594 < baseStart_290594 := by decide
  rcases family_descends (prefixWord ++ tailWord_290594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290611 : List Nat := [1, 1, 1, 2, 8, 1, 5]
def baseStart_290611 : Nat := 118140960795 + 290611 * 2 ^ 59
def prefixEnd_290611 : Nat := 4983230072969 + 3 ^ 40 * 290611 * 2
def baseEnd_290611 : Nat := 29476173132615845298965

theorem tailTrace_290611 : CollatzResearch.WordTrace tailWord_290611 prefixEnd_290611 29476173132615845298965 := by
  unfold tailWord_290611
  simp only [CollatzResearch.WordTrace]
  refine ⟨10599453950173454252471687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7066302633448969501647791 10599453950173454252471687)
  ·
    refine ⟨15899180925260181378707531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10599453950173454252471687 15899180925260181378707531)
    ·
      refine ⟨23848771387890272068061297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15899180925260181378707531 23848771387890272068061297)
      ·
        refine ⟨17886578540917704051045973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23848771387890272068061297 17886578540917704051045973)
        ·
          refine ⟨209608342276379344348195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 17886578540917704051045973 209608342276379344348195)
          ·
            refine ⟨314412513414569016522293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209608342276379344348195 314412513414569016522293)
            ·
              refine ⟨29476173132615845298965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 314412513414569016522293 29476173132615845298965)
              ·
                rfl

theorem cell19_290611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_290611 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290611 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290611 prefixEnd_290611 := by exact prefixLift 290611
  have htrace : WordTrace (prefixWord ++ tailWord_290611) baseStart_290611 baseEnd_290611 := by
    simpa [prefixWord, tailWord_290611, baseEnd_290611] using wordTrace_append hprefix tailTrace_290611
  have hstable : (prefixWord ++ tailWord_290611).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290611).length < 2 ^ (prefixWord ++ tailWord_290611).sum := by decide
  have hdescent : baseEnd_290611 < baseStart_290611 := by decide
  rcases family_descends (prefixWord ++ tailWord_290611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290632 : List Nat := [2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_290632 : Nat := 118140960795 + 290632 * 2 ^ 59
def prefixEnd_290632 : Nat := 4983230072969 + 3 ^ 40 * 290632 * 2
def baseEnd_290632 : Nat := 88434909379325709430171

theorem tailTrace_290632 : CollatzResearch.WordTrace tailWord_290632 prefixEnd_290632 88434909379325709430171 := by
  unfold tailWord_290632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300109941548687419493075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7066813255398249892657433 5300109941548687419493075)
  ·
    refine ⟨7950164912323031129239613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5300109941548687419493075 7950164912323031129239613)
    ·
      refine ⟨2981311842121136673464855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7950164912323031129239613 2981311842121136673464855)
      ·
        refine ⟨4471967763181705010197283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981311842121136673464855 4471967763181705010197283)
        ·
          refine ⟨6707951644772557515295925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471967763181705010197283 6707951644772557515295925)
          ·
            refine ⟨628870466697427267058993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6707951644772557515295925 628870466697427267058993)
            ·
              refine ⟨471652850023070450294245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628870466697427267058993 471652850023070450294245)
              ·
                refine ⟨88434909379325709430171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 471652850023070450294245 88434909379325709430171)
                ·
                  rfl

theorem cell19_290632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_290632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290632 prefixEnd_290632 := by exact prefixLift 290632
  have htrace : WordTrace (prefixWord ++ tailWord_290632) baseStart_290632 baseEnd_290632 := by
    simpa [prefixWord, tailWord_290632, baseEnd_290632] using wordTrace_append hprefix tailTrace_290632
  have hstable : (prefixWord ++ tailWord_290632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290632).length < 2 ^ (prefixWord ++ tailWord_290632).sum := by decide
  have hdescent : baseEnd_290632 < baseStart_290632 := by decide
  rcases family_descends (prefixWord ++ tailWord_290632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290670 : List Nat := [4, 1, 2, 3, 1, 8]
def baseStart_290670 : Nat := 118140960795 + 290670 * 2 ^ 59
def prefixEnd_290670 : Nat := 4983230072969 + 3 ^ 40 * 290670 * 2
def baseEnd_290670 : Nat := 9827385800328097842847

theorem tailTrace_290670 : CollatzResearch.WordTrace tailWord_290670 prefixEnd_290670 9827385800328097842847 := by
  unfold tailWord_290670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325200732119963416108683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7067737237973138219246309 1325200732119963416108683)
  ·
    refine ⟨1987801098179945124163025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1325200732119963416108683 1987801098179945124163025)
    ·
      refine ⟨1490850823634958843122269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1987801098179945124163025 1490850823634958843122269)
      ·
        refine ⟨559069058863109566170851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1490850823634958843122269 559069058863109566170851)
        ·
          refine ⟨838603588294664349256277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559069058863109566170851 838603588294664349256277)
          ·
            refine ⟨9827385800328097842847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 838603588294664349256277 9827385800328097842847)
            ·
              rfl

theorem cell19_290670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_290670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290670 prefixEnd_290670 := by exact prefixLift 290670
  have htrace : WordTrace (prefixWord ++ tailWord_290670) baseStart_290670 baseEnd_290670 := by
    simpa [prefixWord, tailWord_290670, baseEnd_290670] using wordTrace_append hprefix tailTrace_290670
  have hstable : (prefixWord ++ tailWord_290670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290670).length < 2 ^ (prefixWord ++ tailWord_290670).sum := by decide
  have hdescent : baseEnd_290670 < baseStart_290670 := by decide
  rcases family_descends (prefixWord ++ tailWord_290670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290727 : List Nat := [1, 1, 6, 1, 2, 2, 6]
def baseStart_290727 : Nat := 118140960795 + 290727 * 2 ^ 59
def prefixEnd_290727 : Nat := 4983230072969 + 3 ^ 40 * 290727 * 2
def baseEnd_290727 : Nat := 29487938812797879106267

theorem tailTrace_290727 : CollatzResearch.WordTrace tailWord_290727 prefixEnd_290727 29487938812797879106267 := by
  unfold tailWord_290727
  simp only [CollatzResearch.WordTrace]
  refine ⟨10603684817753206063694435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7069123211835470709129623 10603684817753206063694435)
  ·
    refine ⟨15905527226629809095541653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10603684817753206063694435 15905527226629809095541653)
    ·
      refine ⟨745571588748272301353515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15905527226629809095541653 745571588748272301353515)
      ·
        refine ⟨1118357383122408452030273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745571588748272301353515 1118357383122408452030273)
        ·
          refine ⟨838768037341806339022705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1118357383122408452030273 838768037341806339022705)
          ·
            refine ⟨629076028006354754267029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838768037341806339022705 629076028006354754267029)
            ·
              refine ⟨29487938812797879106267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 629076028006354754267029 29487938812797879106267)
              ·
                rfl

theorem cell19_290727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_290727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290727 prefixEnd_290727 := by exact prefixLift 290727
  have htrace : WordTrace (prefixWord ++ tailWord_290727) baseStart_290727 baseEnd_290727 := by
    simpa [prefixWord, tailWord_290727, baseEnd_290727] using wordTrace_append hprefix tailTrace_290727
  have hstable : (prefixWord ++ tailWord_290727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290727).length < 2 ^ (prefixWord ++ tailWord_290727).sum := by decide
  have hdescent : baseEnd_290727 < baseStart_290727 := by decide
  rcases family_descends (prefixWord ++ tailWord_290727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
