import V185TrunkScan23Chunk0987

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5848665 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 3]
def baseStart_5848665 : Nat := 118140960795 + 5848665 * 2 ^ 59
def prefixEnd_5848665 : Nat := 4983230072969 + 3 ^ 40 * 5848665 * 2
def baseEnd_5848665 : Nat := 3003176332128464804989985

theorem tailTrace_5848665 : CollatzResearch.WordTrace tailWord_5848665 prefixEnd_5848665 3003176332128464804989985 := by
  unfold tailWord_5848665
  simp only [CollatzResearch.WordTrace]
  refine ⟨213318337356293052302811449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142212224904195368201874299 213318337356293052302811449)
  ·
    refine ⟨159988753017219789227108587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213318337356293052302811449 159988753017219789227108587)
    ·
      refine ⟨239983129525829683840662881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159988753017219789227108587 239983129525829683840662881)
      ·
        refine ⟨179987347144372262880497161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239983129525829683840662881 179987347144372262880497161)
        ·
          refine ⟨134990510358279197160372871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179987347144372262880497161 134990510358279197160372871)
          ·
            refine ⟨202485765537418795740559307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134990510358279197160372871 202485765537418795740559307)
            ·
              refine ⟨303728648306128193610838961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202485765537418795740559307 303728648306128193610838961)
              ·
                refine ⟨227796486229596145208129221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303728648306128193610838961 227796486229596145208129221)
                ·
                  refine ⟨42711841168049277226524229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227796486229596145208129221 42711841168049277226524229)
                  ·
                    refine ⟨8008470219009239479973293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42711841168049277226524229 8008470219009239479973293)
                    ·
                      refine ⟨3003176332128464804989985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008470219009239479973293 3003176332128464804989985)
                      ·
                        rfl

theorem cell23_5848665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_5848665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848665 prefixEnd_5848665 := by exact prefixLift 5848665
  have htrace : WordTrace (prefixWord ++ tailWord_5848665) baseStart_5848665 baseEnd_5848665 := by
    simpa [prefixWord, tailWord_5848665, baseEnd_5848665] using wordTrace_append hprefix tailTrace_5848665
  have hstable : (prefixWord ++ tailWord_5848665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848665).length < 2 ^ (prefixWord ++ tailWord_5848665).sum := by decide
  have hdescent : baseEnd_5848665 < baseStart_5848665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848679 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_5848679 : Nat := 118140960795 + 5848679 * 2 ^ 59
def prefixEnd_5848679 : Nat := 4983230072969 + 3 ^ 40 * 5848679 * 2
def baseEnd_5848679 : Nat := 3003183520857627750214921

theorem tailTrace_5848679 : CollatzResearch.WordTrace tailWord_5848679 prefixEnd_5848679 3003183520857627750214921 := by
  unfold tailWord_5848679
  simp only [CollatzResearch.WordTrace]
  refine ⟨213318847978242332693821091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142212565318828221795880727 213318847978242332693821091)
  ·
    refine ⟨319978271967363499040731637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213318847978242332693821091 319978271967363499040731637)
    ·
      refine ⟨29997962996940328035068591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 319978271967363499040731637 29997962996940328035068591)
      ·
        refine ⟨44996944495410492052602887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29997962996940328035068591 44996944495410492052602887)
        ·
          refine ⟨67495416743115738078904331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44996944495410492052602887 67495416743115738078904331)
          ·
            refine ⟨101243125114673607118356497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67495416743115738078904331 101243125114673607118356497)
            ·
              refine ⟨75932343836005205338767373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101243125114673607118356497 75932343836005205338767373)
              ·
                refine ⟨28474628938501952002037765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75932343836005205338767373 28474628938501952002037765)
                ·
                  refine ⟨5338992925969116000382081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28474628938501952002037765 5338992925969116000382081)
                  ·
                    refine ⟨4004244694476837000286561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5338992925969116000382081 4004244694476837000286561)
                    ·
                      refine ⟨3003183520857627750214921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4004244694476837000286561 3003183520857627750214921)
                      ·
                        rfl

theorem cell23_5848679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_5848679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848679 prefixEnd_5848679 := by exact prefixLift 5848679
  have htrace : WordTrace (prefixWord ++ tailWord_5848679) baseStart_5848679 baseEnd_5848679 := by
    simpa [prefixWord, tailWord_5848679, baseEnd_5848679] using wordTrace_append hprefix tailTrace_5848679
  have hstable : (prefixWord ++ tailWord_5848679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848679).length < 2 ^ (prefixWord ++ tailWord_5848679).sum := by decide
  have hdescent : baseEnd_5848679 < baseStart_5848679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848682 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_5848682 : Nat := 118140960795 + 5848682 * 2 ^ 59
def prefixEnd_5848682 : Nat := 4983230072969 + 3 ^ 40 * 5848682 * 2
def baseEnd_5848682 : Nat := 3003185061299591238477407

theorem tailTrace_5848682 : CollatzResearch.WordTrace tailWord_5848682 prefixEnd_5848682 3003185061299591238477407 := by
  unfold tailWord_5848682
  simp only [CollatzResearch.WordTrace]
  refine ⟨53329739349307866051545075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142212638264820976137453533 53329739349307866051545075)
  ·
    refine ⟨79994609023961799077317613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53329739349307866051545075 79994609023961799077317613)
    ·
      refine ⟨29997978383985674653994105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79994609023961799077317613 29997978383985674653994105)
      ·
        refine ⟨22498483787989255990495579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29997978383985674653994105 22498483787989255990495579)
        ·
          refine ⟨33747725681983883985743369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22498483787989255990495579 33747725681983883985743369)
          ·
            refine ⟨25310794261487912989307527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33747725681983883985743369 25310794261487912989307527)
            ·
              refine ⟨37966191392231869483961291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25310794261487912989307527 37966191392231869483961291)
              ·
                refine ⟨56949287088347804225941937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37966191392231869483961291 56949287088347804225941937)
                ·
                  refine ⟨42711965316260853169456453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56949287088347804225941937 42711965316260853169456453)
                  ·
                    refine ⟨8008493496798909969273085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42711965316260853169456453 8008493496798909969273085)
                    ·
                      refine ⟨3003185061299591238477407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008493496798909969273085 3003185061299591238477407)
                      ·
                        rfl

theorem cell23_5848682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_5848682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848682 prefixEnd_5848682 := by exact prefixLift 5848682
  have htrace : WordTrace (prefixWord ++ tailWord_5848682) baseStart_5848682 baseEnd_5848682 := by
    simpa [prefixWord, tailWord_5848682, baseEnd_5848682] using wordTrace_append hprefix tailTrace_5848682
  have hstable : (prefixWord ++ tailWord_5848682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848682).length < 2 ^ (prefixWord ++ tailWord_5848682).sum := by decide
  have hdescent : baseEnd_5848682 < baseStart_5848682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848715 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 1, 7]
def baseStart_5848715 : Nat := 118140960795 + 5848715 * 2 ^ 59
def prefixEnd_5848715 : Nat := 4983230072969 + 3 ^ 40 * 5848715 * 2
def baseEnd_5848715 : Nat := 1001067335387063203121585

theorem tailTrace_5848715 : CollatzResearch.WordTrace tailWord_5848715 prefixEnd_5848715 1001067335387063203121585 := by
  unfold tailWord_5848715
  simp only [CollatzResearch.WordTrace]
  refine ⟨213320161006111910842131599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142213440670741273894754399 213320161006111910842131599)
  ·
    refine ⟨319980241509167866263197399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213320161006111910842131599 319980241509167866263197399)
    ·
      refine ⟨479970362263751799394796099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319980241509167866263197399 479970362263751799394796099)
      ·
        refine ⟨719955543395627699092194149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479970362263751799394796099 719955543395627699092194149)
        ·
          refine ⟨134991664386680193579786403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 719955543395627699092194149 134991664386680193579786403)
          ·
            refine ⟨202487496580020290369679605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134991664386680193579786403 202487496580020290369679605)
            ·
              refine ⟨18983202804376902222157463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202487496580020290369679605 18983202804376902222157463)
              ·
                refine ⟨28474804206565353333236195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18983202804376902222157463 28474804206565353333236195)
                ·
                  refine ⟨42712206309848029999854293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28474804206565353333236195 42712206309848029999854293)
                  ·
                    refine ⟨1001067335387063203121585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42712206309848029999854293 1001067335387063203121585)
                    ·
                      rfl

theorem cell23_5848715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 7].length) (baseStart_5848715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848715 prefixEnd_5848715 := by exact prefixLift 5848715
  have htrace : WordTrace (prefixWord ++ tailWord_5848715) baseStart_5848715 baseEnd_5848715 := by
    simpa [prefixWord, tailWord_5848715, baseEnd_5848715] using wordTrace_append hprefix tailTrace_5848715
  have hstable : (prefixWord ++ tailWord_5848715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848715).length < 2 ^ (prefixWord ++ tailWord_5848715).sum := by decide
  have hdescent : baseEnd_5848715 < baseStart_5848715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848725 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_5848725 : Nat := 118140960795 + 5848725 * 2 ^ 59
def prefixEnd_5848725 : Nat := 4983230072969 + 3 ^ 40 * 5848725 * 2
def baseEnd_5848725 : Nat := 3003207140967734570239709

theorem tailTrace_5848725 : CollatzResearch.WordTrace tailWord_5848725 prefixEnd_5848725 3003207140967734570239709 := by
  unfold tailWord_5848725
  simp only [CollatzResearch.WordTrace]
  refine ⟨213320525736075682549995629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142213683824050455033330419 213320525736075682549995629)
  ·
    refine ⟨79995197151028380956248361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213320525736075682549995629 79995197151028380956248361)
    ·
      refine ⟨59996397863271285717186271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79995197151028380956248361 59996397863271285717186271)
      ·
        refine ⟨89994596794906928575779407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59996397863271285717186271 89994596794906928575779407)
        ·
          refine ⟨134991895192360392863669111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89994596794906928575779407 134991895192360392863669111)
          ·
            refine ⟨202487842788540589295503667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134991895192360392863669111 202487842788540589295503667)
            ·
              refine ⟨303731764182810883943255501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202487842788540589295503667 303731764182810883943255501)
              ·
                refine ⟨113899411568554081478720813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303731764182810883943255501 113899411568554081478720813)
                ·
                  refine ⟨42712279338207780554520305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113899411568554081478720813 42712279338207780554520305)
                  ·
                    refine ⟨32034209503655835415890229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42712279338207780554520305 32034209503655835415890229)
                    ·
                      refine ⟨3003207140967734570239709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32034209503655835415890229 3003207140967734570239709)
                      ·
                        rfl

theorem cell23_5848725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_5848725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848725 prefixEnd_5848725 := by exact prefixLift 5848725
  have htrace : WordTrace (prefixWord ++ tailWord_5848725) baseStart_5848725 baseEnd_5848725 := by
    simpa [prefixWord, tailWord_5848725, baseEnd_5848725] using wordTrace_append hprefix tailTrace_5848725
  have hstable : (prefixWord ++ tailWord_5848725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848725).length < 2 ^ (prefixWord ++ tailWord_5848725).sum := by decide
  have hdescent : baseEnd_5848725 < baseStart_5848725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848775 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 10]
def baseStart_5848775 : Nat := 118140960795 + 5848775 * 2 ^ 59
def prefixEnd_5848775 : Nat := 4983230072969 + 3 ^ 40 * 5848775 * 2
def baseEnd_5848775 : Nat := 333692535000051041623831

theorem tailTrace_5848775 : CollatzResearch.WordTrace tailWord_5848775 prefixEnd_5848775 333692535000051041623831 := by
  unfold tailWord_5848775
  simp only [CollatzResearch.WordTrace]
  refine ⟨213322349385894541089315779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142214899590596360726210519 213322349385894541089315779)
  ·
    refine ⟨319983524078841811633973669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213322349385894541089315779 319983524078841811633973669)
    ·
      refine ⟨59996910764782839681370063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319983524078841811633973669 59996910764782839681370063)
      ·
        refine ⟨89995366147174259522055095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59996910764782839681370063 89995366147174259522055095)
        ·
          refine ⟨134993049220761389283082643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89995366147174259522055095 134993049220761389283082643)
          ·
            refine ⟨202489573831142083924623965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134993049220761389283082643 202489573831142083924623965)
            ·
              refine ⟨75933590186678281471733987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202489573831142083924623965 75933590186678281471733987)
              ·
                refine ⟨113900385280017422207600981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75933590186678281471733987 113900385280017422207600981)
                ·
                  refine ⟨333692535000051041623831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 113900385280017422207600981 333692535000051041623831)
                  ·
                    rfl

theorem cell23_5848775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 10].length) (baseStart_5848775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848775 prefixEnd_5848775 := by exact prefixLift 5848775
  have htrace : WordTrace (prefixWord ++ tailWord_5848775) baseStart_5848775 baseEnd_5848775 := by
    simpa [prefixWord, tailWord_5848775, baseEnd_5848775] using wordTrace_append hprefix tailTrace_5848775
  have hstable : (prefixWord ++ tailWord_5848775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848775).length < 2 ^ (prefixWord ++ tailWord_5848775).sum := by decide
  have hdescent : baseEnd_5848775 < baseStart_5848775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848792 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 6]
def baseStart_5848792 : Nat := 118140960795 + 5848792 * 2 ^ 59
def prefixEnd_5848792 : Nat := 4983230072969 + 3 ^ 40 * 5848792 * 2
def baseEnd_5848792 : Nat := 333693504907953978677989

theorem tailTrace_5848792 : CollatzResearch.WordTrace tailWord_5848792 prefixEnd_5848792 333693504907953978677989 := by
  unfold tailWord_5848792
  simp only [CollatzResearch.WordTrace]
  refine ⟨106661484713416476496342315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142215312951221968661789753 106661484713416476496342315)
  ·
    refine ⟨159992227070124714744513473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106661484713416476496342315 159992227070124714744513473)
    ·
      refine ⟨119994170302593536058385105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159992227070124714744513473 119994170302593536058385105)
      ·
        refine ⟨89995627726945152043788829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119994170302593536058385105 89995627726945152043788829)
        ·
          refine ⟨33748360397604432016420811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89995627726945152043788829 33748360397604432016420811)
          ·
            refine ⟨50622540596406648024631217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33748360397604432016420811 50622540596406648024631217)
            ·
              refine ⟨37966905447304986018473413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50622540596406648024631217 37966905447304986018473413)
              ·
                refine ⟨7118794771369684878463765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37966905447304986018473413 7118794771369684878463765)
                ·
                  refine ⟨333693504907953978677989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7118794771369684878463765 333693504907953978677989)
                  ·
                    rfl

theorem cell23_5848792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 6].length) (baseStart_5848792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848792 prefixEnd_5848792 := by exact prefixLift 5848792
  have htrace : WordTrace (prefixWord ++ tailWord_5848792) baseStart_5848792 baseEnd_5848792 := by
    simpa [prefixWord, tailWord_5848792, baseEnd_5848792] using wordTrace_append hprefix tailTrace_5848792
  have hstable : (prefixWord ++ tailWord_5848792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848792).length < 2 ^ (prefixWord ++ tailWord_5848792).sum := by decide
  have hdescent : baseEnd_5848792 < baseStart_5848792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848819 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 3]
def baseStart_5848819 : Nat := 118140960795 + 5848819 * 2 ^ 59
def prefixEnd_5848819 : Nat := 4983230072969 + 3 ^ 40 * 5848819 * 2
def baseEnd_5848819 : Nat := 3003255408149257202464277

theorem tailTrace_5848819 : CollatzResearch.WordTrace tailWord_5848819 prefixEnd_5848819 3003255408149257202464277 := by
  unfold tailWord_5848819
  simp only [CollatzResearch.WordTrace]
  refine ⟨213323954197735136603917511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142215969465156757735945007 213323954197735136603917511)
  ·
    refine ⟨319985931296602704905876267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213323954197735136603917511 319985931296602704905876267)
    ·
      refine ⟨479978896944904057358814401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319985931296602704905876267 479978896944904057358814401)
      ·
        refine ⟨359984172708678043019110801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479978896944904057358814401 359984172708678043019110801)
        ·
          refine ⟨269988129531508532264333101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359984172708678043019110801 269988129531508532264333101)
          ·
            refine ⟨101245548574315699599124913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269988129531508532264333101 101245548574315699599124913)
            ·
              refine ⟨75934161430736774699343685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101245548574315699599124913 75934161430736774699343685)
              ·
                refine ⟨14237655268263145256126941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75934161430736774699343685 14237655268263145256126941)
                ·
                  refine ⟨5339120725598679471047603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14237655268263145256126941 5339120725598679471047603)
                  ·
                    refine ⟨8008681088398019206571405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5339120725598679471047603 8008681088398019206571405)
                    ·
                      refine ⟨3003255408149257202464277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008681088398019206571405 3003255408149257202464277)
                      ·
                        rfl

theorem cell23_5848819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 3].length) (baseStart_5848819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848819 prefixEnd_5848819 := by exact prefixLift 5848819
  have htrace : WordTrace (prefixWord ++ tailWord_5848819) baseStart_5848819 baseEnd_5848819 := by
    simpa [prefixWord, tailWord_5848819, baseEnd_5848819] using wordTrace_append hprefix tailTrace_5848819
  have hstable : (prefixWord ++ tailWord_5848819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848819).length < 2 ^ (prefixWord ++ tailWord_5848819).sum := by decide
  have hdescent : baseEnd_5848819 < baseStart_5848819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848846 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_5848846 : Nat := 118140960795 + 5848846 * 2 ^ 59
def prefixEnd_5848846 : Nat := 4983230072969 + 3 ^ 40 * 5848846 * 2
def baseEnd_5848846 : Nat := 3003269272126928596826653

theorem tailTrace_5848846 : CollatzResearch.WordTrace tailWord_5848846 prefixEnd_5848846 3003269272126928596826653 := by
  unfold tailWord_5848846
  simp only [CollatzResearch.WordTrace]
  refine ⟨26665617371079665026893799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142216625979091546810100261 26665617371079665026893799)
  ·
    refine ⟨39998426056619497540340699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26665617371079665026893799 39998426056619497540340699)
    ·
      refine ⟨59997639084929246310511049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39998426056619497540340699 59997639084929246310511049)
      ·
        refine ⟨44998229313696934732883287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59997639084929246310511049 44998229313696934732883287)
        ·
          refine ⟨67497343970545402099324931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44998229313696934732883287 67497343970545402099324931)
          ·
            refine ⟨101246015955818103148987397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67497343970545402099324931 101246015955818103148987397)
            ·
              refine ⟨18983627991715894340435137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101246015955818103148987397 18983627991715894340435137)
              ·
                refine ⟨14237720993786920755326353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18983627991715894340435137 14237720993786920755326353)
                ·
                  refine ⟨10678290745340190566494765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14237720993786920755326353 10678290745340190566494765)
                  ·
                    refine ⟨4004359029502571462435537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10678290745340190566494765 4004359029502571462435537)
                    ·
                      refine ⟨3003269272126928596826653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4004359029502571462435537 3003269272126928596826653)
                      ·
                        rfl

theorem cell23_5848846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_5848846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848846 prefixEnd_5848846 := by exact prefixLift 5848846
  have htrace : WordTrace (prefixWord ++ tailWord_5848846) baseStart_5848846 baseEnd_5848846 := by
    simpa [prefixWord, tailWord_5848846, baseEnd_5848846] using wordTrace_append hprefix tailTrace_5848846
  have hstable : (prefixWord ++ tailWord_5848846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848846).length < 2 ^ (prefixWord ++ tailWord_5848846).sum := by decide
  have hdescent : baseEnd_5848846 < baseStart_5848846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848853 : List Nat := [1, 3, 2, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_5848853 : Nat := 118140960795 + 5848853 * 2 ^ 59
def prefixEnd_5848853 : Nat := 4983230072969 + 3 ^ 40 * 5848853 * 2
def baseEnd_5848853 : Nat := 3003272866491510069439121

theorem tailTrace_5848853 : CollatzResearch.WordTrace tailWord_5848853 prefixEnd_5848853 3003272866491510069439121 := by
  unfold tailWord_5848853
  simp only [CollatzResearch.WordTrace]
  refine ⟨213325194279611960410655213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142216796186407973607103475 213325194279611960410655213)
  ·
    refine ⟨79996947854854485153995705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213325194279611960410655213 79996947854854485153995705)
    ·
      refine ⟨59997710891140863865496779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79996947854854485153995705 59997710891140863865496779)
      ·
        refine ⟨89996566336711295798245169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59997710891140863865496779 89996566336711295798245169)
        ·
          refine ⟨67497424752533471848683877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89996566336711295798245169 67497424752533471848683877)
          ·
            refine ⟨12655767141100025971628227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67497424752533471848683877 12655767141100025971628227)
            ·
              refine ⟨18983650711650038957442341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12655767141100025971628227 18983650711650038957442341)
              ·
                refine ⟨3559434508434382304520439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18983650711650038957442341 3559434508434382304520439)
                ·
                  refine ⟨5339151762651573456780659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559434508434382304520439 5339151762651573456780659)
                  ·
                    refine ⟨8008727643977360185170989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5339151762651573456780659 8008727643977360185170989)
                    ·
                      refine ⟨3003272866491510069439121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008727643977360185170989 3003272866491510069439121)
                      ·
                        rfl

theorem cell23_5848853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_5848853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848853 prefixEnd_5848853 := by exact prefixLift 5848853
  have htrace : WordTrace (prefixWord ++ tailWord_5848853) baseStart_5848853 baseEnd_5848853 := by
    simpa [prefixWord, tailWord_5848853, baseEnd_5848853] using wordTrace_append hprefix tailTrace_5848853
  have hstable : (prefixWord ++ tailWord_5848853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848853).length < 2 ^ (prefixWord ++ tailWord_5848853).sum := by decide
  have hdescent : baseEnd_5848853 < baseStart_5848853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848869 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_5848869 : Nat := 118140960795 + 5848869 * 2 ^ 59
def prefixEnd_5848869 : Nat := 4983230072969 + 3 ^ 40 * 5848869 * 2
def baseEnd_5848869 : Nat := 1001093694060660668946349

theorem tailTrace_5848869 : CollatzResearch.WordTrace tailWord_5848869 prefixEnd_5848869 1001093694060660668946349 := by
  unfold tailWord_5848869
  simp only [CollatzResearch.WordTrace]
  refine ⟨213325777847553995143237661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142217185231702663428825107 213325777847553995143237661)
  ·
    refine ⟨79997166692832748178714123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213325777847553995143237661 79997166692832748178714123)
    ·
      refine ⟨119995750039249122268071185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79997166692832748178714123 119995750039249122268071185)
      ·
        refine ⟨89996812529436841701053389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119995750039249122268071185 89996812529436841701053389)
        ·
          refine ⟨33748804698538815637895021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89996812529436841701053389 33748804698538815637895021)
          ·
            refine ⟨12655801761952055864210633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33748804698538815637895021 12655801761952055864210633)
            ·
              refine ⟨9491851321464041898157975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12655801761952055864210633 9491851321464041898157975)
              ·
                refine ⟨14237776982196062847236963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9491851321464041898157975 14237776982196062847236963)
                ·
                  refine ⟨21356665473294094270855445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14237776982196062847236963 21356665473294094270855445)
                  ·
                    refine ⟨1001093694060660668946349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21356665473294094270855445 1001093694060660668946349)
                    ·
                      rfl

theorem cell23_5848869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_5848869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848869 prefixEnd_5848869 := by exact prefixLift 5848869
  have htrace : WordTrace (prefixWord ++ tailWord_5848869) baseStart_5848869 baseEnd_5848869 := by
    simpa [prefixWord, tailWord_5848869, baseEnd_5848869] using wordTrace_append hprefix tailTrace_5848869
  have hstable : (prefixWord ++ tailWord_5848869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848869).length < 2 ^ (prefixWord ++ tailWord_5848869).sum := by decide
  have hdescent : baseEnd_5848869 < baseStart_5848869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848876 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 5, 2, 2]
def baseStart_5848876 : Nat := 118140960795 + 5848876 * 2 ^ 59
def prefixEnd_5848876 : Nat := 4983230072969 + 3 ^ 40 * 5848876 * 2
def baseEnd_5848876 : Nat := 3003284676546563479451515

theorem tailTrace_5848876 : CollatzResearch.WordTrace tailWord_5848876 prefixEnd_5848876 3003284676546563479451515 := by
  unfold tailWord_5848876
  simp only [CollatzResearch.WordTrace]
  refine ⟨106663016579264317669371241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142217355439019090225828321 106663016579264317669371241)
  ·
    refine ⟨79997262434448238252028431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106663016579264317669371241 79997262434448238252028431)
    ·
      refine ⟨119995893651672357378042647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79997262434448238252028431 119995893651672357378042647)
      ·
        refine ⟨179993840477508536067063971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119995893651672357378042647 179993840477508536067063971)
        ·
          refine ⟨269990760716262804100595957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179993840477508536067063971 269990760716262804100595957)
          ·
            refine ⟨25311633817149637884430871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 269990760716262804100595957 25311633817149637884430871)
            ·
              refine ⟨37967450725724456826646307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25311633817149637884430871 37967450725724456826646307)
              ·
                refine ⟨56951176088586685239969461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37967450725724456826646307 56951176088586685239969461)
                ·
                  refine ⟨5339172758305001741247137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56951176088586685239969461 5339172758305001741247137)
                  ·
                    refine ⟨4004379568728751305935353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5339172758305001741247137 4004379568728751305935353)
                    ·
                      refine ⟨3003284676546563479451515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4004379568728751305935353 3003284676546563479451515)
                      ·
                        rfl

theorem cell23_5848876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_5848876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848876 prefixEnd_5848876 := by exact prefixLift 5848876
  have htrace : WordTrace (prefixWord ++ tailWord_5848876) baseStart_5848876 baseEnd_5848876 := by
    simpa [prefixWord, tailWord_5848876, baseEnd_5848876] using wordTrace_append hprefix tailTrace_5848876
  have hstable : (prefixWord ++ tailWord_5848876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848876).length < 2 ^ (prefixWord ++ tailWord_5848876).sum := by decide
  have hdescent : baseEnd_5848876 < baseStart_5848876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848886 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5848886 : Nat := 118140960795 + 5848886 * 2 ^ 59
def prefixEnd_5848886 : Nat := 4983230072969 + 3 ^ 40 * 5848886 * 2
def baseEnd_5848886 : Nat := 1001096603784369480108823

theorem tailTrace_5848886 : CollatzResearch.WordTrace tailWord_5848886 prefixEnd_5848886 1001096603784369480108823 := by
  unfold tailWord_5848886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13332899868030775440412907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142217598592328271364404341 13332899868030775440412907)
  ·
    refine ⟨19999349802046163160619361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13332899868030775440412907 19999349802046163160619361)
    ·
      refine ⟨14999512351534622370464521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19999349802046163160619361 14999512351534622370464521)
      ·
        refine ⟨11249634263650966777848391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14999512351534622370464521 11249634263650966777848391)
        ·
          refine ⟨16874451395476450166772587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11249634263650966777848391 16874451395476450166772587)
          ·
            refine ⟨25311677093214675250158881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16874451395476450166772587 25311677093214675250158881)
            ·
              refine ⟨18983757819911006437619161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25311677093214675250158881 18983757819911006437619161)
              ·
                refine ⟨14237818364933254828214371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18983757819911006437619161 14237818364933254828214371)
                ·
                  refine ⟨21356727547399882242321557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14237818364933254828214371 21356727547399882242321557)
                  ·
                    refine ⟨1001096603784369480108823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21356727547399882242321557 1001096603784369480108823)
                    ·
                      rfl

theorem cell23_5848886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5848886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848886 prefixEnd_5848886 := by exact prefixLift 5848886
  have htrace : WordTrace (prefixWord ++ tailWord_5848886) baseStart_5848886 baseEnd_5848886 := by
    simpa [prefixWord, tailWord_5848886, baseEnd_5848886] using wordTrace_append hprefix tailTrace_5848886
  have hstable : (prefixWord ++ tailWord_5848886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848886).length < 2 ^ (prefixWord ++ tailWord_5848886).sum := by decide
  have hdescent : baseEnd_5848886 < baseStart_5848886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848893 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5848893 : Nat := 118140960795 + 5848893 * 2 ^ 59
def prefixEnd_5848893 : Nat := 4983230072969 + 3 ^ 40 * 5848893 * 2
def baseEnd_5848893 : Nat := 3003293405717689912938937

theorem tailTrace_5848893 : CollatzResearch.WordTrace tailWord_5848893 prefixEnd_5848893 3003293405717689912938937 := by
  unfold tailWord_5848893
  simp only [CollatzResearch.WordTrace]
  refine ⟨213326653199467047242111333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142217768799644698161407555 213326653199467047242111333)
  ·
    refine ⟨39998747474900071357895875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213326653199467047242111333 39998747474900071357895875)
    ·
      refine ⟨59998121212350107036843813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39998747474900071357895875 59998121212350107036843813)
      ·
        refine ⟨11249647727315645069408215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59998121212350107036843813 11249647727315645069408215)
        ·
          refine ⟨16874471590973467604112323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11249647727315645069408215 16874471590973467604112323)
          ·
            refine ⟨25311707386460201406168485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16874471590973467604112323 25311707386460201406168485)
            ·
              refine ⟨4745945134961287763656591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25311707386460201406168485 4745945134961287763656591)
              ·
                refine ⟨7118917702441931645484887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745945134961287763656591 7118917702441931645484887)
                ·
                  refine ⟨10678376553662897468227331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7118917702441931645484887 10678376553662897468227331)
                  ·
                    refine ⟨16017564830494346202340997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10678376553662897468227331 16017564830494346202340997)
                    ·
                      refine ⟨3003293405717689912938937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16017564830494346202340997 3003293405717689912938937)
                      ·
                        rfl

theorem cell23_5848893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5848893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848893 prefixEnd_5848893 := by exact prefixLift 5848893
  have htrace : WordTrace (prefixWord ++ tailWord_5848893) baseStart_5848893 baseEnd_5848893 := by
    simpa [prefixWord, tailWord_5848893, baseEnd_5848893] using wordTrace_append hprefix tailTrace_5848893
  have hstable : (prefixWord ++ tailWord_5848893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848893).length < 2 ^ (prefixWord ++ tailWord_5848893).sum := by decide
  have hdescent : baseEnd_5848893 < baseStart_5848893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848969 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 3]
def baseStart_5848969 : Nat := 118140960795 + 5848969 * 2 ^ 59
def prefixEnd_5848969 : Nat := 4983230072969 + 3 ^ 40 * 5848969 * 2
def baseEnd_5848969 : Nat := 3003332430247431615588587

theorem tailTrace_5848969 : CollatzResearch.WordTrace tailWord_5848969 prefixEnd_5848969 3003332430247431615588587 := by
  unfold tailWord_5848969
  simp only [CollatzResearch.WordTrace]
  refine ⟨213329425147191712221877961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142219616764794474814585307 213329425147191712221877961)
  ·
    refine ⟨159997068860393784166408471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213329425147191712221877961 159997068860393784166408471)
    ·
      refine ⟨239995603290590676249612707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159997068860393784166408471 239995603290590676249612707)
      ·
        refine ⟨359993404935886014374419061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239995603290590676249612707 359993404935886014374419061)
        ·
          refine ⟨33749381712739313847601787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 359993404935886014374419061 33749381712739313847601787)
          ·
            refine ⟨50624072569108970771402681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33749381712739313847601787 50624072569108970771402681)
            ·
              refine ⟨37968054426831728078552011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50624072569108970771402681 37968054426831728078552011)
              ·
                refine ⟨56952081640247592117828017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37968054426831728078552011 56952081640247592117828017)
                ·
                  refine ⟨42714061230185694088371013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56952081640247592117828017 42714061230185694088371013)
                  ·
                    refine ⟨8008886480659817641569565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42714061230185694088371013 8008886480659817641569565)
                    ·
                      refine ⟨3003332430247431615588587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008886480659817641569565 3003332430247431615588587)
                      ·
                        rfl

theorem cell23_5848969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_5848969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848969 prefixEnd_5848969 := by exact prefixLift 5848969
  have htrace : WordTrace (prefixWord ++ tailWord_5848969) baseStart_5848969 baseEnd_5848969 := by
    simpa [prefixWord, tailWord_5848969, baseEnd_5848969] using wordTrace_append hprefix tailTrace_5848969
  have hstable : (prefixWord ++ tailWord_5848969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848969).length < 2 ^ (prefixWord ++ tailWord_5848969).sum := by decide
  have hdescent : baseEnd_5848969 < baseStart_5848969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849039 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_5849039 : Nat := 118140960795 + 5849039 * 2 ^ 59
def prefixEnd_5849039 : Nat := 4983230072969 + 3 ^ 40 * 5849039 * 2
def baseEnd_5849039 : Nat := 3003368373893246341713265

theorem tailTrace_5849039 : CollatzResearch.WordTrace tailWord_5849039 prefixEnd_5849039 3003368373893246341713265 := by
  unfold tailWord_5849039
  simp only [CollatzResearch.WordTrace]
  refine ⟨213331978256938114176926171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142221318837958742784617447 213331978256938114176926171)
  ·
    refine ⟨319997967385407171265389257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213331978256938114176926171 319997967385407171265389257)
    ·
      refine ⟨239998475539055378449041943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319997967385407171265389257 239998475539055378449041943)
      ·
        refine ⟨359997713308583067673562915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239998475539055378449041943 359997713308583067673562915)
        ·
          refine ⟨539996569962874601510344373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359997713308583067673562915 539996569962874601510344373)
          ·
            refine ⟨50624678434019493891594785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 539996569962874601510344373 50624678434019493891594785)
            ·
              refine ⟨37968508825514620418696089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50624678434019493891594785 37968508825514620418696089)
              ·
                refine ⟨28476381619135965314022067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37968508825514620418696089 28476381619135965314022067)
                ·
                  refine ⟨42714572428703947971033101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28476381619135965314022067 42714572428703947971033101)
                  ·
                    refine ⟨16017964660763980489137413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42714572428703947971033101 16017964660763980489137413)
                    ·
                      refine ⟨3003368373893246341713265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16017964660763980489137413 3003368373893246341713265)
                      ·
                        rfl

theorem cell23_5849039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_5849039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849039 prefixEnd_5849039 := by exact prefixLift 5849039
  have htrace : WordTrace (prefixWord ++ tailWord_5849039) baseStart_5849039 baseEnd_5849039 := by
    simpa [prefixWord, tailWord_5849039, baseEnd_5849039] using wordTrace_append hprefix tailTrace_5849039
  have hstable : (prefixWord ++ tailWord_5849039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849039).length < 2 ^ (prefixWord ++ tailWord_5849039).sum := by decide
  have hdescent : baseEnd_5849039 < baseStart_5849039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849066 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_5849066 : Nat := 118140960795 + 5849066 * 2 ^ 59
def prefixEnd_5849066 : Nat := 4983230072969 + 3 ^ 40 * 5849066 * 2
def baseEnd_5849066 : Nat := 1001127412623639245358547

theorem tailTrace_5849066 : CollatzResearch.WordTrace tailWord_5849066 prefixEnd_5849066 1001127412623639245358547 := by
  unfold tailWord_5849066
  simp only [CollatzResearch.WordTrace]
  refine ⟨53333240756960074447039763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142221975351893531858772701 53333240756960074447039763)
  ·
    refine ⟨79999861135440111670559645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53333240756960074447039763 79999861135440111670559645)
    ·
      refine ⟨29999947925790041876459867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79999861135440111670559645 29999947925790041876459867)
      ·
        refine ⟨44999921888685062814689801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29999947925790041876459867 44999921888685062814689801)
        ·
          refine ⟨33749941416513797111017351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44999921888685062814689801 33749941416513797111017351)
          ·
            refine ⟨50624912124770695666526027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33749941416513797111017351 50624912124770695666526027)
            ·
              refine ⟨75937368187156043499789041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50624912124770695666526027 75937368187156043499789041)
              ·
                refine ⟨56953026140367032624841781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75937368187156043499789041 56953026140367032624841781)
                ·
                  refine ⟨5339346200659409308578917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56953026140367032624841781 5339346200659409308578917)
                  ·
                    refine ⟨1001127412623639245358547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5339346200659409308578917 1001127412623639245358547)
                    ·
                      rfl

theorem cell23_5849066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_5849066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849066 prefixEnd_5849066 := by exact prefixLift 5849066
  have htrace : WordTrace (prefixWord ++ tailWord_5849066) baseStart_5849066 baseEnd_5849066 := by
    simpa [prefixWord, tailWord_5849066, baseEnd_5849066] using wordTrace_append hprefix tailTrace_5849066
  have hstable : (prefixWord ++ tailWord_5849066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849066).length < 2 ^ (prefixWord ++ tailWord_5849066).sum := by decide
  have hdescent : baseEnd_5849066 < baseStart_5849066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849083 : List Nat := [1, 1, 1, 1, 1, 3, 6, 4, 1, 4]
def baseStart_5849083 : Nat := 118140960795 + 5849083 * 2 ^ 59
def prefixEnd_5849083 : Nat := 4983230072969 + 3 ^ 40 * 5849083 * 2
def baseEnd_5849083 : Nat := 1001130322347348056521021

theorem tailTrace_5849083 : CollatzResearch.WordTrace tailWord_5849083 prefixEnd_5849083 1001130322347348056521021 := by
  unfold tailWord_5849083
  simp only [CollatzResearch.WordTrace]
  refine ⟨213333583068778709691527903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142222388712519139794351935 213333583068778709691527903)
  ·
    refine ⟨320000374603168064537291855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213333583068778709691527903 320000374603168064537291855)
    ·
      refine ⟨480000561904752096805937783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320000374603168064537291855 480000561904752096805937783)
      ·
        refine ⟨720000842857128145208906675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480000561904752096805937783 720000842857128145208906675)
        ·
          refine ⟨1080001264285692217813360013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720000842857128145208906675 1080001264285692217813360013)
          ·
            refine ⟨405000474107134581680010005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1080001264285692217813360013 405000474107134581680010005)
            ·
              refine ⟨18984397223771933516250469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 405000474107134581680010005 18984397223771933516250469)
              ·
                refine ⟨3559574479457237534296963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18984397223771933516250469 3559574479457237534296963)
                ·
                  refine ⟨5339361719185856301445445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559574479457237534296963 5339361719185856301445445)
                  ·
                    refine ⟨1001130322347348056521021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5339361719185856301445445 1001130322347348056521021)
                    ·
                      rfl

theorem cell23_5849083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 4].length) (baseStart_5849083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849083 prefixEnd_5849083 := by exact prefixLift 5849083
  have htrace : WordTrace (prefixWord ++ tailWord_5849083) baseStart_5849083 baseEnd_5849083 := by
    simpa [prefixWord, tailWord_5849083, baseEnd_5849083] using wordTrace_append hprefix tailTrace_5849083
  have hstable : (prefixWord ++ tailWord_5849083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849083).length < 2 ^ (prefixWord ++ tailWord_5849083).sum := by decide
  have hdescent : baseEnd_5849083 < baseStart_5849083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849099 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6]
def baseStart_5849099 : Nat := 118140960795 + 5849099 * 2 ^ 59
def prefixEnd_5849099 : Nat := 4983230072969 + 3 ^ 40 * 5849099 * 2
def baseEnd_5849099 : Nat := 3003399182732516106962989

theorem tailTrace_5849099 : CollatzResearch.WordTrace tailWord_5849099 prefixEnd_5849099 3003399182732516106962989 := by
  unfold tailWord_5849099
  simp only [CollatzResearch.WordTrace]
  refine ⟨213334166636720744424110351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142222777757813829616073567 213334166636720744424110351)
  ·
    refine ⟨320001249955081116636165527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213334166636720744424110351 320001249955081116636165527)
    ·
      refine ⟨480001874932621674954248291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320001249955081116636165527 480001874932621674954248291)
      ·
        refine ⟨720002812398932512431372437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480001874932621674954248291 720002812398932512431372437)
        ·
          refine ⟨33750131831199961520220583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 720002812398932512431372437 33750131831199961520220583)
          ·
            refine ⟨50625197746799942280330875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33750131831199961520220583 50625197746799942280330875)
            ·
              refine ⟨75937796620199913420496313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50625197746799942280330875 75937796620199913420496313)
              ·
                refine ⟨56953347465149935065372235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75937796620199913420496313 56953347465149935065372235)
                ·
                  refine ⟨85430021197724902598058353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56953347465149935065372235 85430021197724902598058353)
                  ·
                    refine ⟨64072515898293676948543765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85430021197724902598058353 64072515898293676948543765)
                    ·
                      refine ⟨3003399182732516106962989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64072515898293676948543765 3003399182732516106962989)
                      ·
                        rfl

theorem cell23_5849099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_5849099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849099 prefixEnd_5849099 := by exact prefixLift 5849099
  have htrace : WordTrace (prefixWord ++ tailWord_5849099) baseStart_5849099 baseEnd_5849099 := by
    simpa [prefixWord, tailWord_5849099, baseEnd_5849099] using wordTrace_append hprefix tailTrace_5849099
  have hstable : (prefixWord ++ tailWord_5849099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849099).length < 2 ^ (prefixWord ++ tailWord_5849099).sum := by decide
  have hdescent : baseEnd_5849099 < baseStart_5849099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849117 : List Nat := [1, 4, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_5849117 : Nat := 118140960795 + 5849117 * 2 ^ 59
def prefixEnd_5849117 : Nat := 4983230072969 + 3 ^ 40 * 5849117 * 2
def baseEnd_5849117 : Nat := 1001136141794765678845969

theorem tailTrace_5849117 : CollatzResearch.WordTrace tailWord_5849117 prefixEnd_5849117 1001136141794765678845969 := by
  unfold tailWord_5849117
  simp only [CollatzResearch.WordTrace]
  refine ⟨213334823150655533498265605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142223215433770355665510403 213334823150655533498265605)
  ·
    refine ⟨40000279340747912530924801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213334823150655533498265605 40000279340747912530924801)
    ·
      refine ⟨30000209505560934398193601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40000279340747912530924801 30000209505560934398193601)
      ·
        refine ⟨22500157129170700798645201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30000209505560934398193601 22500157129170700798645201)
        ·
          refine ⟨16875117846878025598983901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22500157129170700798645201 16875117846878025598983901)
          ·
            refine ⟨6328169192579259599618963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16875117846878025598983901 6328169192579259599618963)
            ·
              refine ⟨9492253788868889399428445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328169192579259599618963 9492253788868889399428445)
              ·
                refine ⟨3559595170825833524785667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9492253788868889399428445 3559595170825833524785667)
                ·
                  refine ⟨5339392756238750287178501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559595170825833524785667 5339392756238750287178501)
                  ·
                    refine ⟨1001136141794765678845969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5339392756238750287178501 1001136141794765678845969)
                    ·
                      rfl

theorem cell23_5849117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_5849117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849117 prefixEnd_5849117 := by exact prefixLift 5849117
  have htrace : WordTrace (prefixWord ++ tailWord_5849117) baseStart_5849117 baseEnd_5849117 := by
    simpa [prefixWord, tailWord_5849117, baseEnd_5849117] using wordTrace_append hprefix tailTrace_5849117
  have hstable : (prefixWord ++ tailWord_5849117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849117).length < 2 ^ (prefixWord ++ tailWord_5849117).sum := by decide
  have hdescent : baseEnd_5849117 < baseStart_5849117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849129 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_5849129 : Nat := 118140960795 + 5849129 * 2 ^ 59
def prefixEnd_5849129 : Nat := 4983230072969 + 3 ^ 40 * 5849129 * 2
def baseEnd_5849129 : Nat := 3003414587152150989587851

theorem tailTrace_5849129 : CollatzResearch.WordTrace tailWord_5849129 prefixEnd_5849129 3003414587152150989587851 := by
  unfold tailWord_5849129
  simp only [CollatzResearch.WordTrace]
  refine ⟨213335260826612059547702441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142223507217741373031801627 213335260826612059547702441)
  ·
    refine ⟨160001445619959044660776831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213335260826612059547702441 160001445619959044660776831)
    ·
      refine ⟨240002168429938566991165247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160001445619959044660776831 240002168429938566991165247)
      ·
        refine ⟨360003252644907850486747871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240002168429938566991165247 360003252644907850486747871)
        ·
          refine ⟨540004878967361775730121807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360003252644907850486747871 540004878967361775730121807)
          ·
            refine ⟨810007318451042663595182711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540004878967361775730121807 810007318451042663595182711)
            ·
              refine ⟨1215010977676563995392774067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810007318451042663595182711 1215010977676563995392774067)
              ·
                refine ⟨1822516466514845993089161101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215010977676563995392774067 1822516466514845993089161101)
                ·
                  refine ⟨683443674943067247408435413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1822516466514845993089161101 683443674943067247408435413)
                  ·
                    refine ⟨16018211131478138611135205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 683443674943067247408435413 16018211131478138611135205)
                    ·
                      refine ⟨3003414587152150989587851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16018211131478138611135205 3003414587152150989587851)
                      ·
                        rfl

theorem cell23_5849129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_5849129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849129 prefixEnd_5849129 := by exact prefixLift 5849129
  have htrace : WordTrace (prefixWord ++ tailWord_5849129) baseStart_5849129 baseEnd_5849129 := by
    simpa [prefixWord, tailWord_5849129, baseEnd_5849129] using wordTrace_append hprefix tailTrace_5849129
  have hstable : (prefixWord ++ tailWord_5849129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849129).length < 2 ^ (prefixWord ++ tailWord_5849129).sum := by decide
  have hdescent : baseEnd_5849129 < baseStart_5849129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849146 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_5849146 : Nat := 118140960795 + 5849146 * 2 ^ 59
def prefixEnd_5849146 : Nat := 4983230072969 + 3 ^ 40 * 5849146 * 2
def baseEnd_5849146 : Nat := 3003423316323277423075273

theorem tailTrace_5849146 : CollatzResearch.WordTrace tailWord_5849146 prefixEnd_5849146 3003423316323277423075273 := by
  unfold tailWord_5849146
  simp only [CollatzResearch.WordTrace]
  refine ⟨53333970216887617862767823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142223920578366980967380861 53333970216887617862767823)
  ·
    refine ⟨80000955325331426794151735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53333970216887617862767823 80000955325331426794151735)
    ·
      refine ⟨120001432987997140191227603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80000955325331426794151735 120001432987997140191227603)
      ·
        refine ⟨180002149481995710286841405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120001432987997140191227603 180002149481995710286841405)
        ·
          refine ⟨67500806055748391357565527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180002149481995710286841405 67500806055748391357565527)
          ·
            refine ⟨101251209083622587036348291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67500806055748391357565527 101251209083622587036348291)
            ·
              refine ⟨151876813625433880554522437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101251209083622587036348291 151876813625433880554522437)
              ·
                refine ⟨28476902554768852603972957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151876813625433880554522437 28476902554768852603972957)
                ·
                  refine ⟨10678838458038319726489859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28476902554768852603972957 10678838458038319726489859)
                  ·
                    refine ⟨16018257687057479589734789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10678838458038319726489859 16018257687057479589734789)
                    ·
                      refine ⟨3003423316323277423075273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16018257687057479589734789 3003423316323277423075273)
                      ·
                        rfl

theorem cell23_5849146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_5849146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849146 prefixEnd_5849146 := by exact prefixLift 5849146
  have htrace : WordTrace (prefixWord ++ tailWord_5849146) baseStart_5849146 baseEnd_5849146 := by
    simpa [prefixWord, tailWord_5849146, baseEnd_5849146] using wordTrace_append hprefix tailTrace_5849146
  have hstable : (prefixWord ++ tailWord_5849146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849146).length < 2 ^ (prefixWord ++ tailWord_5849146).sum := by decide
  have hdescent : baseEnd_5849146 < baseStart_5849146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849176 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_5849176 : Nat := 118140960795 + 5849176 * 2 ^ 59
def prefixEnd_5849176 : Nat := 4983230072969 + 3 ^ 40 * 5849176 * 2
def baseEnd_5849176 : Nat := 3003438720742912305700135

theorem tailTrace_5849176 : CollatzResearch.WordTrace tailWord_5849176 prefixEnd_5849176 3003438720742912305700135 := by
  unfold tailWord_5849176
  simp only [CollatzResearch.WordTrace]
  refine ⟨106668487528720893287331691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142224650038294524383108921 106668487528720893287331691)
  ·
    refine ⟨160002731293081339930997537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106668487528720893287331691 160002731293081339930997537)
    ·
      refine ⟨120002048469811004948248153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160002731293081339930997537 120002048469811004948248153)
      ·
        refine ⟨90001536352358253711186115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120002048469811004948248153 90001536352358253711186115)
        ·
          refine ⟨135002304528537380566779173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90001536352358253711186115 135002304528537380566779173)
          ·
            refine ⟨25312932099100758856271095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135002304528537380566779173 25312932099100758856271095)
            ·
              refine ⟨37969398148651138284406643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25312932099100758856271095 37969398148651138284406643)
              ·
                refine ⟨56954097222976707426609965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37969398148651138284406643 56954097222976707426609965)
                ·
                  refine ⟨21357786458616265284978737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56954097222976707426609965 21357786458616265284978737)
                  ·
                    refine ⟨16018339843962198963734053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21357786458616265284978737 16018339843962198963734053)
                    ·
                      refine ⟨3003438720742912305700135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16018339843962198963734053 3003438720742912305700135)
                      ·
                        rfl

theorem cell23_5849176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_5849176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849176 prefixEnd_5849176 := by exact prefixLift 5849176
  have htrace : WordTrace (prefixWord ++ tailWord_5849176) baseStart_5849176 baseEnd_5849176 := by
    simpa [prefixWord, tailWord_5849176, baseEnd_5849176] using wordTrace_append hprefix tailTrace_5849176
  have hstable : (prefixWord ++ tailWord_5849176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849176).length < 2 ^ (prefixWord ++ tailWord_5849176).sum := by decide
  have hdescent : baseEnd_5849176 < baseStart_5849176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849186 : List Nat := [3, 3, 2, 2, 13]
def baseStart_5849186 : Nat := 118140960795 + 5849186 * 2 ^ 59
def prefixEnd_5849186 : Nat := 4983230072969 + 3 ^ 40 * 5849186 * 2
def baseEnd_5849186 : Nat := 4119950419135057978841

theorem tailTrace_5849186 : CollatzResearch.WordTrace tailWord_5849186 prefixEnd_5849186 4119950419135057978841 := by
  unfold tailWord_5849186
  simp only [CollatzResearch.WordTrace]
  refine ⟨53334334946851389570631853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142224893191603705521684941 53334334946851389570631853)
  ·
    refine ⟨20000375605069271088986945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53334334946851389570631853 20000375605069271088986945)
    ·
      refine ⟨15000281703801953316740209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20000375605069271088986945 15000281703801953316740209)
      ·
        refine ⟨11250211277851464987555157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15000281703801953316740209 11250211277851464987555157)
        ·
          refine ⟨4119950419135057978841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11250211277851464987555157 4119950419135057978841)
          ·
            rfl

theorem cell23_5849186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 13].length) (baseStart_5849186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849186 prefixEnd_5849186 := by exact prefixLift 5849186
  have htrace : WordTrace (prefixWord ++ tailWord_5849186) baseStart_5849186 baseEnd_5849186 := by
    simpa [prefixWord, tailWord_5849186, baseEnd_5849186] using wordTrace_append hprefix tailTrace_5849186
  have hstable : (prefixWord ++ tailWord_5849186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849186).length < 2 ^ (prefixWord ++ tailWord_5849186).sum := by decide
  have hdescent : baseEnd_5849186 < baseStart_5849186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849213 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_5849213 : Nat := 118140960795 + 5849213 * 2 ^ 59
def prefixEnd_5849213 : Nat := 4983230072969 + 3 ^ 40 * 5849213 * 2
def baseEnd_5849213 : Nat := 3003457719527128660937465

theorem tailTrace_5849213 : CollatzResearch.WordTrace tailWord_5849213 prefixEnd_5849213 3003457719527128660937465 := by
  unfold tailWord_5849213
  simp only [CollatzResearch.WordTrace]
  refine ⟨213338324558307741893760293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142225549705538494595840195 213338324558307741893760293)
  ·
    refine ⟨40000935854682701605080055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213338324558307741893760293 40000935854682701605080055)
    ·
      refine ⟨60001403782024052407620083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40000935854682701605080055 60001403782024052407620083)
      ·
        refine ⟨90002105673036078611430125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60001403782024052407620083 90002105673036078611430125)
        ·
          refine ⟨33750789627388529479286297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90002105673036078611430125 33750789627388529479286297)
          ·
            refine ⟨25313092220541397109464723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33750789627388529479286297 25313092220541397109464723)
            ·
              refine ⟨37969638330812095664197085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25313092220541397109464723 37969638330812095664197085)
              ·
                refine ⟨14238614374054535874073907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37969638330812095664197085 14238614374054535874073907)
                ·
                  refine ⟨21357921561081803811110861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14238614374054535874073907 21357921561081803811110861)
                  ·
                    refine ⟨8009220585405676429166573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21357921561081803811110861 8009220585405676429166573)
                    ·
                      refine ⟨3003457719527128660937465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8009220585405676429166573 3003457719527128660937465)
                      ·
                        rfl

theorem cell23_5849213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_5849213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849213 prefixEnd_5849213 := by exact prefixLift 5849213
  have htrace : WordTrace (prefixWord ++ tailWord_5849213) baseStart_5849213 baseEnd_5849213 := by
    simpa [prefixWord, tailWord_5849213, baseEnd_5849213] using wordTrace_append hprefix tailTrace_5849213
  have hstable : (prefixWord ++ tailWord_5849213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849213).length < 2 ^ (prefixWord ++ tailWord_5849213).sum := by decide
  have hdescent : baseEnd_5849213 < baseStart_5849213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849247 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5849247 : Nat := 118140960795 + 5849247 * 2 ^ 59
def prefixEnd_5849247 : Nat := 4983230072969 + 3 ^ 40 * 5849247 * 2
def baseEnd_5849247 : Nat := 3003475177869381527912309

theorem tailTrace_5849247 : CollatzResearch.WordTrace tailWord_5849247 prefixEnd_5849247 3003475177869381527912309 := by
  unfold tailWord_5849247
  simp only [CollatzResearch.WordTrace]
  refine ⟨213339564640184565700497995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142226376426789710466998663 213339564640184565700497995)
  ·
    refine ⟨320009346960276848550746993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213339564640184565700497995 320009346960276848550746993)
    ·
      refine ⟨240007010220207636413060245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320009346960276848550746993 240007010220207636413060245)
      ·
        refine ⟨11250328604072232956862199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 240007010220207636413060245 11250328604072232956862199)
        ·
          refine ⟨16875492906108349435293299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11250328604072232956862199 16875492906108349435293299)
          ·
            refine ⟨25313239359162524152939949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16875492906108349435293299 25313239359162524152939949)
            ·
              refine ⟨9492464759685946557352481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25313239359162524152939949 9492464759685946557352481)
              ·
                refine ⟨7119348569764459918014361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9492464759685946557352481 7119348569764459918014361)
                ·
                  refine ⟨5339511427323344938510771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7119348569764459918014361 5339511427323344938510771)
                  ·
                    refine ⟨8009267140985017407766157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5339511427323344938510771 8009267140985017407766157)
                    ·
                      refine ⟨3003475177869381527912309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8009267140985017407766157 3003475177869381527912309)
                      ·
                        rfl

theorem cell23_5849247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5849247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849247 prefixEnd_5849247 := by exact prefixLift 5849247
  have htrace : WordTrace (prefixWord ++ tailWord_5849247) baseStart_5849247 baseEnd_5849247 := by
    simpa [prefixWord, tailWord_5849247, baseEnd_5849247] using wordTrace_append hprefix tailTrace_5849247
  have hstable : (prefixWord ++ tailWord_5849247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849247).length < 2 ^ (prefixWord ++ tailWord_5849247).sum := by decide
  have hdescent : baseEnd_5849247 < baseStart_5849247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849336 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 2, 8]
def baseStart_5849336 : Nat := 118140960795 + 5849336 * 2 ^ 59
def prefixEnd_5849336 : Nat := 4983230072969 + 3 ^ 40 * 5849336 * 2
def baseEnd_5849336 : Nat := 1001173625882543893233133

theorem tailTrace_5849336 : CollatzResearch.WordTrace tailWord_5849336 prefixEnd_5849336 1001173625882543893233133 := by
  unfold tailWord_5849336
  simp only [CollatzResearch.WordTrace]
  refine ⟨106671405368431066950243931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142228540491241422600325241 106671405368431066950243931)
  ·
    refine ⟨160007108052646600425365897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106671405368431066950243931 160007108052646600425365897)
    ·
      refine ⟨120005331039484950319024423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160007108052646600425365897 120005331039484950319024423)
      ·
        refine ⟨180007996559227425478536635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120005331039484950319024423 180007996559227425478536635)
        ·
          refine ⟨270011994838841138217804953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180007996559227425478536635 270011994838841138217804953)
          ·
            refine ⟨202508996129130853663353715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270011994838841138217804953 202508996129130853663353715)
            ·
              refine ⟨303763494193696280495030573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202508996129130853663353715 303763494193696280495030573)
              ·
                refine ⟨113911310322636105185636465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303763494193696280495030573 113911310322636105185636465)
                ·
                  refine ⟨85433482741977078889227349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113911310322636105185636465 85433482741977078889227349)
                  ·
                    refine ⟨1001173625882543893233133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85433482741977078889227349 1001173625882543893233133)
                    ·
                      rfl

theorem cell23_5849336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_5849336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849336 prefixEnd_5849336 := by exact prefixLift 5849336
  have htrace : WordTrace (prefixWord ++ tailWord_5849336) baseStart_5849336 baseEnd_5849336 := by
    simpa [prefixWord, tailWord_5849336, baseEnd_5849336] using wordTrace_append hprefix tailTrace_5849336
  have hstable : (prefixWord ++ tailWord_5849336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849336).length < 2 ^ (prefixWord ++ tailWord_5849336).sum := by decide
  have hdescent : baseEnd_5849336 < baseStart_5849336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849340 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_5849340 : Nat := 118140960795 + 5849340 * 2 ^ 59
def prefixEnd_5849340 : Nat := 4983230072969 + 3 ^ 40 * 5849340 * 2
def baseEnd_5849340 : Nat := 1001174310523416554683127

theorem tailTrace_5849340 : CollatzResearch.WordTrace tailWord_5849340 prefixEnd_5849340 1001174310523416554683127 := by
  unfold tailWord_5849340
  simp only [CollatzResearch.WordTrace]
  refine ⟨106671478314423821291816737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142228637752565095055755649 106671478314423821291816737)
  ·
    refine ⟨80003608735817865968862553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106671478314423821291816737 80003608735817865968862553)
    ·
      refine ⟨60002706551863399476646915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80003608735817865968862553 60002706551863399476646915)
      ·
        refine ⟨90004059827795099214970373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60002706551863399476646915 90004059827795099214970373)
        ·
          refine ⟨16875761217711581102806945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90004059827795099214970373 16875761217711581102806945)
          ·
            refine ⟨12656820913283685827105209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16875761217711581102806945 12656820913283685827105209)
            ·
              refine ⟨9492615684962764370328907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12656820913283685827105209 9492615684962764370328907)
              ·
                refine ⟨14238923527444146555493361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492615684962764370328907 14238923527444146555493361)
                ·
                  refine ⟨10679192645583109916620021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14238923527444146555493361 10679192645583109916620021)
                  ·
                    refine ⟨1001174310523416554683127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10679192645583109916620021 1001174310523416554683127)
                    ·
                      rfl

theorem cell23_5849340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_5849340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849340 prefixEnd_5849340 := by exact prefixLift 5849340
  have htrace : WordTrace (prefixWord ++ tailWord_5849340) baseStart_5849340 baseEnd_5849340 := by
    simpa [prefixWord, tailWord_5849340, baseEnd_5849340] using wordTrace_append hprefix tailTrace_5849340
  have hstable : (prefixWord ++ tailWord_5849340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849340).length < 2 ^ (prefixWord ++ tailWord_5849340).sum := by decide
  have hdescent : baseEnd_5849340 < baseStart_5849340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849394 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_5849394 : Nat := 118140960795 + 5849394 * 2 ^ 59
def prefixEnd_5849394 : Nat := 4983230072969 + 3 ^ 40 * 5849394 * 2
def baseEnd_5849394 : Nat := 3003550659525592452774133

theorem tailTrace_5849394 : CollatzResearch.WordTrace tailWord_5849394 prefixEnd_5849394 3003550659525592452774133 := by
  unfold tailWord_5849394
  simp only [CollatzResearch.WordTrace]
  refine ⟨53336231542663002451524809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142229950780434673204066157 53336231542663002451524809)
  ·
    refine ⟨40002173656997251838643607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53336231542663002451524809 40002173656997251838643607)
    ·
      refine ⟨60003260485495877757965411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40002173656997251838643607 60003260485495877757965411)
      ·
        refine ⟨90004890728243816636948117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60003260485495877757965411 90004890728243816636948117)
        ·
          refine ⟨4218979252886428904856943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90004890728243816636948117 4218979252886428904856943)
          ·
            refine ⟨6328468879329643357285415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218979252886428904856943 6328468879329643357285415)
            ·
              refine ⟨9492703318994465035928123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328468879329643357285415 9492703318994465035928123)
              ·
                refine ⟨14239054978491697553892185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492703318994465035928123 14239054978491697553892185)
                ·
                  refine ⟨10679291233868773165419139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14239054978491697553892185 10679291233868773165419139)
                  ·
                    refine ⟨16018936850803159748128709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10679291233868773165419139 16018936850803159748128709)
                    ·
                      refine ⟨3003550659525592452774133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16018936850803159748128709 3003550659525592452774133)
                      ·
                        rfl

theorem cell23_5849394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_5849394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849394 prefixEnd_5849394 := by exact prefixLift 5849394
  have htrace : WordTrace (prefixWord ++ tailWord_5849394) baseStart_5849394 baseEnd_5849394 := by
    simpa [prefixWord, tailWord_5849394, baseEnd_5849394] using wordTrace_append hprefix tailTrace_5849394
  have hstable : (prefixWord ++ tailWord_5849394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849394).length < 2 ^ (prefixWord ++ tailWord_5849394).sum := by decide
  have hdescent : baseEnd_5849394 < baseStart_5849394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849447 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 1, 5]
def baseStart_5849447 : Nat := 118140960795 + 5849447 * 2 ^ 59
def prefixEnd_5849447 : Nat := 4983230072969 + 3 ^ 40 * 5849447 * 2
def baseEnd_5849447 : Nat := 1001192624666760248470463

theorem tailTrace_5849447 : CollatzResearch.WordTrace tailWord_5849447 prefixEnd_5849447 1001192624666760248470463 := by
  unfold tailWord_5849447
  simp only [CollatzResearch.WordTrace]
  refine ⟨213346859239459999857778595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142231239492973333238519063 213346859239459999857778595)
  ·
    refine ⟨320020288859189999786667893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213346859239459999857778595 320020288859189999786667893)
    ·
      refine ⟨30001902080549062480000115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320020288859189999786667893 30001902080549062480000115)
      ·
        refine ⟨45002853120823593720000173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30001902080549062480000115 45002853120823593720000173)
        ·
          refine ⟨16876069920308847645000065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45002853120823593720000173 16876069920308847645000065)
          ·
            refine ⟨12657052440231635733750049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16876069920308847645000065 12657052440231635733750049)
            ·
              refine ⟨9492789330173726800312537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12657052440231635733750049 9492789330173726800312537)
              ·
                refine ⟨7119591997630295100234403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9492789330173726800312537 7119591997630295100234403)
                ·
                  refine ⟨10679387996445442650351605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7119591997630295100234403 10679387996445442650351605)
                  ·
                    refine ⟨1001192624666760248470463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10679387996445442650351605 1001192624666760248470463)
                    ·
                      rfl

theorem cell23_5849447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_5849447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849447 prefixEnd_5849447 := by exact prefixLift 5849447
  have htrace : WordTrace (prefixWord ++ tailWord_5849447) baseStart_5849447 baseEnd_5849447 := by
    simpa [prefixWord, tailWord_5849447, baseEnd_5849447] using wordTrace_append hprefix tailTrace_5849447
  have hstable : (prefixWord ++ tailWord_5849447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849447).length < 2 ^ (prefixWord ++ tailWord_5849447).sum := by decide
  have hdescent : baseEnd_5849447 < baseStart_5849447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849461 : List Nat := [1, 3, 4, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_5849461 : Nat := 118140960795 + 5849461 * 2 ^ 59
def prefixEnd_5849461 : Nat := 4983230072969 + 3 ^ 40 * 5849461 * 2
def baseEnd_5849461 : Nat := 3003585062729443690636325

theorem tailTrace_5849461 : CollatzResearch.WordTrace tailWord_5849461 prefixEnd_5849461 3003585062729443690636325 := by
  unfold tailWord_5849461
  simp only [CollatzResearch.WordTrace]
  refine ⟨213347369861409280248788237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142231579907606186832525491 213347369861409280248788237)
  ·
    refine ⟨80005263698028480093295589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213347369861409280248788237 80005263698028480093295589)
    ·
      refine ⟨15000986943380340017492923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80005263698028480093295589 15000986943380340017492923)
      ·
        refine ⟨22501480415070510026239385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15000986943380340017492923 22501480415070510026239385)
        ·
          refine ⟨16876110311302882519679539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22501480415070510026239385 16876110311302882519679539)
          ·
            refine ⟨25314165466954323779519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16876110311302882519679539 25314165466954323779519309)
            ·
              refine ⟨9492812050107871417319741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25314165466954323779519309 9492812050107871417319741)
              ·
                refine ⟨3559804518790451781494903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9492812050107871417319741 3559804518790451781494903)
                ·
                  refine ⟨5339706778185677672242355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559804518790451781494903 5339706778185677672242355)
                  ·
                    refine ⟨8009560167278516508363533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5339706778185677672242355 8009560167278516508363533)
                    ·
                      refine ⟨3003585062729443690636325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8009560167278516508363533 3003585062729443690636325)
                      ·
                        rfl

theorem cell23_5849461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_5849461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849461 prefixEnd_5849461 := by exact prefixLift 5849461
  have htrace : WordTrace (prefixWord ++ tailWord_5849461) baseStart_5849461 baseEnd_5849461 := by
    simpa [prefixWord, tailWord_5849461, baseEnd_5849461] using wordTrace_append hprefix tailTrace_5849461
  have hstable : (prefixWord ++ tailWord_5849461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849461).length < 2 ^ (prefixWord ++ tailWord_5849461).sum := by decide
  have hdescent : baseEnd_5849461 < baseStart_5849461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849484 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 3, 2, 2]
def baseStart_5849484 : Nat := 118140960795 + 5849484 * 2 ^ 59
def prefixEnd_5849484 : Nat := 4983230072969 + 3 ^ 40 * 5849484 * 2
def baseEnd_5849484 : Nat := 3003596872784497100648719

theorem tailTrace_5849484 : CollatzResearch.WordTrace tailWord_5849484 prefixEnd_5849484 3003596872784497100648719 := by
  unfold tailWord_5849484
  simp only [CollatzResearch.WordTrace]
  refine ⟨106674104370162977588437753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142232139160217303451250337 106674104370162977588437753)
  ·
    refine ⟨80005578277622233191328315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106674104370162977588437753 80005578277622233191328315)
    ·
      refine ⟨120008367416433349786992473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80005578277622233191328315 120008367416433349786992473)
      ·
        refine ⟨90006275562325012340244355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120008367416433349786992473 90006275562325012340244355)
        ·
          refine ⟨135009413343487518510366533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90006275562325012340244355 135009413343487518510366533)
          ·
            refine ⟨25314265001903909720693725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135009413343487518510366533 25314265001903909720693725)
            ·
              refine ⟨9492849375713966145260147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25314265001903909720693725 9492849375713966145260147)
              ·
                refine ⟨14239274063570949217890221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492849375713966145260147 14239274063570949217890221)
                ·
                  refine ⟨5339727773839105956708833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14239274063570949217890221 5339727773839105956708833)
                  ·
                    refine ⟨4004795830379329467531625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5339727773839105956708833 4004795830379329467531625)
                    ·
                      refine ⟨3003596872784497100648719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4004795830379329467531625 3003596872784497100648719)
                      ·
                        rfl

theorem cell23_5849484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_5849484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849484 prefixEnd_5849484 := by exact prefixLift 5849484
  have htrace : WordTrace (prefixWord ++ tailWord_5849484) baseStart_5849484 baseEnd_5849484 := by
    simpa [prefixWord, tailWord_5849484, baseEnd_5849484] using wordTrace_append hprefix tailTrace_5849484
  have hstable : (prefixWord ++ tailWord_5849484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849484).length < 2 ^ (prefixWord ++ tailWord_5849484).sum := by decide
  have hdescent : baseEnd_5849484 < baseStart_5849484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849493 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_5849493 : Nat := 118140960795 + 5849493 * 2 ^ 59
def prefixEnd_5849493 : Nat := 4983230072969 + 3 ^ 40 * 5849493 * 2
def baseEnd_5849493 : Nat := 3003601494110387565436177

theorem tailTrace_5849493 : CollatzResearch.WordTrace tailWord_5849493 prefixEnd_5849493 3003601494110387565436177 := by
  unfold tailWord_5849493
  simp only [CollatzResearch.WordTrace]
  refine ⟨213348536997293349713953133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142232357998195566475968755 213348536997293349713953133)
  ·
    refine ⟨80005701373985006142732425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213348536997293349713953133 80005701373985006142732425)
    ·
      refine ⟨60004276030488754607049319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80005701373985006142732425 60004276030488754607049319)
      ·
        refine ⟨90006414045733131910573979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60004276030488754607049319 90006414045733131910573979)
        ·
          refine ⟨135009621068599697865860969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90006414045733131910573979 135009621068599697865860969)
          ·
            refine ⟨101257215801449773399395727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135009621068599697865860969 101257215801449773399395727)
            ·
              refine ⟨151885823702174660099093591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101257215801449773399395727 151885823702174660099093591)
              ·
                refine ⟨227828735553261990148640387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151885823702174660099093591 227828735553261990148640387)
                ·
                  refine ⟨341743103329892985222960581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227828735553261990148640387 341743103329892985222960581)
                  ·
                    refine ⟨64076831874354934729305109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341743103329892985222960581 64076831874354934729305109)
                    ·
                      refine ⟨3003601494110387565436177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64076831874354934729305109 3003601494110387565436177)
                      ·
                        rfl

theorem cell23_5849493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_5849493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849493 prefixEnd_5849493 := by exact prefixLift 5849493
  have htrace : WordTrace (prefixWord ++ tailWord_5849493) baseStart_5849493 baseEnd_5849493 := by
    simpa [prefixWord, tailWord_5849493, baseEnd_5849493] using wordTrace_append hprefix tailTrace_5849493
  have hstable : (prefixWord ++ tailWord_5849493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849493).length < 2 ^ (prefixWord ++ tailWord_5849493).sum := by decide
  have hdescent : baseEnd_5849493 < baseStart_5849493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849501 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_5849501 : Nat := 118140960795 + 5849501 * 2 ^ 59
def prefixEnd_5849501 : Nat := 4983230072969 + 3 ^ 40 * 5849501 * 2
def baseEnd_5849501 : Nat := 3003605601955623534136141

theorem tailTrace_5849501 : CollatzResearch.WordTrace tailWord_5849501 prefixEnd_5849501 3003605601955623534136141 := by
  unfold tailWord_5849501
  simp only [CollatzResearch.WordTrace]
  refine ⟨213348828781264367080244357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142232552520842911386829571 213348828781264367080244357)
  ·
    refine ⟨40002905396487068827545817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213348828781264367080244357 40002905396487068827545817)
    ·
      refine ⟨30002179047365301620659363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40002905396487068827545817 30002179047365301620659363)
      ·
        refine ⟨45003268571047952430989045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30002179047365301620659363 45003268571047952430989045)
        ·
          refine ⟨4219056428535745540405223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45003268571047952430989045 4219056428535745540405223)
          ·
            refine ⟨6328584642803618310607835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219056428535745540405223 6328584642803618310607835)
            ·
              refine ⟨9492876964205427465911753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328584642803618310607835 9492876964205427465911753)
              ·
                refine ⟨7119657723154070599433815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9492876964205427465911753 7119657723154070599433815)
                ·
                  refine ⟨10679486584731105899150723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7119657723154070599433815 10679486584731105899150723)
                  ·
                    refine ⟨16019229877096658848726085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10679486584731105899150723 16019229877096658848726085)
                    ·
                      refine ⟨3003605601955623534136141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16019229877096658848726085 3003605601955623534136141)
                      ·
                        rfl

theorem cell23_5849501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_5849501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849501 prefixEnd_5849501 := by exact prefixLift 5849501
  have htrace : WordTrace (prefixWord ++ tailWord_5849501) baseStart_5849501 baseEnd_5849501 := by
    simpa [prefixWord, tailWord_5849501, baseEnd_5849501] using wordTrace_append hprefix tailTrace_5849501
  have hstable : (prefixWord ++ tailWord_5849501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849501).length < 2 ^ (prefixWord ++ tailWord_5849501).sum := by decide
  have hdescent : baseEnd_5849501 < baseStart_5849501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849504 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3]
def baseStart_5849504 : Nat := 118140960795 + 5849504 * 2 ^ 59
def prefixEnd_5849504 : Nat := 4983230072969 + 3 ^ 40 * 5849504 * 2
def baseEnd_5849504 : Nat := 3003607142397587022398627

theorem tailTrace_5849504 : CollatzResearch.WordTrace tailWord_5849504 prefixEnd_5849504 3003607142397587022398627 := by
  unfold tailWord_5849504
  simp only [CollatzResearch.WordTrace]
  refine ⟨106674469100126749296301783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142232625466835665728402377 106674469100126749296301783)
  ·
    refine ⟨160011703650190123944452675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106674469100126749296301783 160011703650190123944452675)
    ·
      refine ⟨240017555475285185916679013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160011703650190123944452675 240017555475285185916679013)
      ·
        refine ⟨45003291651615972359377315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240017555475285185916679013 45003291651615972359377315)
        ·
          refine ⟨67504937477423958539065973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45003291651615972359377315 67504937477423958539065973)
          ·
            refine ⟨6328587888508496113037435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67504937477423958539065973 6328587888508496113037435)
            ·
              refine ⟨9492881832762744169556153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328587888508496113037435 9492881832762744169556153)
              ·
                refine ⟨7119661374572058127167115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9492881832762744169556153 7119661374572058127167115)
                ·
                  refine ⟨10679492061858087190750673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7119661374572058127167115 10679492061858087190750673)
                  ·
                    refine ⟨8009619046393565393063005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10679492061858087190750673 8009619046393565393063005)
                    ·
                      refine ⟨3003607142397587022398627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8009619046393565393063005 3003607142397587022398627)
                      ·
                        rfl

theorem cell23_5849504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_5849504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849504 prefixEnd_5849504 := by exact prefixLift 5849504
  have htrace : WordTrace (prefixWord ++ tailWord_5849504) baseStart_5849504 baseEnd_5849504 := by
    simpa [prefixWord, tailWord_5849504, baseEnd_5849504] using wordTrace_append hprefix tailTrace_5849504
  have hstable : (prefixWord ++ tailWord_5849504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849504).length < 2 ^ (prefixWord ++ tailWord_5849504).sum := by decide
  have hdescent : baseEnd_5849504 < baseStart_5849504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849513 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_5849513 : Nat := 118140960795 + 5849513 * 2 ^ 59
def prefixEnd_5849513 : Nat := 4983230072969 + 3 ^ 40 * 5849513 * 2
def baseEnd_5849513 : Nat := 3003611763723477487186085

theorem tailTrace_5849513 : CollatzResearch.WordTrace tailWord_5849513 prefixEnd_5849513 3003611763723477487186085 := by
  unfold tailWord_5849513
  simp only [CollatzResearch.WordTrace]
  refine ⟨213349266457220893129681193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142232844304813928753120795 213349266457220893129681193)
  ·
    refine ⟨160011949842915669847260895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213349266457220893129681193 160011949842915669847260895)
    ·
      refine ⟨240017924764373504770891343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160011949842915669847260895 240017924764373504770891343)
      ·
        refine ⟨360026887146560257156337015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240017924764373504770891343 360026887146560257156337015)
        ·
          refine ⟨540040330719840385734505523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360026887146560257156337015 540040330719840385734505523)
          ·
            refine ⟨810060496079760578601758285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540040330719840385734505523 810060496079760578601758285)
            ·
              refine ⟨303772686029910216975659357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 810060496079760578601758285 303772686029910216975659357)
              ·
                refine ⟨113914757261216331365872259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303772686029910216975659357 113914757261216331365872259)
                ·
                  refine ⟨170872135891824497048808389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113914757261216331365872259 170872135891824497048808389)
                  ·
                    refine ⟨32038525479717093196651573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170872135891824497048808389 32038525479717093196651573)
                    ·
                      refine ⟨3003611763723477487186085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32038525479717093196651573 3003611763723477487186085)
                      ·
                        rfl

theorem cell23_5849513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_5849513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849513 prefixEnd_5849513 := by exact prefixLift 5849513
  have htrace : WordTrace (prefixWord ++ tailWord_5849513) baseStart_5849513 baseEnd_5849513 := by
    simpa [prefixWord, tailWord_5849513, baseEnd_5849513] using wordTrace_append hprefix tailTrace_5849513
  have hstable : (prefixWord ++ tailWord_5849513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849513).length < 2 ^ (prefixWord ++ tailWord_5849513).sum := by decide
  have hdescent : baseEnd_5849513 < baseStart_5849513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849524 : List Nat := [2, 5, 2, 2, 2, 10]
def baseStart_5849524 : Nat := 118140960795 + 5849524 * 2 ^ 59
def prefixEnd_5849524 : Nat := 4983230072969 + 3 ^ 40 * 5849524 * 2
def baseEnd_5849524 : Nat := 12360565481525419523245

theorem tailTrace_5849524 : CollatzResearch.WordTrace tailWord_5849524 prefixEnd_5849524 12360565481525419523245 := by
  unfold tailWord_5849524
  simp only [CollatzResearch.WordTrace]
  refine ⟨106674833830090521004165813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142233111773454028005554417 106674833830090521004165813)
  ·
    refine ⟨10000765671570986344140545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106674833830090521004165813 10000765671570986344140545)
    ·
      refine ⟨7500574253678239758105409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10000765671570986344140545 7500574253678239758105409)
      ·
        refine ⟨5625430690258679818579057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7500574253678239758105409 5625430690258679818579057)
        ·
          refine ⟨4219073017694009863934293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5625430690258679818579057 4219073017694009863934293)
          ·
            refine ⟨12360565481525419523245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4219073017694009863934293 12360565481525419523245)
            ·
              rfl

theorem cell23_5849524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 10].length) (baseStart_5849524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849524 prefixEnd_5849524 := by exact prefixLift 5849524
  have htrace : WordTrace (prefixWord ++ tailWord_5849524) baseStart_5849524 baseEnd_5849524 := by
    simpa [prefixWord, tailWord_5849524, baseEnd_5849524] using wordTrace_append hprefix tailTrace_5849524
  have hstable : (prefixWord ++ tailWord_5849524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849524).length < 2 ^ (prefixWord ++ tailWord_5849524).sum := by decide
  have hdescent : baseEnd_5849524 < baseStart_5849524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849534 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_5849534 : Nat := 118140960795 + 5849534 * 2 ^ 59
def prefixEnd_5849534 : Nat := 4983230072969 + 3 ^ 40 * 5849534 * 2
def baseEnd_5849534 : Nat := 3003622546817221905023489

theorem tailTrace_5849534 : CollatzResearch.WordTrace tailWord_5849534 prefixEnd_5849534 3003622546817221905023489 := by
  unfold tailWord_5849534
  simp only [CollatzResearch.WordTrace]
  refine ⟨26668754048768101714524457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142233354926763209144130437 26668754048768101714524457)
  ·
    refine ⟨20001565536576076285893343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26668754048768101714524457 20001565536576076285893343)
    ·
      refine ⟨30002348304864114428840015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20001565536576076285893343 30002348304864114428840015)
      ·
        refine ⟨45003522457296171643260023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30002348304864114428840015 45003522457296171643260023)
        ·
          refine ⟨67505283685944257464890035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45003522457296171643260023 67505283685944257464890035)
          ·
            refine ⟨101257925528916386197335053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67505283685944257464890035 101257925528916386197335053)
            ·
              refine ⟨37971722073343644824000645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101257925528916386197335053 37971722073343644824000645)
              ·
                refine ⟨7119697888751933404500121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37971722073343644824000645 7119697888751933404500121)
                ·
                  refine ⟨5339773416563950053375091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7119697888751933404500121 5339773416563950053375091)
                  ·
                    refine ⟨8009660124845925080062637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5339773416563950053375091 8009660124845925080062637)
                    ·
                      refine ⟨3003622546817221905023489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8009660124845925080062637 3003622546817221905023489)
                      ·
                        rfl

theorem cell23_5849534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_5849534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849534 prefixEnd_5849534 := by exact prefixLift 5849534
  have htrace : WordTrace (prefixWord ++ tailWord_5849534) baseStart_5849534 baseEnd_5849534 := by
    simpa [prefixWord, tailWord_5849534, baseEnd_5849534] using wordTrace_append hprefix tailTrace_5849534
  have hstable : (prefixWord ++ tailWord_5849534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849534).length < 2 ^ (prefixWord ++ tailWord_5849534).sum := by decide
  have hdescent : baseEnd_5849534 < baseStart_5849534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849560 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_5849560 : Nat := 118140960795 + 5849560 * 2 ^ 59
def prefixEnd_5849560 : Nat := 4983230072969 + 3 ^ 40 * 5849560 * 2
def baseEnd_5849560 : Nat := 3003635897314238803298369

theorem tailTrace_5849560 : CollatzResearch.WordTrace tailWord_5849560 prefixEnd_5849560 3003635897314238803298369 := by
  unfold tailWord_5849560
  simp only [CollatzResearch.WordTrace]
  refine ⟨106675490344025310078321067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142233987125367080104428089 106675490344025310078321067)
  ·
    refine ⟨160013235516037965117481601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106675490344025310078321067 160013235516037965117481601)
    ·
      refine ⟨120009926637028473838111201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160013235516037965117481601 120009926637028473838111201)
      ·
        refine ⟨90007444977771355378583401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120009926637028473838111201 90007444977771355378583401)
        ·
          refine ⟨67505583733328516533937551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90007444977771355378583401 67505583733328516533937551)
          ·
            refine ⟨101258375599992774800906327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67505583733328516533937551 101258375599992774800906327)
            ·
              refine ⟨151887563399989162201359491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101258375599992774800906327 151887563399989162201359491)
              ·
                refine ⟨227831345099983743302039237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151887563399989162201359491 227831345099983743302039237)
                ·
                  refine ⟨42718377206246951869132357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227831345099983743302039237 42718377206246951869132357)
                  ·
                    refine ⟨8009695726171303475462317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42718377206246951869132357 8009695726171303475462317)
                    ·
                      refine ⟨3003635897314238803298369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8009695726171303475462317 3003635897314238803298369)
                      ·
                        rfl

theorem cell23_5849560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_5849560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849560 prefixEnd_5849560 := by exact prefixLift 5849560
  have htrace : WordTrace (prefixWord ++ tailWord_5849560) baseStart_5849560 baseEnd_5849560 := by
    simpa [prefixWord, tailWord_5849560, baseEnd_5849560] using wordTrace_append hprefix tailTrace_5849560
  have hstable : (prefixWord ++ tailWord_5849560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849560).length < 2 ^ (prefixWord ++ tailWord_5849560).sum := by decide
  have hdescent : baseEnd_5849560 < baseStart_5849560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849578 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_5849578 : Nat := 118140960795 + 5849578 * 2 ^ 59
def prefixEnd_5849578 : Nat := 4983230072969 + 3 ^ 40 * 5849578 * 2
def baseEnd_5849578 : Nat := 3003645139966019732873287

theorem tailTrace_5849578 : CollatzResearch.WordTrace tailWord_5849578 prefixEnd_5849578 3003645139966019732873287 := by
  unfold tailWord_5849578
  simp only [CollatzResearch.WordTrace]
  refine ⟨53337909300496352307699347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142234424801323606153864925 53337909300496352307699347)
  ·
    refine ⟨80006863950744528461549021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53337909300496352307699347 80006863950744528461549021)
    ·
      refine ⟨30002573981529198173080883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80006863950744528461549021 30002573981529198173080883)
      ·
        refine ⟨45003860972293797259621325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30002573981529198173080883 45003860972293797259621325)
        ·
          refine ⟨16876447864610173972357997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45003860972293797259621325 16876447864610173972357997)
          ·
            refine ⟨6328667949228815239634249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16876447864610173972357997 6328667949228815239634249)
            ·
              refine ⟨4746500961921611429725687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6328667949228815239634249 4746500961921611429725687)
              ·
                refine ⟨7119751442882417144588531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4746500961921611429725687 7119751442882417144588531)
                ·
                  refine ⟨10679627164323625716882797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7119751442882417144588531 10679627164323625716882797)
                  ·
                    refine ⟨4004860186621359643831049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10679627164323625716882797 4004860186621359643831049)
                    ·
                      refine ⟨3003645139966019732873287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4004860186621359643831049 3003645139966019732873287)
                      ·
                        rfl

theorem cell23_5849578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_5849578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849578 prefixEnd_5849578 := by exact prefixLift 5849578
  have htrace : WordTrace (prefixWord ++ tailWord_5849578) baseStart_5849578 baseEnd_5849578 := by
    simpa [prefixWord, tailWord_5849578, baseEnd_5849578] using wordTrace_append hprefix tailTrace_5849578
  have hstable : (prefixWord ++ tailWord_5849578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849578).length < 2 ^ (prefixWord ++ tailWord_5849578).sum := by decide
  have hdescent : baseEnd_5849578 < baseStart_5849578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849597 : List Nat := [1, 4, 1, 1, 1, 3, 1, 6, 5]
def baseStart_5849597 : Nat := 118140960795 + 5849597 * 2 ^ 59
def prefixEnd_5849597 : Nat := 4983230072969 + 3 ^ 40 * 5849597 * 2
def baseEnd_5849597 : Nat := 333739432899828350948411

theorem tailTrace_5849597 : CollatzResearch.WordTrace tailWord_5849597 prefixEnd_5849597 333739432899828350948411 := by
  unfold tailWord_5849597
  simp only [CollatzResearch.WordTrace]
  refine ⟨213352330188916575475739045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142234886792611050317159363 213352330188916575475739045)
  ·
    refine ⟨40003561910421857901701071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213352330188916575475739045 40003561910421857901701071)
    ·
      refine ⟨60005342865632786852551607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40003561910421857901701071 60005342865632786852551607)
      ·
        refine ⟨90008014298449180278827411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60005342865632786852551607 90008014298449180278827411)
        ·
          refine ⟨135012021447673770418241117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90008014298449180278827411 135012021447673770418241117)
          ·
            refine ⟨50629508042877663906840419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135012021447673770418241117 50629508042877663906840419)
            ·
              refine ⟨75944262064316495860260629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50629508042877663906840419 75944262064316495860260629)
              ·
                refine ⟨3559887284264835743449717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75944262064316495860260629 3559887284264835743449717)
                ·
                  refine ⟨333739432899828350948411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3559887284264835743449717 333739432899828350948411)
                  ·
                    rfl

theorem cell23_5849597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_5849597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849597 prefixEnd_5849597 := by exact prefixLift 5849597
  have htrace : WordTrace (prefixWord ++ tailWord_5849597) baseStart_5849597 baseEnd_5849597 := by
    simpa [prefixWord, tailWord_5849597, baseEnd_5849597] using wordTrace_append hprefix tailTrace_5849597
  have hstable : (prefixWord ++ tailWord_5849597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849597).length < 2 ^ (prefixWord ++ tailWord_5849597).sum := by decide
  have hdescent : baseEnd_5849597 < baseStart_5849597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849610 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_5849610 : Nat := 118140960795 + 5849610 * 2 ^ 59
def prefixEnd_5849610 : Nat := 4983230072969 + 3 ^ 40 * 5849610 * 2
def baseEnd_5849610 : Nat := 1001220523782321202557713

theorem tailTrace_5849610 : CollatzResearch.WordTrace tailWord_5849610 prefixEnd_5849610 1001220523782321202557713 := by
  unfold tailWord_5849610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53338201084467369673990571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142235202891912985797308189 53338201084467369673990571)
  ·
    refine ⟨80007301626701054510985857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53338201084467369673990571 80007301626701054510985857)
    ·
      refine ⟨60005476220025790883239393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80007301626701054510985857 60005476220025790883239393)
      ·
        refine ⟨45004107165019343162429545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60005476220025790883239393 45004107165019343162429545)
        ·
          refine ⟨33753080373764507371822159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45004107165019343162429545 33753080373764507371822159)
          ·
            refine ⟨50629620560646761057733239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33753080373764507371822159 50629620560646761057733239)
            ·
              refine ⟨75944430840970141586599859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50629620560646761057733239 75944430840970141586599859)
              ·
                refine ⟨113916646261455212379899789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75944430840970141586599859 113916646261455212379899789)
                ·
                  refine ⟨42718742348045704642462421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113916646261455212379899789 42718742348045704642462421)
                  ·
                    refine ⟨1001220523782321202557713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42718742348045704642462421 1001220523782321202557713)
                    ·
                      rfl

theorem cell23_5849610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_5849610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849610 prefixEnd_5849610 := by exact prefixLift 5849610
  have htrace : WordTrace (prefixWord ++ tailWord_5849610) baseStart_5849610 baseEnd_5849610 := by
    simpa [prefixWord, tailWord_5849610, baseEnd_5849610] using wordTrace_append hprefix tailTrace_5849610
  have hstable : (prefixWord ++ tailWord_5849610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849610).length < 2 ^ (prefixWord ++ tailWord_5849610).sum := by decide
  have hdescent : baseEnd_5849610 < baseStart_5849610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849654 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_5849654 : Nat := 118140960795 + 5849654 * 2 ^ 59
def prefixEnd_5849654 : Nat := 4983230072969 + 3 ^ 40 * 5849654 * 2
def baseEnd_5849654 : Nat := 3003684164495761435522937

theorem tailTrace_5849654 : CollatzResearch.WordTrace tailWord_5849654 prefixEnd_5849654 3003684164495761435522937 := by
  unfold tailWord_5849654
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334650571856879638160251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142236272766473382807042677 13334650571856879638160251)
  ·
    refine ⟨20001975857785319457240377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13334650571856879638160251 20001975857785319457240377)
    ·
      refine ⟨15001481893338989592930283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20001975857785319457240377 15001481893338989592930283)
      ·
        refine ⟨22502222840008484389395425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15001481893338989592930283 22502222840008484389395425)
        ·
          refine ⟨16876667130006363292046569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22502222840008484389395425 16876667130006363292046569)
          ·
            refine ⟨12657500347504772469034927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16876667130006363292046569 12657500347504772469034927)
            ·
              refine ⟨18986250521257158703552391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12657500347504772469034927 18986250521257158703552391)
              ·
                refine ⟨28479375781885738055328587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18986250521257158703552391 28479375781885738055328587)
                ·
                  refine ⟨42719063672828607082992881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28479375781885738055328587 42719063672828607082992881)
                  ·
                    refine ⟨32039297754621455312244661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42719063672828607082992881 32039297754621455312244661)
                    ·
                      refine ⟨3003684164495761435522937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32039297754621455312244661 3003684164495761435522937)
                      ·
                        rfl

theorem cell23_5849654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_5849654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849654 prefixEnd_5849654 := by exact prefixLift 5849654
  have htrace : WordTrace (prefixWord ++ tailWord_5849654) baseStart_5849654 baseEnd_5849654 := by
    simpa [prefixWord, tailWord_5849654, baseEnd_5849654] using wordTrace_append hprefix tailTrace_5849654
  have hstable : (prefixWord ++ tailWord_5849654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849654).length < 2 ^ (prefixWord ++ tailWord_5849654).sum := by decide
  have hdescent : baseEnd_5849654 < baseStart_5849654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849684 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_5849684 : Nat := 118140960795 + 5849684 * 2 ^ 59
def prefixEnd_5849684 : Nat := 4983230072969 + 3 ^ 40 * 5849684 * 2
def baseEnd_5849684 : Nat := 3003699568915396318147799

theorem tailTrace_5849684 : CollatzResearch.WordTrace tailWord_5849684 prefixEnd_5849684 3003699568915396318147799 := by
  unfold tailWord_5849684
  simp only [CollatzResearch.WordTrace]
  refine ⟨106677751669800694667078053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142237002226400926222770737 106677751669800694667078053)
  ·
    refine ⟨20002078438087630250077135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106677751669800694667078053 20002078438087630250077135)
    ·
      refine ⟨30003117657131445375115703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20002078438087630250077135 30003117657131445375115703)
      ·
        refine ⟨45004676485697168062673555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30003117657131445375115703 45004676485697168062673555)
        ·
          refine ⟨67507014728545752094010333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45004676485697168062673555 67507014728545752094010333)
          ·
            refine ⟨25315130523204657035253875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67507014728545752094010333 25315130523204657035253875)
            ·
              refine ⟨37972695784806985552880813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25315130523204657035253875 37972695784806985552880813)
              ·
                refine ⟨14239760919302619582330305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37972695784806985552880813 14239760919302619582330305)
                ·
                  refine ⟨10679820689476964686747729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14239760919302619582330305 10679820689476964686747729)
                  ·
                    refine ⟨8009865517107723515060797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10679820689476964686747729 8009865517107723515060797)
                    ·
                      refine ⟨3003699568915396318147799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8009865517107723515060797 3003699568915396318147799)
                      ·
                        rfl

theorem cell23_5849684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_5849684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849684 prefixEnd_5849684 := by exact prefixLift 5849684
  have htrace : WordTrace (prefixWord ++ tailWord_5849684) baseStart_5849684 baseEnd_5849684 := by
    simpa [prefixWord, tailWord_5849684, baseEnd_5849684] using wordTrace_append hprefix tailTrace_5849684
  have hstable : (prefixWord ++ tailWord_5849684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849684).length < 2 ^ (prefixWord ++ tailWord_5849684).sum := by decide
  have hdescent : baseEnd_5849684 < baseStart_5849684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849690 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_5849690 : Nat := 118140960795 + 5849690 * 2 ^ 59
def prefixEnd_5849690 : Nat := 4983230072969 + 3 ^ 40 * 5849690 * 2
def baseEnd_5849690 : Nat := 3003702649799323294672771

theorem tailTrace_5849690 : CollatzResearch.WordTrace tailWord_5849690 prefixEnd_5849690 3003702649799323294672771 := by
  unfold tailWord_5849690
  simp only [CollatzResearch.WordTrace]
  refine ⟨53338930544394913089718631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142237148118386434905916349 53338930544394913089718631)
  ·
    refine ⟨80008395816592369634577947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53338930544394913089718631 80008395816592369634577947)
    ·
      refine ⟨120012593724888554451866921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80008395816592369634577947 120012593724888554451866921)
      ·
        refine ⟨90009445293666415838900191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120012593724888554451866921 90009445293666415838900191)
        ·
          refine ⟨135014167940499623758350287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90009445293666415838900191 135014167940499623758350287)
          ·
            refine ⟨202521251910749435637525431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135014167940499623758350287 202521251910749435637525431)
            ·
              refine ⟨303781877866124153456288147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202521251910749435637525431 303781877866124153456288147)
              ·
                refine ⟨455672816799186230184432221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303781877866124153456288147 455672816799186230184432221)
                ·
                  refine ⟨170877306299694836319162083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455672816799186230184432221 170877306299694836319162083)
                  ·
                    refine ⟨256315959449542254478743125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170877306299694836319162083 256315959449542254478743125)
                    ·
                      refine ⟨3003702649799323294672771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 256315959449542254478743125 3003702649799323294672771)
                      ·
                        rfl

theorem cell23_5849690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_5849690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849690 prefixEnd_5849690 := by exact prefixLift 5849690
  have htrace : WordTrace (prefixWord ++ tailWord_5849690) baseStart_5849690 baseEnd_5849690 := by
    simpa [prefixWord, tailWord_5849690, baseEnd_5849690] using wordTrace_append hprefix tailTrace_5849690
  have hstable : (prefixWord ++ tailWord_5849690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849690).length < 2 ^ (prefixWord ++ tailWord_5849690).sum := by decide
  have hdescent : baseEnd_5849690 < baseStart_5849690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849724 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_5849724 : Nat := 118140960795 + 5849724 * 2 ^ 59
def prefixEnd_5849724 : Nat := 4983230072969 + 3 ^ 40 * 5849724 * 2
def baseEnd_5849724 : Nat := 3003720108141576161647615

theorem tailTrace_5849724 : CollatzResearch.WordTrace tailWord_5849724 prefixEnd_5849724 3003720108141576161647615 := by
  unfold tailWord_5849724
  simp only [CollatzResearch.WordTrace]
  refine ⟨106678481129728238082806113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142237974839637650777074817 106678481129728238082806113)
  ·
    refine ⟨80008860847296178562104585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106678481129728238082806113 80008860847296178562104585)
    ·
      refine ⟨60006645635472133921578439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80008860847296178562104585 60006645635472133921578439)
      ·
        refine ⟨90009968453208200882367659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60006645635472133921578439 90009968453208200882367659)
        ·
          refine ⟨135014952679812301323551489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90009968453208200882367659 135014952679812301323551489)
          ·
            refine ⟨101261214509859225992663617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135014952679812301323551489 101261214509859225992663617)
            ·
              refine ⟨75945910882394419494497713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101261214509859225992663617 75945910882394419494497713)
              ·
                refine ⟨56959433161795814620873285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75945910882394419494497713 56959433161795814620873285)
                ·
                  refine ⟨10679893717836715241413741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56959433161795814620873285 10679893717836715241413741)
                  ·
                    refine ⟨4004960144188768215530153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10679893717836715241413741 4004960144188768215530153)
                    ·
                      refine ⟨3003720108141576161647615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4004960144188768215530153 3003720108141576161647615)
                      ·
                        rfl

theorem cell23_5849724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_5849724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849724 prefixEnd_5849724 := by exact prefixLift 5849724
  have htrace : WordTrace (prefixWord ++ tailWord_5849724) baseStart_5849724 baseEnd_5849724 := by
    simpa [prefixWord, tailWord_5849724, baseEnd_5849724] using wordTrace_append hprefix tailTrace_5849724
  have hstable : (prefixWord ++ tailWord_5849724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849724).length < 2 ^ (prefixWord ++ tailWord_5849724).sum := by decide
  have hdescent : baseEnd_5849724 < baseStart_5849724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849747 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 6, 4]
def baseStart_5849747 : Nat := 118140960795 + 5849747 * 2 ^ 59
def prefixEnd_5849747 : Nat := 4983230072969 + 3 ^ 40 * 5849747 * 2
def baseEnd_5849747 : Nat := 1001243972732209857220003

theorem tailTrace_5849747 : CollatzResearch.WordTrace tailWord_5849747 prefixEnd_5849747 1001243972732209857220003 := by
  unfold tailWord_5849747
  simp only [CollatzResearch.WordTrace]
  refine ⟨213357801138373151093699495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142238534092248767395799663 213357801138373151093699495)
  ·
    refine ⟨320036701707559726640549243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213357801138373151093699495 320036701707559726640549243)
    ·
      refine ⟨480055052561339589960823865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320036701707559726640549243 480055052561339589960823865)
      ·
        refine ⟨360041289421004692470617899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480055052561339589960823865 360041289421004692470617899)
        ·
          refine ⟨540061934131507038705926849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360041289421004692470617899 540061934131507038705926849)
          ·
            refine ⟨405046450598630279029445137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540061934131507038705926849 405046450598630279029445137)
            ·
              refine ⟨303784837948972709272083853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405046450598630279029445137 303784837948972709272083853)
              ·
                refine ⟨113919314230864765977031445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303784837948972709272083853 113919314230864765977031445)
                ·
                  refine ⟨5339967854571785905173349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113919314230864765977031445 5339967854571785905173349)
                  ·
                    refine ⟨1001243972732209857220003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5339967854571785905173349 1001243972732209857220003)
                    ·
                      rfl

theorem cell23_5849747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 4].length) (baseStart_5849747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849747 prefixEnd_5849747 := by exact prefixLift 5849747
  have htrace : WordTrace (prefixWord ++ tailWord_5849747) baseStart_5849747 baseEnd_5849747 := by
    simpa [prefixWord, tailWord_5849747, baseEnd_5849747] using wordTrace_append hprefix tailTrace_5849747
  have hstable : (prefixWord ++ tailWord_5849747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849747).length < 2 ^ (prefixWord ++ tailWord_5849747).sum := by decide
  have hdescent : baseEnd_5849747 < baseStart_5849747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849764 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_5849764 : Nat := 118140960795 + 5849764 * 2 ^ 59
def prefixEnd_5849764 : Nat := 4983230072969 + 3 ^ 40 * 5849764 * 2
def baseEnd_5849764 : Nat := 1001246882455918668382477

theorem tailTrace_5849764 : CollatzResearch.WordTrace tailWord_5849764 prefixEnd_5849764 1001246882455918668382477 := by
  unfold tailWord_5849764
  simp only [CollatzResearch.WordTrace]
  refine ⟨106679210589655781498534173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142238947452874375331378897 106679210589655781498534173)
  ·
    refine ⟨40004703971120918061950315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106679210589655781498534173 40004703971120918061950315)
    ·
      refine ⟨60007055956681377092925473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40004703971120918061950315 60007055956681377092925473)
      ·
        refine ⟨45005291967511032819694105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60007055956681377092925473 45005291967511032819694105)
        ·
          refine ⟨33753968975633274614770579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45005291967511032819694105 33753968975633274614770579)
          ·
            refine ⟨50630953463449911922155869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33753968975633274614770579 50630953463449911922155869)
            ·
              refine ⟨18986607548793716970808451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50630953463449911922155869 18986607548793716970808451)
              ·
                refine ⟨28479911323190575456212677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18986607548793716970808451 28479911323190575456212677)
                ·
                  refine ⟨5339983373098232898039877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28479911323190575456212677 5339983373098232898039877)
                  ·
                    refine ⟨1001246882455918668382477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5339983373098232898039877 1001246882455918668382477)
                    ·
                      rfl

theorem cell23_5849764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_5849764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849764 prefixEnd_5849764 := by exact prefixLift 5849764
  have htrace : WordTrace (prefixWord ++ tailWord_5849764) baseStart_5849764 baseEnd_5849764 := by
    simpa [prefixWord, tailWord_5849764, baseEnd_5849764] using wordTrace_append hprefix tailTrace_5849764
  have hstable : (prefixWord ++ tailWord_5849764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849764).length < 2 ^ (prefixWord ++ tailWord_5849764).sum := by decide
  have hdescent : baseEnd_5849764 < baseStart_5849764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849781 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_5849781 : Nat := 118140960795 + 5849781 * 2 ^ 59
def prefixEnd_5849781 : Nat := 4983230072969 + 3 ^ 40 * 5849781 * 2
def baseEnd_5849781 : Nat := 1001249792179627479544951

theorem tailTrace_5849781 : CollatzResearch.WordTrace tailWord_5849781 prefixEnd_5849781 1001249792179627479544951 := by
  unfold tailWord_5849781
  simp only [CollatzResearch.WordTrace]
  refine ⟨213359041220249974900437197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142239360813499983266958131 213359041220249974900437197)
  ·
    refine ⟨80009640457593740587663949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213359041220249974900437197 80009640457593740587663949)
    ·
      refine ⟨30003615171597652720373981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80009640457593740587663949 30003615171597652720373981)
      ·
        refine ⟨11251355689349119770140243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30003615171597652720373981 11251355689349119770140243)
        ·
          refine ⟨16877033534023679655210365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11251355689349119770140243 16877033534023679655210365)
          ·
            refine ⟨6328887575258879870703887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16877033534023679655210365 6328887575258879870703887)
            ·
              refine ⟨9493331362888319806055831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328887575258879870703887 9493331362888319806055831)
              ·
                refine ⟨14239997044332479709083747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9493331362888319806055831 14239997044332479709083747)
                ·
                  refine ⟨21359995566498719563625621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14239997044332479709083747 21359995566498719563625621)
                  ·
                    refine ⟨1001249792179627479544951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21359995566498719563625621 1001249792179627479544951)
                    ·
                      rfl

theorem cell23_5849781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_5849781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849781 prefixEnd_5849781 := by exact prefixLift 5849781
  have htrace : WordTrace (prefixWord ++ tailWord_5849781) baseStart_5849781 baseEnd_5849781 := by
    simpa [prefixWord, tailWord_5849781, baseEnd_5849781] using wordTrace_append hprefix tailTrace_5849781
  have hstable : (prefixWord ++ tailWord_5849781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849781).length < 2 ^ (prefixWord ++ tailWord_5849781).sum := by decide
  have hdescent : baseEnd_5849781 < baseStart_5849781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849791 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 3]
def baseStart_5849791 : Nat := 118140960795 + 5849791 * 2 ^ 59
def prefixEnd_5849791 : Nat := 4983230072969 + 3 ^ 40 * 5849791 * 2
def baseEnd_5849791 : Nat := 3003754511345427399509807

theorem tailTrace_5849791 : CollatzResearch.WordTrace tailWord_5849791 prefixEnd_5849791 3003754511345427399509807 := by
  unfold tailWord_5849791
  simp only [CollatzResearch.WordTrace]
  refine ⟨213359405950213746608301227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142239603966809164405534151 213359405950213746608301227)
  ·
    refine ⟨320039108925320619912451841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213359405950213746608301227 320039108925320619912451841)
    ·
      refine ⟨240029331693990464934338881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320039108925320619912451841 240029331693990464934338881)
      ·
        refine ⟨180021998770492848700754161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240029331693990464934338881 180021998770492848700754161)
        ·
          refine ⟨135016499077869636525565621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180021998770492848700754161 135016499077869636525565621)
          ·
            refine ⟨12657796788550278424271777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135016499077869636525565621 12657796788550278424271777)
            ·
              refine ⟨9493347591412708818203833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12657796788550278424271777 9493347591412708818203833)
              ·
                refine ⟨7120010693559531613652875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9493347591412708818203833 7120010693559531613652875)
                ·
                  refine ⟨10680016040339297420479313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7120010693559531613652875 10680016040339297420479313)
                  ·
                    refine ⟨8010012030254473065359485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10680016040339297420479313 8010012030254473065359485)
                    ·
                      refine ⟨3003754511345427399509807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8010012030254473065359485 3003754511345427399509807)
                      ·
                        rfl

theorem cell23_5849791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_5849791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849791 prefixEnd_5849791 := by exact prefixLift 5849791
  have htrace : WordTrace (prefixWord ++ tailWord_5849791) baseStart_5849791 baseEnd_5849791 := by
    simpa [prefixWord, tailWord_5849791, baseEnd_5849791] using wordTrace_append hprefix tailTrace_5849791
  have hstable : (prefixWord ++ tailWord_5849791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849791).length < 2 ^ (prefixWord ++ tailWord_5849791).sum := by decide
  have hdescent : baseEnd_5849791 < baseStart_5849791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849817 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_5849817 : Nat := 118140960795 + 5849817 * 2 ^ 59
def prefixEnd_5849817 : Nat := 4983230072969 + 3 ^ 40 * 5849817 * 2
def baseEnd_5849817 : Nat := 3003767861842444297784687

theorem tailTrace_5849817 : CollatzResearch.WordTrace tailWord_5849817 prefixEnd_5849817 3003767861842444297784687 := by
  unfold tailWord_5849817
  simp only [CollatzResearch.WordTrace]
  refine ⟨213360354248119553048747705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142240236165413035365831803 213360354248119553048747705)
  ·
    refine ⟨160020265686089664786560779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213360354248119553048747705 160020265686089664786560779)
    ·
      refine ⟨240030398529134497179841169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160020265686089664786560779 240030398529134497179841169)
      ·
        refine ⟨180022798896850872884880877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240030398529134497179841169 180022798896850872884880877)
        ·
          refine ⟨67508549586319077331830329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180022798896850872884880877 67508549586319077331830329)
          ·
            refine ⟨50631412189739307998872747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67508549586319077331830329 50631412189739307998872747)
            ·
              refine ⟨75947118284608961998309121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50631412189739307998872747 75947118284608961998309121)
              ·
                refine ⟨56960338713456721498731841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75947118284608961998309121 56960338713456721498731841)
                ·
                  refine ⟨42720254035092541124048881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56960338713456721498731841 42720254035092541124048881)
                  ·
                    refine ⟨32040190526319405843036661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42720254035092541124048881 32040190526319405843036661)
                    ·
                      refine ⟨3003767861842444297784687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32040190526319405843036661 3003767861842444297784687)
                      ·
                        rfl

theorem cell23_5849817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_5849817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849817 prefixEnd_5849817 := by exact prefixLift 5849817
  have htrace : WordTrace (prefixWord ++ tailWord_5849817) baseStart_5849817 baseEnd_5849817 := by
    simpa [prefixWord, tailWord_5849817, baseEnd_5849817] using wordTrace_append hprefix tailTrace_5849817
  have hstable : (prefixWord ++ tailWord_5849817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849817).length < 2 ^ (prefixWord ++ tailWord_5849817).sum := by decide
  have hdescent : baseEnd_5849817 < baseStart_5849817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849838 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_5849838 : Nat := 118140960795 + 5849838 * 2 ^ 59
def prefixEnd_5849838 : Nat := 4983230072969 + 3 ^ 40 * 5849838 * 2
def baseEnd_5849838 : Nat := 3003778644936188715622091

theorem tailTrace_5849838 : CollatzResearch.WordTrace tailWord_5849838 prefixEnd_5849838 3003778644936188715622091 := by
  unfold tailWord_5849838
  simp only [CollatzResearch.WordTrace]
  refine ⟨26670140022630434204407771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142240746787362315756841445 26670140022630434204407771)
  ·
    refine ⟨40005210033945651306611657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26670140022630434204407771 40005210033945651306611657)
    ·
      refine ⟨30003907525459238479958743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40005210033945651306611657 30003907525459238479958743)
      ·
        refine ⟨45005861288188857719938115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30003907525459238479958743 45005861288188857719938115)
        ·
          refine ⟨67508791932283286579907173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45005861288188857719938115 67508791932283286579907173)
          ·
            refine ⟨12657898487303116233732595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67508791932283286579907173 12657898487303116233732595)
            ·
              refine ⟨18986847730954674350598893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12657898487303116233732595 18986847730954674350598893)
              ·
                refine ⟨7120067899108002881474585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18986847730954674350598893 7120067899108002881474585)
                ·
                  refine ⟨5340050924331002161105939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7120067899108002881474585 5340050924331002161105939)
                  ·
                    refine ⟨8010076386496503241658909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5340050924331002161105939 8010076386496503241658909)
                    ·
                      refine ⟨3003778644936188715622091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8010076386496503241658909 3003778644936188715622091)
                      ·
                        rfl

theorem cell23_5849838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_5849838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849838 prefixEnd_5849838 := by exact prefixLift 5849838
  have htrace : WordTrace (prefixWord ++ tailWord_5849838) baseStart_5849838 baseEnd_5849838 := by
    simpa [prefixWord, tailWord_5849838, baseEnd_5849838] using wordTrace_append hprefix tailTrace_5849838
  have hstable : (prefixWord ++ tailWord_5849838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849838).length < 2 ^ (prefixWord ++ tailWord_5849838).sum := by decide
  have hdescent : baseEnd_5849838 < baseStart_5849838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849861 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 6, 2, 2]
def baseStart_5849861 : Nat := 118140960795 + 5849861 * 2 ^ 59
def prefixEnd_5849861 : Nat := 4983230072969 + 3 ^ 40 * 5849861 * 2
def baseEnd_5849861 : Nat := 3003790454991242125634485

theorem tailTrace_5849861 : CollatzResearch.WordTrace tailWord_5849861 prefixEnd_5849861 3003790454991242125634485 := by
  unfold tailWord_5849861
  simp only [CollatzResearch.WordTrace]
  refine ⟨213361959059960148563349437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142241306039973432375566291 213361959059960148563349437)
  ·
    refine ⟨80010734647485055711256039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213361959059960148563349437 80010734647485055711256039)
    ·
      refine ⟨120016101971227583566884059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80010734647485055711256039 120016101971227583566884059)
      ·
        refine ⟨180024152956841375350326089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120016101971227583566884059 180024152956841375350326089)
        ·
          refine ⟨135018114717631031512744567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180024152956841375350326089 135018114717631031512744567)
          ·
            refine ⟨202527172076446547269116851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135018114717631031512744567 202527172076446547269116851)
            ·
              refine ⟨303790758114669820903675277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202527172076446547269116851 303790758114669820903675277)
              ·
                refine ⟨113921534293001182838878229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303790758114669820903675277 113921534293001182838878229)
                ·
                  refine ⟨5340071919984430445572417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113921534293001182838878229 5340071919984430445572417)
                  ·
                    refine ⟨4005053939988322834179313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5340071919984430445572417 4005053939988322834179313)
                    ·
                      refine ⟨3003790454991242125634485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005053939988322834179313 3003790454991242125634485)
                      ·
                        rfl

theorem cell23_5849861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_5849861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849861 prefixEnd_5849861 := by exact prefixLift 5849861
  have htrace : WordTrace (prefixWord ++ tailWord_5849861) baseStart_5849861 baseEnd_5849861 := by
    simpa [prefixWord, tailWord_5849861, baseEnd_5849861] using wordTrace_append hprefix tailTrace_5849861
  have hstable : (prefixWord ++ tailWord_5849861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849861).length < 2 ^ (prefixWord ++ tailWord_5849861).sum := by decide
  have hdescent : baseEnd_5849861 < baseStart_5849861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849864 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_5849864 : Nat := 118140960795 + 5849864 * 2 ^ 59
def prefixEnd_5849864 : Nat := 4983230072969 + 3 ^ 40 * 5849864 * 2
def baseEnd_5849864 : Nat := 3003791995433205613896971

theorem tailTrace_5849864 : CollatzResearch.WordTrace tailWord_5849864 prefixEnd_5849864 3003791995433205613896971 := by
  unfold tailWord_5849864
  simp only [CollatzResearch.WordTrace]
  refine ⟨106681034239474640037854323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142241378985966186717139097 106681034239474640037854323)
  ·
    refine ⟨160021551359211960056781485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106681034239474640037854323 160021551359211960056781485)
    ·
      refine ⟨60008081759704485021293057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160021551359211960056781485 60008081759704485021293057)
      ·
        refine ⟨45006061319778363765969793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60008081759704485021293057 45006061319778363765969793)
        ·
          refine ⟨33754545989833772824477345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45006061319778363765969793 33754545989833772824477345)
          ·
            refine ⟨25315909492375329618358009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33754545989833772824477345 25315909492375329618358009)
            ·
              refine ⟨18986932119281497213768507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25315909492375329618358009 18986932119281497213768507)
              ·
                refine ⟨28480398178922245820652761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18986932119281497213768507 28480398178922245820652761)
                ·
                  refine ⟨21360298634191684365489571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28480398178922245820652761 21360298634191684365489571)
                  ·
                    refine ⟨32040447951287526548234357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21360298634191684365489571 32040447951287526548234357)
                    ·
                      refine ⟨3003791995433205613896971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32040447951287526548234357 3003791995433205613896971)
                      ·
                        rfl

theorem cell23_5849864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_5849864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849864 prefixEnd_5849864 := by exact prefixLift 5849864
  have htrace : WordTrace (prefixWord ++ tailWord_5849864) baseStart_5849864 baseEnd_5849864 := by
    simpa [prefixWord, tailWord_5849864, baseEnd_5849864] using wordTrace_append hprefix tailTrace_5849864
  have hstable : (prefixWord ++ tailWord_5849864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849864).length < 2 ^ (prefixWord ++ tailWord_5849864).sum := by decide
  have hdescent : baseEnd_5849864 < baseStart_5849864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849897 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 3, 7]
def baseStart_5849897 : Nat := 118140960795 + 5849897 * 2 ^ 59
def prefixEnd_5849897 : Nat := 4983230072969 + 3 ^ 40 * 5849897 * 2
def baseEnd_5849897 : Nat := 1001269646764934661594773

theorem tailTrace_5849897 : CollatzResearch.WordTrace tailWord_5849897 prefixEnd_5849897 1001269646764934661594773 := by
  unfold tailWord_5849897
  simp only [CollatzResearch.WordTrace]
  refine ⟨213363272087829726711659945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142242181391886484474439963 213363272087829726711659945)
  ·
    refine ⟨160022454065872295033744959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213363272087829726711659945 160022454065872295033744959)
    ·
      refine ⟨240033681098808442550617439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160022454065872295033744959 240033681098808442550617439)
      ·
        refine ⟨360050521648212663825926159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240033681098808442550617439 360050521648212663825926159)
        ·
          refine ⟨540075782472318995738889239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360050521648212663825926159 540075782472318995738889239)
          ·
            refine ⟨810113673708478493608333859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540075782472318995738889239 810113673708478493608333859)
            ·
              refine ⟨1215170510562717740412500789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810113673708478493608333859 1215170510562717740412500789)
              ·
                refine ⟨113922235365254788163671949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1215170510562717740412500789 113922235365254788163671949)
                ·
                  refine ⟨42720838261970545561376981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113922235365254788163671949 42720838261970545561376981)
                  ·
                    refine ⟨1001269646764934661594773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42720838261970545561376981 1001269646764934661594773)
                    ·
                      rfl

theorem cell23_5849897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_5849897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849897 prefixEnd_5849897 := by exact prefixLift 5849897
  have htrace : WordTrace (prefixWord ++ tailWord_5849897) baseStart_5849897 baseEnd_5849897 := by
    simpa [prefixWord, tailWord_5849897, baseEnd_5849897] using wordTrace_append hprefix tailTrace_5849897
  have hstable : (prefixWord ++ tailWord_5849897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849897).length < 2 ^ (prefixWord ++ tailWord_5849897).sum := by decide
  have hdescent : baseEnd_5849897 < baseStart_5849897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849951 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 2, 4, 2]
def baseStart_5849951 : Nat := 118140960795 + 5849951 * 2 ^ 59
def prefixEnd_5849951 : Nat := 4983230072969 + 3 ^ 40 * 5849951 * 2
def baseEnd_5849951 : Nat := 3003836668250146773509071

theorem tailTrace_5849951 : CollatzResearch.WordTrace tailWord_5849951 prefixEnd_5849951 3003836668250146773509071 := by
  unfold tailWord_5849951
  simp only [CollatzResearch.WordTrace]
  refine ⟨213365241629634093934125707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142243494419756062622750471 213365241629634093934125707)
  ·
    refine ⟨320047862444451140901188561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213365241629634093934125707 320047862444451140901188561)
    ·
      refine ⟨240035896833338355675891421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320047862444451140901188561 240035896833338355675891421)
      ·
        refine ⟨90013461312501883378459283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240035896833338355675891421 90013461312501883378459283)
        ·
          refine ⟨135020191968752825067688925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90013461312501883378459283 135020191968752825067688925)
          ·
            refine ⟨50632571988282309400383347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135020191968752825067688925 50632571988282309400383347)
            ·
              refine ⟨75948857982423464100575021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50632571988282309400383347 75948857982423464100575021)
              ·
                refine ⟨28480821743408799037715633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75948857982423464100575021 28480821743408799037715633)
                ·
                  refine ⟨21360616307556599278286725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28480821743408799037715633 21360616307556599278286725)
                  ·
                    refine ⟨4005115557666862364678761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21360616307556599278286725 4005115557666862364678761)
                    ·
                      refine ⟨3003836668250146773509071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005115557666862364678761 3003836668250146773509071)
                      ·
                        rfl

theorem cell23_5849951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_5849951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849951 prefixEnd_5849951 := by exact prefixLift 5849951
  have htrace : WordTrace (prefixWord ++ tailWord_5849951) baseStart_5849951 baseEnd_5849951 := by
    simpa [prefixWord, tailWord_5849951, baseEnd_5849951] using wordTrace_append hprefix tailTrace_5849951
  have hstable : (prefixWord ++ tailWord_5849951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849951).length < 2 ^ (prefixWord ++ tailWord_5849951).sum := by decide
  have hdescent : baseEnd_5849951 < baseStart_5849951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849964 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_5849964 : Nat := 118140960795 + 5849964 * 2 ^ 59
def prefixEnd_5849964 : Nat := 4983230072969 + 3 ^ 40 * 5849964 * 2
def baseEnd_5849964 : Nat := 3003843343498655222646511

theorem tailTrace_5849964 : CollatzResearch.WordTrace tailWord_5849964 prefixEnd_5849964 3003843343498655222646511 := by
  unfold tailWord_5849964
  simp only [CollatzResearch.WordTrace]
  refine ⟨106682857889293498577174473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142243810519057998102899297 106682857889293498577174473)
  ·
    refine ⟨80012143416970123932880855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106682857889293498577174473 80012143416970123932880855)
    ·
      refine ⟨120018215125455185899321283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80012143416970123932880855 120018215125455185899321283)
      ·
        refine ⟨180027322688182778848981925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120018215125455185899321283 180027322688182778848981925)
        ·
          refine ⟨33755123004034271034184111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180027322688182778848981925 33755123004034271034184111)
          ·
            refine ⟨50632684506051406551276167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33755123004034271034184111 50632684506051406551276167)
            ·
              refine ⟨75949026759077109826914251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50632684506051406551276167 75949026759077109826914251)
              ·
                refine ⟨113923540138615664740371377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75949026759077109826914251 113923540138615664740371377)
                ·
                  refine ⟨85442655103961748555278533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113923540138615664740371377 85442655103961748555278533)
                  ·
                    refine ⟨16020497831992827854114725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85442655103961748555278533 16020497831992827854114725)
                    ·
                      refine ⟨3003843343498655222646511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16020497831992827854114725 3003843343498655222646511)
                      ·
                        rfl

theorem cell23_5849964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_5849964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5849964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5849964 prefixEnd_5849964 := by exact prefixLift 5849964
  have htrace : WordTrace (prefixWord ++ tailWord_5849964) baseStart_5849964 baseEnd_5849964 := by
    simpa [prefixWord, tailWord_5849964, baseEnd_5849964] using wordTrace_append hprefix tailTrace_5849964
  have hstable : (prefixWord ++ tailWord_5849964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849964).length < 2 ^ (prefixWord ++ tailWord_5849964).sum := by decide
  have hdescent : baseEnd_5849964 < baseStart_5849964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850068 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_5850068 : Nat := 118140960795 + 5850068 * 2 ^ 59
def prefixEnd_5850068 : Nat := 4983230072969 + 3 ^ 40 * 5850068 * 2
def baseEnd_5850068 : Nat := 1001298915162240938582011

theorem tailTrace_5850068 : CollatzResearch.WordTrace tailWord_5850068 prefixEnd_5850068 1001298915162240938582011 := by
  unfold tailWord_5850068
  simp only [CollatzResearch.WordTrace]
  refine ⟨106684754485105111458067429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142246339313473481944089905 106684754485105111458067429)
  ·
    refine ⟨20003391465957208398387643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106684754485105111458067429 20003391465957208398387643)
    ·
      refine ⟨30005087198935812597581465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20003391465957208398387643 30005087198935812597581465)
      ·
        refine ⟨22503815399201859448186099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30005087198935812597581465 22503815399201859448186099)
        ·
          refine ⟨33755723098802789172279149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22503815399201859448186099 33755723098802789172279149)
          ·
            refine ⟨12658396162051045939604681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33755723098802789172279149 12658396162051045939604681)
            ·
              refine ⟨9493797121538284454703511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12658396162051045939604681 9493797121538284454703511)
              ·
                refine ⟨14240695682307426682055267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9493797121538284454703511 14240695682307426682055267)
                ·
                  refine ⟨21361043523461140023082901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14240695682307426682055267 21361043523461140023082901)
                  ·
                    refine ⟨1001298915162240938582011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21361043523461140023082901 1001298915162240938582011)
                    ·
                      rfl

theorem cell23_5850068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_5850068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850068 prefixEnd_5850068 := by exact prefixLift 5850068
  have htrace : WordTrace (prefixWord ++ tailWord_5850068) baseStart_5850068 baseEnd_5850068 := by
    simpa [prefixWord, tailWord_5850068, baseEnd_5850068] using wordTrace_append hprefix tailTrace_5850068
  have hstable : (prefixWord ++ tailWord_5850068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850068).length < 2 ^ (prefixWord ++ tailWord_5850068).sum := by decide
  have hdescent : baseEnd_5850068 < baseStart_5850068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850095 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 1, 2, 3]
def baseStart_5850095 : Nat := 118140960795 + 5850095 * 2 ^ 59
def prefixEnd_5850095 : Nat := 4983230072969 + 3 ^ 40 * 5850095 * 2
def baseEnd_5850095 : Nat := 3003910609464394210108409

theorem tailTrace_5850095 : CollatzResearch.WordTrace tailWord_5850095 prefixEnd_5850095 3003910609464394210108409 := by
  unfold tailWord_5850095
  simp only [CollatzResearch.WordTrace]
  refine ⟨213370493741112406527367739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142246995827408271018245159 213370493741112406527367739)
  ·
    refine ⟨320055740611668609791051609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213370493741112406527367739 320055740611668609791051609)
    ·
      refine ⟨240041805458751457343288707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320055740611668609791051609 240041805458751457343288707)
      ·
        refine ⟨360062708188127186014933061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240041805458751457343288707 360062708188127186014933061)
        ·
          refine ⟨67511757785273847377799949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360062708188127186014933061 67511757785273847377799949)
          ·
            refine ⟨25316909169477692766674981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67511757785273847377799949 25316909169477692766674981)
            ·
              refine ⟨4746920469277067393751559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25316909169477692766674981 4746920469277067393751559)
              ·
                refine ⟨7120380703915601090627339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4746920469277067393751559 7120380703915601090627339)
                ·
                  refine ⟨10680571055873401635941009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7120380703915601090627339 10680571055873401635941009)
                  ·
                    refine ⟨8010428291905051226955757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10680571055873401635941009 8010428291905051226955757)
                    ·
                      refine ⟨3003910609464394210108409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8010428291905051226955757 3003910609464394210108409)
                      ·
                        rfl

theorem cell23_5850095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 2, 3].length) (baseStart_5850095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850095 prefixEnd_5850095 := by exact prefixLift 5850095
  have htrace : WordTrace (prefixWord ++ tailWord_5850095) baseStart_5850095 baseEnd_5850095 := by
    simpa [prefixWord, tailWord_5850095, baseEnd_5850095] using wordTrace_append hprefix tailTrace_5850095
  have hstable : (prefixWord ++ tailWord_5850095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850095).length < 2 ^ (prefixWord ++ tailWord_5850095).sum := by decide
  have hdescent : baseEnd_5850095 < baseStart_5850095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850098 : List Nat := [3, 2, 1, 5, 1, 1, 10]
def baseStart_5850098 : Nat := 118140960795 + 5850098 * 2 ^ 59
def prefixEnd_5850098 : Nat := 4983230072969 + 3 ^ 40 * 5850098 * 2
def baseEnd_5850098 : Nat := 37085335184029107387295

theorem tailTrace_5850098 : CollatzResearch.WordTrace tailWord_5850098 prefixEnd_5850098 37085335184029107387295 := by
  unfold tailWord_5850098
  simp only [CollatzResearch.WordTrace]
  refine ⟨53342650790025384509931737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142247068773401025359817965 53342650790025384509931737)
  ·
    refine ⟨40006988092519038382448803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53342650790025384509931737 40006988092519038382448803)
    ·
      refine ⟨60010482138778557573673205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40006988092519038382448803 60010482138778557573673205)
      ·
        refine ⟨5625982700510489772531863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60010482138778557573673205 5625982700510489772531863)
        ·
          refine ⟨8438974050765734658797795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5625982700510489772531863 8438974050765734658797795)
          ·
            refine ⟨12658461076148601988196693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8438974050765734658797795 12658461076148601988196693)
            ·
              refine ⟨37085335184029107387295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12658461076148601988196693 37085335184029107387295)
              ·
                rfl

theorem cell23_5850098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 10].length) (baseStart_5850098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850098 prefixEnd_5850098 := by exact prefixLift 5850098
  have htrace : WordTrace (prefixWord ++ tailWord_5850098) baseStart_5850098 baseEnd_5850098 := by
    simpa [prefixWord, tailWord_5850098, baseEnd_5850098] using wordTrace_append hprefix tailTrace_5850098
  have hstable : (prefixWord ++ tailWord_5850098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850098).length < 2 ^ (prefixWord ++ tailWord_5850098).sum := by decide
  have hdescent : baseEnd_5850098 < baseStart_5850098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850102 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_5850102 : Nat := 118140960795 + 5850102 * 2 ^ 59
def prefixEnd_5850102 : Nat := 4983230072969 + 3 ^ 40 * 5850102 * 2
def baseEnd_5850102 : Nat := 1001304734609658560906959

theorem tailTrace_5850102 : CollatzResearch.WordTrace tailWord_5850102 prefixEnd_5850102 1001304734609658560906959 := by
  unfold tailWord_5850102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13335671815755440420179535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142247166034724697815248373 13335671815755440420179535)
  ·
    refine ⟨20003507723633160630269303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13335671815755440420179535 20003507723633160630269303)
    ·
      refine ⟨30005261585449740945403955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20003507723633160630269303 30005261585449740945403955)
      ·
        refine ⟨45007892378174611418105933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30005261585449740945403955 45007892378174611418105933)
        ·
          refine ⟨16877959641815479281789725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45007892378174611418105933 16877959641815479281789725)
          ·
            refine ⟨6329234865680804730671147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16877959641815479281789725 6329234865680804730671147)
            ·
              refine ⟨9493852298521207096006721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329234865680804730671147 9493852298521207096006721)
              ·
                refine ⟨7120389223890905322005041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9493852298521207096006721 7120389223890905322005041)
                ·
                  refine ⟨5340291917918178991503781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7120389223890905322005041 5340291917918178991503781)
                  ·
                    refine ⟨1001304734609658560906959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5340291917918178991503781 1001304734609658560906959)
                    ·
                      rfl

theorem cell23_5850102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_5850102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850102 prefixEnd_5850102 := by exact prefixLift 5850102
  have htrace : WordTrace (prefixWord ++ tailWord_5850102) baseStart_5850102 baseEnd_5850102 := by
    simpa [prefixWord, tailWord_5850102, baseEnd_5850102] using wordTrace_append hprefix tailTrace_5850102
  have hstable : (prefixWord ++ tailWord_5850102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850102).length < 2 ^ (prefixWord ++ tailWord_5850102).sum := by decide
  have hdescent : baseEnd_5850102 < baseStart_5850102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850216 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5850216 : Nat := 118140960795 + 5850216 * 2 ^ 59
def prefixEnd_5850216 : Nat := 4983230072969 + 3 ^ 40 * 5850216 * 2
def baseEnd_5850216 : Nat := 3003972740623588236695353

theorem tailTrace_5850216 : CollatzResearch.WordTrace tailWord_5850216 prefixEnd_5850216 3003972740623588236695353 := by
  unfold tailWord_5850216
  simp only [CollatzResearch.WordTrace]
  refine ⟨106687453486837022096261251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142249937982449362795015001 106687453486837022096261251)
  ·
    refine ⟨160031180230255533144391877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106687453486837022096261251 160031180230255533144391877)
    ·
      refine ⟨30005846293172912464573477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160031180230255533144391877 30005846293172912464573477)
      ·
        refine ⟨5626096179969921087107527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30005846293172912464573477 5626096179969921087107527)
        ·
          refine ⟨8439144269954881630661291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626096179969921087107527 8439144269954881630661291)
          ·
            refine ⟨12658716404932322445991937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8439144269954881630661291 12658716404932322445991937)
            ·
              refine ⟨9494037303699241834493953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12658716404932322445991937 9494037303699241834493953)
              ·
                refine ⟨7120527977774431375870465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9494037303699241834493953 7120527977774431375870465)
                ·
                  refine ⟨5340395983330823531902849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7120527977774431375870465 5340395983330823531902849)
                  ·
                    refine ⟨4005296987498117648927137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5340395983330823531902849 4005296987498117648927137)
                    ·
                      refine ⟨3003972740623588236695353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005296987498117648927137 3003972740623588236695353)
                      ·
                        rfl

theorem cell23_5850216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5850216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850216 prefixEnd_5850216 := by exact prefixLift 5850216
  have htrace : WordTrace (prefixWord ++ tailWord_5850216) baseStart_5850216 baseEnd_5850216 := by
    simpa [prefixWord, tailWord_5850216, baseEnd_5850216] using wordTrace_append hprefix tailTrace_5850216
  have hstable : (prefixWord ++ tailWord_5850216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850216).length < 2 ^ (prefixWord ++ tailWord_5850216).sum := by decide
  have hdescent : baseEnd_5850216 < baseStart_5850216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850222 : List Nat := [4, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_5850222 : Nat := 118140960795 + 5850222 * 2 ^ 59
def prefixEnd_5850222 : Nat := 4983230072969 + 3 ^ 40 * 5850222 * 2
def baseEnd_5850222 : Nat := 333775091278612801468925

theorem tailTrace_5850222 : CollatzResearch.WordTrace tailWord_5850222 prefixEnd_5850222 333775091278612801468925 := by
  unfold tailWord_5850222
  simp only [CollatzResearch.WordTrace]
  refine ⟨26671890726456538402155115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142250083874434871478160613 26671890726456538402155115)
  ·
    refine ⟨40007836089684807603232673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26671890726456538402155115 40007836089684807603232673)
    ·
      refine ⟨30005877067263605702424505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40007836089684807603232673 30005877067263605702424505)
      ·
        refine ⟨22504407800447704276818379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30005877067263605702424505 22504407800447704276818379)
        ·
          refine ⟨33756611700671556415227569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22504407800447704276818379 33756611700671556415227569)
          ·
            refine ⟨25317458775503667311420677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33756611700671556415227569 25317458775503667311420677)
            ·
              refine ⟨4747023520406937620891377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25317458775503667311420677 4747023520406937620891377)
              ·
                refine ⟨3560267640305203215668533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4747023520406937620891377 3560267640305203215668533)
                ·
                  refine ⟨333775091278612801468925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3560267640305203215668533 333775091278612801468925)
                  ·
                    rfl

theorem cell23_5850222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_5850222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850222 prefixEnd_5850222 := by exact prefixLift 5850222
  have htrace : WordTrace (prefixWord ++ tailWord_5850222) baseStart_5850222 baseEnd_5850222 := by
    simpa [prefixWord, tailWord_5850222, baseEnd_5850222] using wordTrace_append hprefix tailTrace_5850222
  have hstable : (prefixWord ++ tailWord_5850222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850222).length < 2 ^ (prefixWord ++ tailWord_5850222).sum := by decide
  have hdescent : baseEnd_5850222 < baseStart_5850222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850251 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6]
def baseStart_5850251 : Nat := 118140960795 + 5850251 * 2 ^ 59
def prefixEnd_5850251 : Nat := 4983230072969 + 3 ^ 40 * 5850251 * 2
def baseEnd_5850251 : Nat := 3003990712446495599757691

theorem tailTrace_5850251 : CollatzResearch.WordTrace tailWord_5850251 prefixEnd_5850251 3003990712446495599757691 := by
  unfold tailWord_5850251
  simp only [CollatzResearch.WordTrace]
  refine ⟨213376183528547245170046607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142250789019031496780031071 213376183528547245170046607)
  ·
    refine ⟨320064275292820867755069911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213376183528547245170046607 320064275292820867755069911)
    ·
      refine ⟨480096412939231301632604867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320064275292820867755069911 480096412939231301632604867)
      ·
        refine ⟨720144619408846952448907301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480096412939231301632604867 720144619408846952448907301)
        ·
          refine ⟨135027116139158803584170119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 720144619408846952448907301 135027116139158803584170119)
          ·
            refine ⟨202540674208738205376255179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135027116139158803584170119 202540674208738205376255179)
            ·
              refine ⟨303811011313107308064382769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202540674208738205376255179 303811011313107308064382769)
              ·
                refine ⟨227858258484830481048287077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303811011313107308064382769 227858258484830481048287077)
                ·
                  refine ⟨42723423465905715196553827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227858258484830481048287077 42723423465905715196553827)
                  ·
                    refine ⟨64085135198858572794830741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42723423465905715196553827 64085135198858572794830741)
                    ·
                      refine ⟨3003990712446495599757691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64085135198858572794830741 3003990712446495599757691)
                      ·
                        rfl

theorem cell23_5850251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_5850251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850251 prefixEnd_5850251 := by exact prefixLift 5850251
  have htrace : WordTrace (prefixWord ++ tailWord_5850251) baseStart_5850251 baseEnd_5850251 := by
    simpa [prefixWord, tailWord_5850251, baseEnd_5850251] using wordTrace_append hprefix tailTrace_5850251
  have hstable : (prefixWord ++ tailWord_5850251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850251).length < 2 ^ (prefixWord ++ tailWord_5850251).sum := by decide
  have hdescent : baseEnd_5850251 < baseStart_5850251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850268 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5850268 : Nat := 118140960795 + 5850268 * 2 ^ 59
def prefixEnd_5850268 : Nat := 4983230072969 + 3 ^ 40 * 5850268 * 2
def baseEnd_5850268 : Nat := 3003999441617622033245113

theorem tailTrace_5850268 : CollatzResearch.WordTrace tailWord_5850268 prefixEnd_5850268 3003999441617622033245113 := by
  unfold tailWord_5850268
  simp only [CollatzResearch.WordTrace]
  refine ⟨106688401784742828536707729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142251202379657104715610305 106688401784742828536707729)
  ·
    refine ⟨80016301338557121402530797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106688401784742828536707729 80016301338557121402530797)
    ·
      refine ⟨30006113001958920525949049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80016301338557121402530797 30006113001958920525949049)
      ·
        refine ⟨22504584751469190394461787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30006113001958920525949049 22504584751469190394461787)
        ·
          refine ⟨33756877127203785591692681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22504584751469190394461787 33756877127203785591692681)
          ·
            refine ⟨25317657845402839193769511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33756877127203785591692681 25317657845402839193769511)
            ·
              refine ⟨37976486768104258790654267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25317657845402839193769511 37976486768104258790654267)
              ·
                refine ⟨56964730152156388185981401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37976486768104258790654267 56964730152156388185981401)
                ·
                  refine ⟨42723547614117291139486051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56964730152156388185981401 42723547614117291139486051)
                  ·
                    refine ⟨64085321421175936709229077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42723547614117291139486051 64085321421175936709229077)
                    ·
                      refine ⟨3003999441617622033245113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64085321421175936709229077 3003999441617622033245113)
                      ·
                        rfl

theorem cell23_5850268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5850268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850268 prefixEnd_5850268 := by exact prefixLift 5850268
  have htrace : WordTrace (prefixWord ++ tailWord_5850268) baseStart_5850268 baseEnd_5850268 := by
    simpa [prefixWord, tailWord_5850268, baseEnd_5850268] using wordTrace_append hprefix tailTrace_5850268
  have hstable : (prefixWord ++ tailWord_5850268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850268).length < 2 ^ (prefixWord ++ tailWord_5850268).sum := by decide
  have hdescent : baseEnd_5850268 < baseStart_5850268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850282 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5850282 : Nat := 118140960795 + 5850282 * 2 ^ 59
def prefixEnd_5850282 : Nat := 4983230072969 + 3 ^ 40 * 5850282 * 2
def baseEnd_5850282 : Nat := 1001335543448928326156683

theorem tailTrace_5850282 : CollatzResearch.WordTrace tailWord_5850282 prefixEnd_5850282 1001335543448928326156683 := by
  unfold tailWord_5850282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53344328547858734366106275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142251542794289958309616733 53344328547858734366106275)
  ·
    refine ⟨80016492821788101549159413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53344328547858734366106275 80016492821788101549159413)
    ·
      refine ⟨7501546202042634520233695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80016492821788101549159413 7501546202042634520233695)
      ·
        refine ⟨11252319303063951780350543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7501546202042634520233695 11252319303063951780350543)
        ·
          refine ⟨16878478954595927670525815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252319303063951780350543 16878478954595927670525815)
          ·
            refine ⟨25317718431893891505788723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16878478954595927670525815 25317718431893891505788723)
            ·
              refine ⟨37976577647840837258683085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25317718431893891505788723 37976577647840837258683085)
              ·
                refine ⟨14241216617940313972006157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37976577647840837258683085 14241216617940313972006157)
                ·
                  refine ⟨5340456231727617739502309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14241216617940313972006157 5340456231727617739502309)
                  ·
                    refine ⟨1001335543448928326156683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5340456231727617739502309 1001335543448928326156683)
                    ·
                      rfl

theorem cell23_5850282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5850282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850282 prefixEnd_5850282 := by exact prefixLift 5850282
  have htrace : WordTrace (prefixWord ++ tailWord_5850282) baseStart_5850282 baseEnd_5850282 := by
    simpa [prefixWord, tailWord_5850282, baseEnd_5850282] using wordTrace_append hprefix tailTrace_5850282
  have hstable : (prefixWord ++ tailWord_5850282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850282).length < 2 ^ (prefixWord ++ tailWord_5850282).sum := by decide
  have hdescent : baseEnd_5850282 < baseStart_5850282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850295 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 6]
def baseStart_5850295 : Nat := 118140960795 + 5850295 * 2 ^ 59
def prefixEnd_5850295 : Nat := 4983230072969 + 3 ^ 40 * 5850295 * 2
def baseEnd_5850295 : Nat := 333779256177254825289721

theorem tailTrace_5850295 : CollatzResearch.WordTrace tailWord_5850295 prefixEnd_5850295 333779256177254825289721 := by
  unfold tailWord_5850295
  simp only [CollatzResearch.WordTrace]
  refine ⟨213377788340387840684648339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142251858893591893789765559 213377788340387840684648339)
  ·
    refine ⟨320066682510581761026972509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213377788340387840684648339 320066682510581761026972509)
    ·
      refine ⟨120025005941468160385114691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320066682510581761026972509 120025005941468160385114691)
      ·
        refine ⟨180037508912202240577672037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120025005941468160385114691 180037508912202240577672037)
        ·
          refine ⟨33757032921037920108313507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180037508912202240577672037 33757032921037920108313507)
          ·
            refine ⟨50635549381556880162470261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33757032921037920108313507 50635549381556880162470261)
            ·
              refine ⟨4747082754520957515231587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50635549381556880162470261 4747082754520957515231587)
              ·
                refine ⟨7120624131781436272847381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747082754520957515231587 7120624131781436272847381)
                ·
                  refine ⟨333779256177254825289721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7120624131781436272847381 333779256177254825289721)
                  ·
                    rfl

theorem cell23_5850295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 6].length) (baseStart_5850295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850295 prefixEnd_5850295 := by exact prefixLift 5850295
  have htrace : WordTrace (prefixWord ++ tailWord_5850295) baseStart_5850295 baseEnd_5850295 := by
    simpa [prefixWord, tailWord_5850295, baseEnd_5850295] using wordTrace_append hprefix tailTrace_5850295
  have hstable : (prefixWord ++ tailWord_5850295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850295).length < 2 ^ (prefixWord ++ tailWord_5850295).sum := by decide
  have hdescent : baseEnd_5850295 < baseStart_5850295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850362 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2]
def baseStart_5850362 : Nat := 118140960795 + 5850362 * 2 ^ 59
def prefixEnd_5850362 : Nat := 4983230072969 + 3 ^ 40 * 5850362 * 2
def baseEnd_5850362 : Nat := 3004047708799144665469681

theorem tailTrace_5850362 : CollatzResearch.WordTrace tailWord_5850362 prefixEnd_5850362 3004047708799144665469681 := by
  unfold tailWord_5850362
  simp only [CollatzResearch.WordTrace]
  refine ⟨53345058007786277781834335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142253488020763407418224893 53345058007786277781834335)
  ·
    refine ⟨80017587011679416672751503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53345058007786277781834335 80017587011679416672751503)
    ·
      refine ⟨120026380517519125009127255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80017587011679416672751503 120026380517519125009127255)
      ·
        refine ⟨180039570776278687513690883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120026380517519125009127255 180039570776278687513690883)
        ·
          refine ⟨270059356164418031270536325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180039570776278687513690883 270059356164418031270536325)
          ·
            refine ⟨50636129280828380863225561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270059356164418031270536325 50636129280828380863225561)
            ·
              refine ⟨37977096960621285647419171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50636129280828380863225561 37977096960621285647419171)
              ·
                refine ⟨56965645440931928471128757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37977096960621285647419171 56965645440931928471128757)
                ·
                  refine ⟨5340529260087368294168321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56965645440931928471128757 5340529260087368294168321)
                  ·
                    refine ⟨4005396945065526220626241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5340529260087368294168321 4005396945065526220626241)
                    ·
                      refine ⟨3004047708799144665469681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005396945065526220626241 3004047708799144665469681)
                      ·
                        rfl

theorem cell23_5850362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_5850362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850362 prefixEnd_5850362 := by exact prefixLift 5850362
  have htrace : WordTrace (prefixWord ++ tailWord_5850362) baseStart_5850362 baseEnd_5850362 := by
    simpa [prefixWord, tailWord_5850362, baseEnd_5850362] using wordTrace_append hprefix tailTrace_5850362
  have hstable : (prefixWord ++ tailWord_5850362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850362).length < 2 ^ (prefixWord ++ tailWord_5850362).sum := by decide
  have hdescent : baseEnd_5850362 < baseStart_5850362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850382 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_5850382 : Nat := 118140960795 + 5850382 * 2 ^ 59
def prefixEnd_5850382 : Nat := 4983230072969 + 3 ^ 40 * 5850382 * 2
def baseEnd_5850382 : Nat := 3004057978412234587219589

theorem tailTrace_5850382 : CollatzResearch.WordTrace tailWord_5850382 prefixEnd_5850382 3004057978412234587219589 := by
  unfold tailWord_5850382
  simp only [CollatzResearch.WordTrace]
  refine ⟨26672620186384081817883175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142253974327381769695376933 26672620186384081817883175)
  ·
    refine ⟨40008930279576122726824763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26672620186384081817883175 40008930279576122726824763)
    ·
      refine ⟨60013395419364184090237145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40008930279576122726824763 60013395419364184090237145)
      ·
        refine ⟨45010046564523138067677859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60013395419364184090237145 45010046564523138067677859)
        ·
          refine ⟨67515069846784707101516789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45010046564523138067677859 67515069846784707101516789)
          ·
            refine ⟨6329537798136066290767199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67515069846784707101516789 6329537798136066290767199)
            ·
              refine ⟨9494306697204099436150799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329537798136066290767199 9494306697204099436150799)
              ·
                refine ⟨14241460045806149154226199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9494306697204099436150799 14241460045806149154226199)
                ·
                  refine ⟨21362190068709223731339299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14241460045806149154226199 21362190068709223731339299)
                  ·
                    refine ⟨32043285103063835597008949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21362190068709223731339299 32043285103063835597008949)
                    ·
                      refine ⟨3004057978412234587219589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32043285103063835597008949 3004057978412234587219589)
                      ·
                        rfl

theorem cell23_5850382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_5850382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850382 prefixEnd_5850382 := by exact prefixLift 5850382
  have htrace : WordTrace (prefixWord ++ tailWord_5850382) baseStart_5850382 baseEnd_5850382 := by
    simpa [prefixWord, tailWord_5850382, baseEnd_5850382] using wordTrace_append hprefix tailTrace_5850382
  have hstable : (prefixWord ++ tailWord_5850382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850382).length < 2 ^ (prefixWord ++ tailWord_5850382).sum := by decide
  have hdescent : baseEnd_5850382 < baseStart_5850382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850402 : List Nat := [3, 3, 1, 1, 4, 2, 1, 8]
def baseStart_5850402 : Nat := 118140960795 + 5850402 * 2 ^ 59
def prefixEnd_5850402 : Nat := 4983230072969 + 3 ^ 40 * 5850402 * 2
def baseEnd_5850402 : Nat := 111261786963900907739611

theorem tailTrace_5850402 : CollatzResearch.WordTrace tailWord_5850402 prefixEnd_5850402 111261786963900907739611 := by
  unfold tailWord_5850402
  simp only [CollatzResearch.WordTrace]
  refine ⟨53345422737750049489698365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142254460634000131972528973 53345422737750049489698365)
  ·
    refine ⟨20004533526656268558636887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53345422737750049489698365 20004533526656268558636887)
    ·
      refine ⟨30006800289984402837955331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20004533526656268558636887 30006800289984402837955331)
      ·
        refine ⟨45010200434976604256932997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30006800289984402837955331 45010200434976604256932997)
        ·
          refine ⟨8439412581558113298174937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45010200434976604256932997 8439412581558113298174937)
          ·
            refine ⟨6329559436168584973631203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8439412581558113298174937 6329559436168584973631203)
            ·
              refine ⟨9494339154252877460446805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329559436168584973631203 9494339154252877460446805)
              ·
                refine ⟨111261786963900907739611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9494339154252877460446805 111261786963900907739611)
                ·
                  rfl

theorem cell23_5850402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 8].length) (baseStart_5850402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850402 prefixEnd_5850402 := by exact prefixLift 5850402
  have htrace : WordTrace (prefixWord ++ tailWord_5850402) baseStart_5850402 baseEnd_5850402 := by
    simpa [prefixWord, tailWord_5850402, baseEnd_5850402] using wordTrace_append hprefix tailTrace_5850402
  have hstable : (prefixWord ++ tailWord_5850402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850402).length < 2 ^ (prefixWord ++ tailWord_5850402).sum := by decide
  have hdescent : baseEnd_5850402 < baseStart_5850402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850439 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_5850439 : Nat := 118140960795 + 5850439 * 2 ^ 59
def prefixEnd_5850439 : Nat := 4983230072969 + 3 ^ 40 * 5850439 * 2
def baseEnd_5850439 : Nat := 3004087246809540864206827

theorem tailTrace_5850439 : CollatzResearch.WordTrace tailWord_5850439 prefixEnd_5850439 3004087246809540864206827 := by
  unfold tailWord_5850439
  simp only [CollatzResearch.WordTrace]
  refine ⟨213383040451866153277890371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142255360301244102185260247 213383040451866153277890371)
  ·
    refine ⟨320074560677799229916835557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213383040451866153277890371 320074560677799229916835557)
    ·
      refine ⟨60013980127087355609406667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320074560677799229916835557 60013980127087355609406667)
      ·
        refine ⟨90020970190631033414110001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60013980127087355609406667 90020970190631033414110001)
        ·
          refine ⟨67515727642973275060582501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90020970190631033414110001 67515727642973275060582501)
          ·
            refine ⟨12659198933057489073859219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67515727642973275060582501 12659198933057489073859219)
            ·
              refine ⟨18988798399586233610788829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12659198933057489073859219 18988798399586233610788829)
              ·
                refine ⟨7120799399844837604045811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18988798399586233610788829 7120799399844837604045811)
                ·
                  refine ⟨10681199099767256406068717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7120799399844837604045811 10681199099767256406068717)
                  ·
                    refine ⟨4005449662412721152275769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10681199099767256406068717 4005449662412721152275769)
                    ·
                      refine ⟨3004087246809540864206827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005449662412721152275769 3004087246809540864206827)
                      ·
                        rfl

theorem cell23_5850439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_5850439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850439 prefixEnd_5850439 := by exact prefixLift 5850439
  have htrace : WordTrace (prefixWord ++ tailWord_5850439) baseStart_5850439 baseEnd_5850439 := by
    simpa [prefixWord, tailWord_5850439, baseEnd_5850439] using wordTrace_append hprefix tailTrace_5850439
  have hstable : (prefixWord ++ tailWord_5850439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850439).length < 2 ^ (prefixWord ++ tailWord_5850439).sum := by decide
  have hdescent : baseEnd_5850439 < baseStart_5850439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850520 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5850520 : Nat := 118140960795 + 5850520 * 2 ^ 59
def prefixEnd_5850520 : Nat := 4983230072969 + 3 ^ 40 * 5850520 * 2
def baseEnd_5850520 : Nat := 3004128838742555047293955

theorem tailTrace_5850520 : CollatzResearch.WordTrace tailWord_5850520 prefixEnd_5850520 3004128838742555047293955 := by
  unfold tailWord_5850520
  simp only [CollatzResearch.WordTrace]
  refine ⟨106692997382286352055794507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142257329843048469407726009 106692997382286352055794507)
  ·
    refine ⟨160039496073429528083691761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106692997382286352055794507 160039496073429528083691761)
    ·
      refine ⟨120029622055072146062768821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160039496073429528083691761 120029622055072146062768821)
      ·
        refine ⟨11252777067663013693384577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120029622055072146062768821 11252777067663013693384577)
        ·
          refine ⟨8439582800747260270038433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11252777067663013693384577 8439582800747260270038433)
          ·
            refine ⟨6329687100560445202528825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8439582800747260270038433 6329687100560445202528825)
            ·
              refine ⟨4747265325420333901896619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6329687100560445202528825 4747265325420333901896619)
              ·
                refine ⟨7120897988130500852844929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747265325420333901896619 7120897988130500852844929)
                ·
                  refine ⟨5340673491097875639633697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7120897988130500852844929 5340673491097875639633697)
                  ·
                    refine ⟨4005505118323406729725273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5340673491097875639633697 4005505118323406729725273)
                    ·
                      refine ⟨3004128838742555047293955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005505118323406729725273 3004128838742555047293955)
                      ·
                        rfl

theorem cell23_5850520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5850520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850520 prefixEnd_5850520 := by exact prefixLift 5850520
  have htrace : WordTrace (prefixWord ++ tailWord_5850520) baseStart_5850520 baseEnd_5850520 := by
    simpa [prefixWord, tailWord_5850520, baseEnd_5850520] using wordTrace_append hprefix tailTrace_5850520
  have hstable : (prefixWord ++ tailWord_5850520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850520).length < 2 ^ (prefixWord ++ tailWord_5850520).sum := by decide
  have hdescent : baseEnd_5850520 < baseStart_5850520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850632 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_5850632 : Nat := 118140960795 + 5850632 * 2 ^ 59
def prefixEnd_5850632 : Nat := 4983230072969 + 3 ^ 40 * 5850632 * 2
def baseEnd_5850632 : Nat := 3004186348575858609093439

theorem tailTrace_5850632 : CollatzResearch.WordTrace tailWord_5850632 prefixEnd_5850632 3004186348575858609093439 := by
  unfold tailWord_5850632
  simp only [CollatzResearch.WordTrace]
  refine ⟨106695039870083473619833075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142260053160111298159777433 106695039870083473619833075)
  ·
    refine ⟨160042559805125210429749613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106695039870083473619833075 160042559805125210429749613)
    ·
      refine ⟨60015959926921953911156105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160042559805125210429749613 60015959926921953911156105)
      ·
        refine ⟨45011969945191465433367079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60015959926921953911156105 45011969945191465433367079)
        ·
          refine ⟨67517954917787198150050619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45011969945191465433367079 67517954917787198150050619)
          ·
            refine ⟨101276932376680797225075929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67517954917787198150050619 101276932376680797225075929)
            ·
              refine ⟨75957699282510597918806947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101276932376680797225075929 75957699282510597918806947)
              ·
                refine ⟨113936548923765896878210421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75957699282510597918806947 113936548923765896878210421)
                ·
                  refine ⟨10681551461603052832332227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113936548923765896878210421 10681551461603052832332227)
                  ·
                    refine ⟨16022327192404579248498341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10681551461603052832332227 16022327192404579248498341)
                    ·
                      refine ⟨3004186348575858609093439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16022327192404579248498341 3004186348575858609093439)
                      ·
                        rfl

theorem cell23_5850632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_5850632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850632 prefixEnd_5850632 := by exact prefixLift 5850632
  have htrace : WordTrace (prefixWord ++ tailWord_5850632) baseStart_5850632 baseEnd_5850632 := by
    simpa [prefixWord, tailWord_5850632, baseEnd_5850632] using wordTrace_append hprefix tailTrace_5850632
  have hstable : (prefixWord ++ tailWord_5850632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850632).length < 2 ^ (prefixWord ++ tailWord_5850632).sum := by decide
  have hdescent : baseEnd_5850632 < baseStart_5850632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850652 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_5850652 : Nat := 118140960795 + 5850652 * 2 ^ 59
def prefixEnd_5850652 : Nat := 4983230072969 + 3 ^ 40 * 5850652 * 2
def baseEnd_5850652 : Nat := 3004196618188948530843347

theorem tailTrace_5850652 : CollatzResearch.WordTrace tailWord_5850652 prefixEnd_5850652 3004196618188948530843347 := by
  unfold tailWord_5850652
  simp only [CollatzResearch.WordTrace]
  refine ⟨106695404600047245327697105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142260539466729660436929473 106695404600047245327697105)
  ·
    refine ⟨80021553450035433995772829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106695404600047245327697105 80021553450035433995772829)
    ·
      refine ⟨30008082543763287748414811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80021553450035433995772829 30008082543763287748414811)
      ·
        refine ⟨45012123815644931622622217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30008082543763287748414811 45012123815644931622622217)
        ·
          refine ⟨33759092861733698716966663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45012123815644931622622217 33759092861733698716966663)
          ·
            refine ⟨50638639292600548075449995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33759092861733698716966663 50638639292600548075449995)
            ·
              refine ⟨75957958938900822113174993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50638639292600548075449995 75957958938900822113174993)
              ·
                refine ⟨56968469204175616584881245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75957958938900822113174993 56968469204175616584881245)
                ·
                  refine ⟨21363175951565856219330467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56968469204175616584881245 21363175951565856219330467)
                  ·
                    refine ⟨32044763927348784328995701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21363175951565856219330467 32044763927348784328995701)
                    ·
                      refine ⟨3004196618188948530843347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32044763927348784328995701 3004196618188948530843347)
                      ·
                        rfl

theorem cell23_5850652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_5850652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850652 prefixEnd_5850652 := by exact prefixLift 5850652
  have htrace : WordTrace (prefixWord ++ tailWord_5850652) baseStart_5850652 baseEnd_5850652 := by
    simpa [prefixWord, tailWord_5850652, baseEnd_5850652] using wordTrace_append hprefix tailTrace_5850652
  have hstable : (prefixWord ++ tailWord_5850652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850652).length < 2 ^ (prefixWord ++ tailWord_5850652).sum := by decide
  have hdescent : baseEnd_5850652 < baseStart_5850652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850654 : List Nat := [4, 3, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5850654 : Nat := 118140960795 + 5850654 * 2 ^ 59
def prefixEnd_5850654 : Nat := 4983230072969 + 3 ^ 40 * 5850654 * 2
def baseEnd_5850654 : Nat := 1001399215050085841006113

theorem tailTrace_5850654 : CollatzResearch.WordTrace tailWord_5850654 prefixEnd_5850654 1001399215050085841006113 := by
  unfold tailWord_5850654
  simp only [CollatzResearch.WordTrace]
  refine ⟨26673860268260905624620877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142260588097391496664644677 26673860268260905624620877)
  ·
    refine ⟨10002697600597839609232829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26673860268260905624620877 10002697600597839609232829)
    ·
      refine ⟨3751011600224189853462311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10002697600597839609232829 3751011600224189853462311)
      ·
        refine ⟨5626517400336284780193467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751011600224189853462311 5626517400336284780193467)
        ·
          refine ⟨8439776100504427170290201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626517400336284780193467 8439776100504427170290201)
          ·
            refine ⟨6329832075378320377717651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8439776100504427170290201 6329832075378320377717651)
            ·
              refine ⟨9494748113067480566576477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329832075378320377717651 9494748113067480566576477)
              ·
                refine ⟨3560530542400305212466179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9494748113067480566576477 3560530542400305212466179)
                ·
                  refine ⟨5340795813600457818699269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560530542400305212466179 5340795813600457818699269)
                  ·
                    refine ⟨1001399215050085841006113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5340795813600457818699269 1001399215050085841006113)
                    ·
                      rfl

theorem cell23_5850654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5850654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850654 prefixEnd_5850654 := by exact prefixLift 5850654
  have htrace : WordTrace (prefixWord ++ tailWord_5850654) baseStart_5850654 baseEnd_5850654 := by
    simpa [prefixWord, tailWord_5850654, baseEnd_5850654] using wordTrace_append hprefix tailTrace_5850654
  have hstable : (prefixWord ++ tailWord_5850654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850654).length < 2 ^ (prefixWord ++ tailWord_5850654).sum := by decide
  have hdescent : baseEnd_5850654 < baseStart_5850654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850716 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_5850716 : Nat := 118140960795 + 5850716 * 2 ^ 59
def prefixEnd_5850716 : Nat := 4983230072969 + 3 ^ 40 * 5850716 * 2
def baseEnd_5850716 : Nat := 3004229480950836280443053

theorem tailTrace_5850716 : CollatzResearch.WordTrace tailWord_5850716 prefixEnd_5850716 3004229480950836280443053 := by
  unfold tailWord_5850716
  simp only [CollatzResearch.WordTrace]
  refine ⟨106696571735931314792862001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142262095647908419723816001 106696571735931314792862001)
  ·
    refine ⟨80022428801948486094646501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106696571735931314792862001 80022428801948486094646501)
    ·
      refine ⟨15004205400365341142746219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80022428801948486094646501 15004205400365341142746219)
      ·
        refine ⟨22506308100548011714119329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15004205400365341142746219 22506308100548011714119329)
        ·
          refine ⟨16879731075411008785589497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22506308100548011714119329 16879731075411008785589497)
          ·
            refine ⟨12659798306558256589192123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16879731075411008785589497 12659798306558256589192123)
            ·
              refine ⟨18989697459837384883788185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12659798306558256589192123 18989697459837384883788185)
              ·
                refine ⟨14242273094878038662841139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18989697459837384883788185 14242273094878038662841139)
                ·
                  refine ⟨21363409642317057994261709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14242273094878038662841139 21363409642317057994261709)
                  ·
                    refine ⟨8011278615868896747848141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21363409642317057994261709 8011278615868896747848141)
                    ·
                      refine ⟨3004229480950836280443053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011278615868896747848141 3004229480950836280443053)
                      ·
                        rfl

theorem cell23_5850716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_5850716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850716 prefixEnd_5850716 := by exact prefixLift 5850716
  have htrace : WordTrace (prefixWord ++ tailWord_5850716) baseStart_5850716 baseEnd_5850716 := by
    simpa [prefixWord, tailWord_5850716, baseEnd_5850716] using wordTrace_append hprefix tailTrace_5850716
  have hstable : (prefixWord ++ tailWord_5850716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850716).length < 2 ^ (prefixWord ++ tailWord_5850716).sum := by decide
  have hdescent : baseEnd_5850716 < baseStart_5850716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850732 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_5850732 : Nat := 118140960795 + 5850732 * 2 ^ 59
def prefixEnd_5850732 : Nat := 4983230072969 + 3 ^ 40 * 5850732 * 2
def baseEnd_5850732 : Nat := 1001412565547102739280993

theorem tailTrace_5850732 : CollatzResearch.WordTrace tailWord_5850732 prefixEnd_5850732 1001412565547102739280993 := by
  unfold tailWord_5850732
  simp only [CollatzResearch.WordTrace]
  refine ⟨106696863519902332159153225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142262484693203109545537633 106696863519902332159153225)
  ·
    refine ⟨80022647639926749119364919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106696863519902332159153225 80022647639926749119364919)
    ·
      refine ⟨120033971459890123679047379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80022647639926749119364919 120033971459890123679047379)
      ·
        refine ⟨180050957189835185518571069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120033971459890123679047379 180050957189835185518571069)
        ·
          refine ⟨67519108946188194569464151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180050957189835185518571069 67519108946188194569464151)
          ·
            refine ⟨101278663419282291854196227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67519108946188194569464151 101278663419282291854196227)
            ·
              refine ⟨151917995128923437781294341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101278663419282291854196227 151917995128923437781294341)
              ·
                refine ⟨28484624086673144583992689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151917995128923437781294341 28484624086673144583992689)
                ·
                  refine ⟨21363468065004858437994517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28484624086673144583992689 21363468065004858437994517)
                  ·
                    refine ⟨1001412565547102739280993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21363468065004858437994517 1001412565547102739280993)
                    ·
                      rfl

theorem cell23_5850732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_5850732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850732 prefixEnd_5850732 := by exact prefixLift 5850732
  have htrace : WordTrace (prefixWord ++ tailWord_5850732) baseStart_5850732 baseEnd_5850732 := by
    simpa [prefixWord, tailWord_5850732, baseEnd_5850732] using wordTrace_append hprefix tailTrace_5850732
  have hstable : (prefixWord ++ tailWord_5850732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850732).length < 2 ^ (prefixWord ++ tailWord_5850732).sum := by decide
  have hdescent : baseEnd_5850732 < baseStart_5850732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850734 : List Nat := [4, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_5850734 : Nat := 118140960795 + 5850734 * 2 ^ 59
def prefixEnd_5850734 : Nat := 4983230072969 + 3 ^ 40 * 5850734 * 2
def baseEnd_5850734 : Nat := 3004238723602617210017971

theorem tailTrace_5850734 : CollatzResearch.WordTrace tailWord_5850734 prefixEnd_5850734 3004238723602617210017971 := by
  unfold tailWord_5850734
  simp only [CollatzResearch.WordTrace]
  refine ⟨26674224998224677332484907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142262533323864945773252837 26674224998224677332484907)
  ·
    refine ⟨40011337497337015998727361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26674224998224677332484907 40011337497337015998727361)
    ·
      refine ⟨30008503123002761999045521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40011337497337015998727361 30008503123002761999045521)
      ·
        refine ⟨22506377342252071499284141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30008503123002761999045521 22506377342252071499284141)
        ·
          refine ⟨8439891503344526812231553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22506377342252071499284141 8439891503344526812231553)
          ·
            refine ⟨6329918627508395109173665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8439891503344526812231553 6329918627508395109173665)
            ·
              refine ⟨4747438970631296331880249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6329918627508395109173665 4747438970631296331880249)
              ·
                refine ⟨3560579227973472248910187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4747438970631296331880249 3560579227973472248910187)
                ·
                  refine ⟨5340868841960208373365281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560579227973472248910187 5340868841960208373365281)
                  ·
                    refine ⟨4005651631470156280023961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5340868841960208373365281 4005651631470156280023961)
                    ·
                      refine ⟨3004238723602617210017971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005651631470156280023961 3004238723602617210017971)
                      ·
                        rfl

theorem cell23_5850734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_5850734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850734 prefixEnd_5850734 := by exact prefixLift 5850734
  have htrace : WordTrace (prefixWord ++ tailWord_5850734) baseStart_5850734 baseEnd_5850734 := by
    simpa [prefixWord, tailWord_5850734, baseEnd_5850734] using wordTrace_append hprefix tailTrace_5850734
  have hstable : (prefixWord ++ tailWord_5850734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850734).length < 2 ^ (prefixWord ++ tailWord_5850734).sum := by decide
  have hdescent : baseEnd_5850734 < baseStart_5850734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850749 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_5850749 : Nat := 118140960795 + 5850749 * 2 ^ 59
def prefixEnd_5850749 : Nat := 4983230072969 + 3 ^ 40 * 5850749 * 2
def baseEnd_5850749 : Nat := 1001415475270811550443467

theorem tailTrace_5850749 : CollatzResearch.WordTrace tailWord_5850749 prefixEnd_5850749 1001415475270811550443467 := by
  unfold tailWord_5850749
  simp only [CollatzResearch.WordTrace]
  refine ⟨213394347080743076221675301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142262898053828717481116867 213394347080743076221675301)
  ·
    refine ⟨40011440077639326791564119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213394347080743076221675301 40011440077639326791564119)
    ·
      refine ⟨60017160116458990187346179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40011440077639326791564119 60017160116458990187346179)
      ·
        refine ⟨90025740174688485281019269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60017160116458990187346179 90025740174688485281019269)
        ·
          refine ⟨16879826282754090990191113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90025740174688485281019269 16879826282754090990191113)
          ·
            refine ⟨12659869712065568242643335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16879826282754090990191113 12659869712065568242643335)
            ·
              refine ⟨18989804568098352363965003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12659869712065568242643335 18989804568098352363965003)
              ·
                refine ⟨28484706852147528545947505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18989804568098352363965003 28484706852147528545947505)
                ·
                  refine ⟨21363530139110646409460629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28484706852147528545947505 21363530139110646409460629)
                  ·
                    refine ⟨1001415475270811550443467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21363530139110646409460629 1001415475270811550443467)
                    ·
                      rfl

theorem cell23_5850749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_5850749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850749 prefixEnd_5850749 := by exact prefixLift 5850749
  have htrace : WordTrace (prefixWord ++ tailWord_5850749) baseStart_5850749 baseEnd_5850749 := by
    simpa [prefixWord, tailWord_5850749, baseEnd_5850749] using wordTrace_append hprefix tailTrace_5850749
  have hstable : (prefixWord ++ tailWord_5850749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850749).length < 2 ^ (prefixWord ++ tailWord_5850749).sum := by decide
  have hdescent : baseEnd_5850749 < baseStart_5850749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850789 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_5850789 : Nat := 118140960795 + 5850789 * 2 ^ 59
def prefixEnd_5850789 : Nat := 4983230072969 + 3 ^ 40 * 5850789 * 2
def baseEnd_5850789 : Nat := 3004266965038614494830217

theorem tailTrace_5850789 : CollatzResearch.WordTrace tailWord_5850789 prefixEnd_5850789 3004266965038614494830217 := by
  unfold tailWord_5850789
  simp only [CollatzResearch.WordTrace]
  refine ⟨213395806000598163053131421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142263870667065442035420947 213395806000598163053131421)
  ·
    refine ⟨80023427250224311144924283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213395806000598163053131421 80023427250224311144924283)
    ·
      refine ⟨120035140875336466717386425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80023427250224311144924283 120035140875336466717386425)
      ·
        refine ⟨90026355656502350038039819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120035140875336466717386425 90026355656502350038039819)
        ·
          refine ⟨135039533484753525057059729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90026355656502350038039819 135039533484753525057059729)
          ·
            refine ⟨101279650113565143792794797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135039533484753525057059729 101279650113565143792794797)
            ·
              refine ⟨37979868792586928922298049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101279650113565143792794797 37979868792586928922298049)
              ·
                refine ⟨28484901594440196691723537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37979868792586928922298049 28484901594440196691723537)
                ·
                  refine ⟨21363676195830147518792653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28484901594440196691723537 21363676195830147518792653)
                  ·
                    refine ⟨8011378573436305319547245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21363676195830147518792653 8011378573436305319547245)
                    ·
                      refine ⟨3004266965038614494830217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011378573436305319547245 3004266965038614494830217)
                      ·
                        rfl

theorem cell23_5850789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_5850789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850789 prefixEnd_5850789 := by exact prefixLift 5850789
  have htrace : WordTrace (prefixWord ++ tailWord_5850789) baseStart_5850789 baseEnd_5850789 := by
    simpa [prefixWord, tailWord_5850789, baseEnd_5850789] using wordTrace_append hprefix tailTrace_5850789
  have hstable : (prefixWord ++ tailWord_5850789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850789).length < 2 ^ (prefixWord ++ tailWord_5850789).sum := by decide
  have hdescent : baseEnd_5850789 < baseStart_5850789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850866 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_5850866 : Nat := 118140960795 + 5850866 * 2 ^ 59
def prefixEnd_5850866 : Nat := 4983230072969 + 3 ^ 40 * 5850866 * 2
def baseEnd_5850866 : Nat := 3004306503049010693567363

theorem tailTrace_5850866 : CollatzResearch.WordTrace tailWord_5850866 prefixEnd_5850866 3004306503049010693567363 := by
  unfold tailWord_5850866
  simp only [CollatzResearch.WordTrace]
  refine ⟨53349653605329801300921113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142265742947546136802456301 53349653605329801300921113)
  ·
    refine ⟨40012240203997350975690835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53349653605329801300921113 40012240203997350975690835)
    ·
      refine ⟨60018360305996026463536253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40012240203997350975690835 60018360305996026463536253)
      ·
        refine ⟨22506885114748509923826095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60018360305996026463536253 22506885114748509923826095)
        ·
          refine ⟨33760327672122764885739143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22506885114748509923826095 33760327672122764885739143)
          ·
            refine ⟨50640491508184147328608715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33760327672122764885739143 50640491508184147328608715)
            ·
              refine ⟨75960737262276220992913073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50640491508184147328608715 75960737262276220992913073)
              ·
                refine ⟨56970552946707165744684805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75960737262276220992913073 56970552946707165744684805)
                ·
                  refine ⟨10681978677507593577128401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56970552946707165744684805 10681978677507593577128401)
                  ·
                    refine ⟨8011484008130695182846301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10681978677507593577128401 8011484008130695182846301)
                    ·
                      refine ⟨3004306503049010693567363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011484008130695182846301 3004306503049010693567363)
                      ·
                        rfl

theorem cell23_5850866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_5850866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850866 prefixEnd_5850866 := by exact prefixLift 5850866
  have htrace : WordTrace (prefixWord ++ tailWord_5850866) baseStart_5850866 baseEnd_5850866 := by
    simpa [prefixWord, tailWord_5850866, baseEnd_5850866] using wordTrace_append hprefix tailTrace_5850866
  have hstable : (prefixWord ++ tailWord_5850866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850866).length < 2 ^ (prefixWord ++ tailWord_5850866).sum := by decide
  have hdescent : baseEnd_5850866 < baseStart_5850866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850879 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 3]
def baseStart_5850879 : Nat := 118140960795 + 5850879 * 2 ^ 59
def prefixEnd_5850879 : Nat := 4983230072969 + 3 ^ 40 * 5850879 * 2
def baseEnd_5850879 : Nat := 3004313178297519142704803

theorem tailTrace_5850879 : CollatzResearch.WordTrace tailWord_5850879 prefixEnd_5850879 3004313178297519142704803 := by
  unfold tailWord_5850879
  simp only [CollatzResearch.WordTrace]
  refine ⟨213399088570272108423907691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142266059046848072282605127 213399088570272108423907691)
  ·
    refine ⟨320098632855408162635861537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213399088570272108423907691 320098632855408162635861537)
    ·
      refine ⟨240073974641556121976896153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320098632855408162635861537 240073974641556121976896153)
      ·
        refine ⟨180055480981167091482672115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240073974641556121976896153 180055480981167091482672115)
        ·
          refine ⟨270083221471750637224008173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180055480981167091482672115 270083221471750637224008173)
          ·
            refine ⟨101281208051906488959003065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270083221471750637224008173 101281208051906488959003065)
            ·
              refine ⟨75960906038929866719252299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101281208051906488959003065 75960906038929866719252299)
              ·
                refine ⟨113941359058394800078878449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75960906038929866719252299 113941359058394800078878449)
                ·
                  refine ⟨85456019293796100059158837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113941359058394800078878449 85456019293796100059158837)
                  ·
                    refine ⟨8011501808793384380546141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85456019293796100059158837 8011501808793384380546141)
                    ·
                      refine ⟨3004313178297519142704803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011501808793384380546141 3004313178297519142704803)
                      ·
                        rfl

theorem cell23_5850879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_5850879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850879 prefixEnd_5850879 := by exact prefixLift 5850879
  have htrace : WordTrace (prefixWord ++ tailWord_5850879) baseStart_5850879 baseEnd_5850879 := by
    simpa [prefixWord, tailWord_5850879, baseEnd_5850879] using wordTrace_append hprefix tailTrace_5850879
  have hstable : (prefixWord ++ tailWord_5850879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850879).length < 2 ^ (prefixWord ++ tailWord_5850879).sum := by decide
  have hdescent : baseEnd_5850879 < baseStart_5850879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850916 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_5850916 : Nat := 118140960795 + 5850916 * 2 ^ 59
def prefixEnd_5850916 : Nat := 4983230072969 + 3 ^ 40 * 5850916 * 2
def baseEnd_5850916 : Nat := 1001444059027245165980711

theorem tailTrace_5850916 : CollatzResearch.WordTrace tailWord_5850916 prefixEnd_5850916 1001444059027245165980711 := by
  unfold tailWord_5850916
  simp only [CollatzResearch.WordTrace]
  refine ⟨106700219035569031871502301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142266958714092042495336401 106700219035569031871502301)
  ·
    refine ⟨40012582138338386951813363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106700219035569031871502301 40012582138338386951813363)
    ·
      refine ⟨60018873207507580427720045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40012582138338386951813363 60018873207507580427720045)
      ·
        refine ⟨22507077452815342660395017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60018873207507580427720045 22507077452815342660395017)
        ·
          refine ⟨16880308089611506995296263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22507077452815342660395017 16880308089611506995296263)
          ·
            refine ⟨25320462134417260492944395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16880308089611506995296263 25320462134417260492944395)
            ·
              refine ⟨37980693201625890739416593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25320462134417260492944395 37980693201625890739416593)
              ·
                refine ⟨28485519901219418054562445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37980693201625890739416593 28485519901219418054562445)
                ·
                  refine ⟨10682069962957281770460917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28485519901219418054562445 10682069962957281770460917)
                  ·
                    refine ⟨1001444059027245165980711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10682069962957281770460917 1001444059027245165980711)
                    ·
                      rfl

theorem cell23_5850916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_5850916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850916 prefixEnd_5850916 := by exact prefixLift 5850916
  have htrace : WordTrace (prefixWord ++ tailWord_5850916) baseStart_5850916 baseEnd_5850916 := by
    simpa [prefixWord, tailWord_5850916, baseEnd_5850916] using wordTrace_append hprefix tailTrace_5850916
  have hstable : (prefixWord ++ tailWord_5850916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850916).length < 2 ^ (prefixWord ++ tailWord_5850916).sum := by decide
  have hdescent : baseEnd_5850916 < baseStart_5850916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850936 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_5850936 : Nat := 118140960795 + 5850936 * 2 ^ 59
def prefixEnd_5850936 : Nat := 4983230072969 + 3 ^ 40 * 5850936 * 2
def baseEnd_5850936 : Nat := 3004342446694825419692041

theorem tailTrace_5850936 : CollatzResearch.WordTrace tailWord_5850936 prefixEnd_5850936 3004342446694825419692041 := by
  unfold tailWord_5850936
  simp only [CollatzResearch.WordTrace]
  refine ⟨106700583765532803579366331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142267445020710404772488441 106700583765532803579366331)
  ·
    refine ⟨160050875648299205369049497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106700583765532803579366331 160050875648299205369049497)
    ·
      refine ⟨120038156736224404026787123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160050875648299205369049497 120038156736224404026787123)
      ·
        refine ⟨180057235104336606040180685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120038156736224404026787123 180057235104336606040180685)
        ·
          refine ⟨67521463164126227265067757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180057235104336606040180685 67521463164126227265067757)
          ·
            refine ⟨25320548686547335224400409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67521463164126227265067757 25320548686547335224400409)
            ·
              refine ⟨18990411514910501418300307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25320548686547335224400409 18990411514910501418300307)
              ·
                refine ⟨28485617272365752127450461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18990411514910501418300307 28485617272365752127450461)
                ·
                  refine ⟨10682106477137157047793923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28485617272365752127450461 10682106477137157047793923)
                  ·
                    refine ⟨16023159715705735571690885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10682106477137157047793923 16023159715705735571690885)
                    ·
                      refine ⟨3004342446694825419692041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16023159715705735571690885 3004342446694825419692041)
                      ·
                        rfl

theorem cell23_5850936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_5850936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850936 prefixEnd_5850936 := by exact prefixLift 5850936
  have htrace : WordTrace (prefixWord ++ tailWord_5850936) baseStart_5850936 baseEnd_5850936 := by
    simpa [prefixWord, tailWord_5850936, baseEnd_5850936] using wordTrace_append hprefix tailTrace_5850936
  have hstable : (prefixWord ++ tailWord_5850936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850936).length < 2 ^ (prefixWord ++ tailWord_5850936).sum := by decide
  have hdescent : baseEnd_5850936 < baseStart_5850936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850953 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 5, 2, 2]
def baseStart_5850953 : Nat := 118140960795 + 5850953 * 2 ^ 59
def prefixEnd_5850953 : Nat := 4983230072969 + 3 ^ 40 * 5850953 * 2
def baseEnd_5850953 : Nat := 3004351175865951853179463

theorem tailTrace_5850953 : CollatzResearch.WordTrace tailWord_5850953 prefixEnd_5850953 3004351175865951853179463 := by
  unfold tailWord_5850953
  simp only [CollatzResearch.WordTrace]
  refine ⟨213401787572004019062101513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142267858381336012708067675 213401787572004019062101513)
  ·
    refine ⟨160051340679003014296576135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213401787572004019062101513 160051340679003014296576135)
    ·
      refine ⟨240077011018504521444864203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160051340679003014296576135 240077011018504521444864203)
      ·
        refine ⟨360115516527756782167296305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240077011018504521444864203 360115516527756782167296305)
        ·
          refine ⟨270086637395817586625472229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360115516527756782167296305 270086637395817586625472229)
          ·
            refine ⟨50641244511715797492276043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270086637395817586625472229 50641244511715797492276043)
            ·
              refine ⟨75961866767573696238414065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50641244511715797492276043 75961866767573696238414065)
              ·
                refine ⟨56971400075680272178810549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75961866767573696238414065 56971400075680272178810549)
                ·
                  refine ⟨5341068757095025516763489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56971400075680272178810549 5341068757095025516763489)
                  ·
                    refine ⟨4005801567821269137572617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341068757095025516763489 4005801567821269137572617)
                    ·
                      refine ⟨3004351175865951853179463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005801567821269137572617 3004351175865951853179463)
                      ·
                        rfl

theorem cell23_5850953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 2, 2].length) (baseStart_5850953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850953 prefixEnd_5850953 := by exact prefixLift 5850953
  have htrace : WordTrace (prefixWord ++ tailWord_5850953) baseStart_5850953 baseEnd_5850953 := by
    simpa [prefixWord, tailWord_5850953, baseEnd_5850953] using wordTrace_append hprefix tailTrace_5850953
  have hstable : (prefixWord ++ tailWord_5850953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850953).length < 2 ^ (prefixWord ++ tailWord_5850953).sum := by decide
  have hdescent : baseEnd_5850953 < baseStart_5850953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850970 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2]
def baseStart_5850970 : Nat := 118140960795 + 5850970 * 2 ^ 59
def prefixEnd_5850970 : Nat := 4983230072969 + 3 ^ 40 * 5850970 * 2
def baseEnd_5850970 : Nat := 3004359905037078286666885

theorem tailTrace_5850970 : CollatzResearch.WordTrace tailWord_5850970 prefixEnd_5850970 3004359905037078286666885 := by
  unfold tailWord_5850970
  simp only [CollatzResearch.WordTrace]
  refine ⟨53350601903235607741367591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142268271741961620643646909 53350601903235607741367591)
  ·
    refine ⟨80025902854853411612051387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53350601903235607741367591 80025902854853411612051387)
    ·
      refine ⟨120038854282280117418077081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80025902854853411612051387 120038854282280117418077081)
      ·
        refine ⟨90029140711710088063557811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120038854282280117418077081 90029140711710088063557811)
        ·
          refine ⟨135043711067565132095336717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90029140711710088063557811 135043711067565132095336717)
          ·
            refine ⟨50641391650336924535751269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135043711067565132095336717 50641391650336924535751269)
            ·
              refine ⟨9495260934438173350453363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50641391650336924535751269 9495260934438173350453363)
              ·
                refine ⟨14242891401657260025680045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495260934438173350453363 14242891401657260025680045)
                ·
                  refine ⟨5341084275621472509630017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14242891401657260025680045 5341084275621472509630017)
                  ·
                    refine ⟨4005813206716104382222513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341084275621472509630017 4005813206716104382222513)
                    ·
                      refine ⟨3004359905037078286666885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005813206716104382222513 3004359905037078286666885)
                      ·
                        rfl

theorem cell23_5850970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_5850970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850970 prefixEnd_5850970 := by exact prefixLift 5850970
  have htrace : WordTrace (prefixWord ++ tailWord_5850970) baseStart_5850970 baseEnd_5850970 := by
    simpa [prefixWord, tailWord_5850970, baseEnd_5850970] using wordTrace_append hprefix tailTrace_5850970
  have hstable : (prefixWord ++ tailWord_5850970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850970).length < 2 ^ (prefixWord ++ tailWord_5850970).sum := by decide
  have hdescent : baseEnd_5850970 < baseStart_5850970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850980 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_5850980 : Nat := 118140960795 + 5850980 * 2 ^ 59
def prefixEnd_5850980 : Nat := 4983230072969 + 3 ^ 40 * 5850980 * 2
def baseEnd_5850980 : Nat := 1001455013281207749180613

theorem tailTrace_5850980 : CollatzResearch.WordTrace tailWord_5850980 prefixEnd_5850980 1001455013281207749180613 := by
  unfold tailWord_5850980
  simp only [CollatzResearch.WordTrace]
  refine ⟨106701386171453101336667197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142268514895270801782222929 106701386171453101336667197)
  ·
    refine ⟨40013019814294913001250199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106701386171453101336667197 40013019814294913001250199)
    ·
      refine ⟨60019529721442369501875299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40013019814294913001250199 60019529721442369501875299)
      ·
        refine ⟨90029294582163554252812949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60019529721442369501875299 90029294582163554252812949)
        ·
          refine ⟨4220123183538916605600607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90029294582163554252812949 4220123183538916605600607)
          ·
            refine ⟨6330184775308374908400911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220123183538916605600607 6330184775308374908400911)
            ·
              refine ⟨9495277162962562362601367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330184775308374908400911 9495277162962562362601367)
              ·
                refine ⟨14242915744443843543902051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495277162962562362601367 14242915744443843543902051)
                ·
                  refine ⟨21364373616665765315853077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14242915744443843543902051 21364373616665765315853077)
                  ·
                    refine ⟨1001455013281207749180613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21364373616665765315853077 1001455013281207749180613)
                    ·
                      rfl

theorem cell23_5850980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_5850980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850980 prefixEnd_5850980 := by exact prefixLift 5850980
  have htrace : WordTrace (prefixWord ++ tailWord_5850980) baseStart_5850980 baseEnd_5850980 := by
    simpa [prefixWord, tailWord_5850980, baseEnd_5850980] using wordTrace_append hprefix tailTrace_5850980
  have hstable : (prefixWord ++ tailWord_5850980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850980).length < 2 ^ (prefixWord ++ tailWord_5850980).sum := by decide
  have hdescent : baseEnd_5850980 < baseStart_5850980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5850990 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5850990 : Nat := 118140960795 + 5850990 * 2 ^ 59
def prefixEnd_5850990 : Nat := 4983230072969 + 3 ^ 40 * 5850990 * 2
def baseEnd_5850990 : Nat := 3004370174650168208416793

theorem tailTrace_5850990 : CollatzResearch.WordTrace tailWord_5850990 prefixEnd_5850990 3004370174650168208416793 := by
  unfold tailWord_5850990
  simp only [CollatzResearch.WordTrace]
  refine ⟨26675392134108746797649803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142268758048579982920798949 26675392134108746797649803)
  ·
    refine ⟨40013088201163120196474705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26675392134108746797649803 40013088201163120196474705)
    ·
      refine ⟨30009816150872340147356029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40013088201163120196474705 30009816150872340147356029)
      ·
        refine ⟨11253681056577127555258511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30009816150872340147356029 11253681056577127555258511)
        ·
          refine ⟨16880521584865691332887767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11253681056577127555258511 16880521584865691332887767)
          ·
            refine ⟨25320782377298536999331651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16880521584865691332887767 25320782377298536999331651)
            ·
              refine ⟨37981173565947805498997477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25320782377298536999331651 37981173565947805498997477)
              ·
                refine ⟨7121470043615213531062027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37981173565947805498997477 7121470043615213531062027)
                ·
                  refine ⟨10682205065422820296593041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7121470043615213531062027 10682205065422820296593041)
                  ·
                    refine ⟨8011653799067115222444781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10682205065422820296593041 8011653799067115222444781)
                    ·
                      refine ⟨3004370174650168208416793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011653799067115222444781 3004370174650168208416793)
                      ·
                        rfl

theorem cell23_5850990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5850990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5850990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5850990 prefixEnd_5850990 := by exact prefixLift 5850990
  have htrace : WordTrace (prefixWord ++ tailWord_5850990) baseStart_5850990 baseEnd_5850990 := by
    simpa [prefixWord, tailWord_5850990, baseEnd_5850990] using wordTrace_append hprefix tailTrace_5850990
  have hstable : (prefixWord ++ tailWord_5850990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5850990).length < 2 ^ (prefixWord ++ tailWord_5850990).sum := by decide
  have hdescent : baseEnd_5850990 < baseStart_5850990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5850990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851037 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_5851037 : Nat := 118140960795 + 5851037 * 2 ^ 59
def prefixEnd_5851037 : Nat := 4983230072969 + 3 ^ 40 * 5851037 * 2
def baseEnd_5851037 : Nat := 3004394308240929524529077

theorem tailTrace_5851037 : CollatzResearch.WordTrace tailWord_5851037 prefixEnd_5851037 3004394308240929524529077 := by
  unfold tailWord_5851037
  simp only [CollatzResearch.WordTrace]
  refine ⟨213404851303699701408159365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142269900869133134272106243 213404851303699701408159365)
  ·
    refine ⟨40013409619443694014029881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213404851303699701408159365 40013409619443694014029881)
    ·
      refine ⟨30010057214582770510522411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40013409619443694014029881 30010057214582770510522411)
      ·
        refine ⟨45015085821874155765783617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30010057214582770510522411 45015085821874155765783617)
        ·
          refine ⟨33761314366405616824337713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45015085821874155765783617 33761314366405616824337713)
          ·
            refine ⟨25320985774804212618253285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33761314366405616824337713 25320985774804212618253285)
            ·
              refine ⟨4747684832775789865922491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25320985774804212618253285 4747684832775789865922491)
              ·
                refine ⟨7121527249163684798883737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747684832775789865922491 7121527249163684798883737)
                ·
                  refine ⟨5341145436872763599162803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7121527249163684798883737 5341145436872763599162803)
                  ·
                    refine ⟨8011718155309145398744205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5341145436872763599162803 8011718155309145398744205)
                    ·
                      refine ⟨3004394308240929524529077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011718155309145398744205 3004394308240929524529077)
                      ·
                        rfl

theorem cell23_5851037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_5851037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851037 prefixEnd_5851037 := by exact prefixLift 5851037
  have htrace : WordTrace (prefixWord ++ tailWord_5851037) baseStart_5851037 baseEnd_5851037 := by
    simpa [prefixWord, tailWord_5851037, baseEnd_5851037] using wordTrace_append hprefix tailTrace_5851037
  have hstable : (prefixWord ++ tailWord_5851037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851037).length < 2 ^ (prefixWord ++ tailWord_5851037).sum := by decide
  have hdescent : baseEnd_5851037 < baseStart_5851037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851043 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 1, 4, 2]
def baseStart_5851043 : Nat := 118140960795 + 5851043 * 2 ^ 59
def prefixEnd_5851043 : Nat := 4983230072969 + 3 ^ 40 * 5851043 * 2
def baseEnd_5851043 : Nat := 3004397389124856501054049

theorem tailTrace_5851043 : CollatzResearch.WordTrace tailWord_5851043 prefixEnd_5851043 3004397389124856501054049 := by
  unfold tailWord_5851043
  simp only [CollatzResearch.WordTrace]
  refine ⟨213405070141677964432877783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142270046761118642955251855 213405070141677964432877783)
  ·
    refine ⟨320107605212516946649316675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213405070141677964432877783 320107605212516946649316675)
    ·
      refine ⟨480161407818775419973975013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320107605212516946649316675 480161407818775419973975013)
      ·
        refine ⟨90030263966020391245120315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 480161407818775419973975013 90030263966020391245120315)
        ·
          refine ⟨135045395949030586867680473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90030263966020391245120315 135045395949030586867680473)
          ·
            refine ⟨101284046961772940150760355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135045395949030586867680473 101284046961772940150760355)
            ·
              refine ⟨151926070442659410226140533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101284046961772940150760355 151926070442659410226140533)
              ·
                refine ⟨14243069103999319708700675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151926070442659410226140533 14243069103999319708700675)
                ·
                  refine ⟨21364603655998979563051013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14243069103999319708700675 21364603655998979563051013)
                  ·
                    refine ⟨4005863185499808668072065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21364603655998979563051013 4005863185499808668072065)
                    ·
                      refine ⟨3004397389124856501054049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005863185499808668072065 3004397389124856501054049)
                      ·
                        rfl

theorem cell23_5851043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_5851043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851043 prefixEnd_5851043 := by exact prefixLift 5851043
  have htrace : WordTrace (prefixWord ++ tailWord_5851043) baseStart_5851043 baseEnd_5851043 := by
    simpa [prefixWord, tailWord_5851043, baseEnd_5851043] using wordTrace_append hprefix tailTrace_5851043
  have hstable : (prefixWord ++ tailWord_5851043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851043).length < 2 ^ (prefixWord ++ tailWord_5851043).sum := by decide
  have hdescent : baseEnd_5851043 < baseStart_5851043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851047 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_5851047 : Nat := 118140960795 + 5851047 * 2 ^ 59
def prefixEnd_5851047 : Nat := 4983230072969 + 3 ^ 40 * 5851047 * 2
def baseEnd_5851047 : Nat := 3004399443047474485404031

theorem tailTrace_5851047 : CollatzResearch.WordTrace tailWord_5851047 prefixEnd_5851047 3004399443047474485404031 := by
  unfold tailWord_5851047
  simp only [CollatzResearch.WordTrace]
  refine ⟨213405216033663473116023395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142270144022442315410682263 213405216033663473116023395)
  ·
    refine ⟨320107824050495209674035093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213405216033663473116023395 320107824050495209674035093)
    ·
      refine ⟨15005054252366962953470395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 320107824050495209674035093 15005054252366962953470395)
      ·
        refine ⟨22507581378550444430205593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15005054252366962953470395 22507581378550444430205593)
        ·
          refine ⟨16880686033912833322654195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22507581378550444430205593 16880686033912833322654195)
          ·
            refine ⟨25321029050869249983981293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16880686033912833322654195 25321029050869249983981293)
            ·
              refine ⟨9495385894075968743992985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25321029050869249983981293 9495385894075968743992985)
              ·
                refine ⟨7121539420556976557994739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9495385894075968743992985 7121539420556976557994739)
                ·
                  refine ⟨10682309130835464836992109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7121539420556976557994739 10682309130835464836992109)
                  ·
                    refine ⟨4005865924063299313872041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10682309130835464836992109 4005865924063299313872041)
                    ·
                      refine ⟨3004399443047474485404031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005865924063299313872041 3004399443047474485404031)
                      ·
                        rfl

theorem cell23_5851047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_5851047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851047 prefixEnd_5851047 := by exact prefixLift 5851047
  have htrace : WordTrace (prefixWord ++ tailWord_5851047) baseStart_5851047 baseEnd_5851047 := by
    simpa [prefixWord, tailWord_5851047, baseEnd_5851047] using wordTrace_append hprefix tailTrace_5851047
  have hstable : (prefixWord ++ tailWord_5851047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851047).length < 2 ^ (prefixWord ++ tailWord_5851047).sum := by decide
  have hdescent : baseEnd_5851047 < baseStart_5851047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851054 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5851054 : Nat := 118140960795 + 5851054 * 2 ^ 59
def prefixEnd_5851054 : Nat := 4983230072969 + 3 ^ 40 * 5851054 * 2
def baseEnd_5851054 : Nat := 3004403037412055958016499

theorem tailTrace_5851054 : CollatzResearch.WordTrace tailWord_5851054 prefixEnd_5851054 3004403037412055958016499 := by
  unfold tailWord_5851054
  simp only [CollatzResearch.WordTrace]
  refine ⟨26675683918079764163941027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142270314229758742207685477 26675683918079764163941027)
  ·
    refine ⟨40013525877119646245911541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26675683918079764163941027 40013525877119646245911541)
    ·
      refine ⟨3751268050979966835554207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40013525877119646245911541 3751268050979966835554207)
      ·
        refine ⟨5626902076469950253331311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751268050979966835554207 5626902076469950253331311)
        ·
          refine ⟨8440353114704925379996967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626902076469950253331311 8440353114704925379996967)
          ·
            refine ⟨12660529672057388069995451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440353114704925379996967 12660529672057388069995451)
            ·
              refine ⟨18990794508086082104993177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12660529672057388069995451 18990794508086082104993177)
              ·
                refine ⟨14243095881064561578744883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18990794508086082104993177 14243095881064561578744883)
                ·
                  refine ⟨21364643821596842368117325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14243095881064561578744883 21364643821596842368117325)
                  ·
                    refine ⟨8011741433098815888043997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21364643821596842368117325 8011741433098815888043997)
                    ·
                      refine ⟨3004403037412055958016499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011741433098815888043997 3004403037412055958016499)
                      ·
                        rfl

theorem cell23_5851054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5851054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851054 prefixEnd_5851054 := by exact prefixLift 5851054
  have htrace : WordTrace (prefixWord ++ tailWord_5851054) baseStart_5851054 baseEnd_5851054 := by
    simpa [prefixWord, tailWord_5851054, baseEnd_5851054] using wordTrace_append hprefix tailTrace_5851054
  have hstable : (prefixWord ++ tailWord_5851054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851054).length < 2 ^ (prefixWord ++ tailWord_5851054).sum := by decide
  have hdescent : baseEnd_5851054 < baseStart_5851054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851083 : List Nat := [1, 1, 1, 1, 3, 4, 3, 4, 5]
def baseStart_5851083 : Nat := 118140960795 + 5851083 * 2 ^ 59
def prefixEnd_5851083 : Nat := 4983230072969 + 3 ^ 40 * 5851083 * 2
def baseEnd_5851083 : Nat := 333824214261226260505985

theorem tailTrace_5851083 : CollatzResearch.WordTrace tailWord_5851083 prefixEnd_5851083 333824214261226260505985 := by
  unfold tailWord_5851083
  simp only [CollatzResearch.WordTrace]
  refine ⟨213406529061533051264333903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142271019374355367509555935 213406529061533051264333903)
  ·
    refine ⟨320109793592299576896500855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213406529061533051264333903 320109793592299576896500855)
    ·
      refine ⟨480164690388449365344751283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320109793592299576896500855 480164690388449365344751283)
      ·
        refine ⟨720247035582674048017126925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480164690388449365344751283 720247035582674048017126925)
        ·
          refine ⟨270092638343502768006422597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 720247035582674048017126925 270092638343502768006422597)
          ·
            refine ⟨50642369689406769001204237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270092638343502768006422597 50642369689406769001204237)
            ·
              refine ⟨18990888633527538375451589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50642369689406769001204237 18990888633527538375451589)
              ·
                refine ⟨3560791618786413445397173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18990888633527538375451589 3560791618786413445397173)
                ·
                  refine ⟨333824214261226260505985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3560791618786413445397173 333824214261226260505985)
                  ·
                    rfl

theorem cell23_5851083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 5].length) (baseStart_5851083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851083 prefixEnd_5851083 := by exact prefixLift 5851083
  have htrace : WordTrace (prefixWord ++ tailWord_5851083) baseStart_5851083 baseEnd_5851083 := by
    simpa [prefixWord, tailWord_5851083, baseEnd_5851083] using wordTrace_append hprefix tailTrace_5851083
  have hstable : (prefixWord ++ tailWord_5851083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851083).length < 2 ^ (prefixWord ++ tailWord_5851083).sum := by decide
  have hdescent : baseEnd_5851083 < baseStart_5851083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851090 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5851090 : Nat := 118140960795 + 5851090 * 2 ^ 59
def prefixEnd_5851090 : Nat := 4983230072969 + 3 ^ 40 * 5851090 * 2
def baseEnd_5851090 : Nat := 3004421522715617817166333

theorem tailTrace_5851090 : CollatzResearch.WordTrace tailWord_5851090 prefixEnd_5851090 3004421522715617817166333 := by
  unfold tailWord_5851090
  simp only [CollatzResearch.WordTrace]
  refine ⟨53351696093126922864959681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142271189581671794306559149 53351696093126922864959681)
  ·
    refine ⟨40013772069845192148719761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53351696093126922864959681 40013772069845192148719761)
    ·
      refine ⟨30010329052383894111539821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40013772069845192148719761 30010329052383894111539821)
      ·
        refine ⟨11253873394643960291827433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30010329052383894111539821 11253873394643960291827433)
        ·
          refine ⟨8440405045982970218870575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11253873394643960291827433 8440405045982970218870575)
          ·
            refine ⟨12660607568974455328305863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440405045982970218870575 12660607568974455328305863)
            ·
              refine ⟨18990911353461682992458795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12660607568974455328305863 18990911353461682992458795)
              ·
                refine ⟨28486367030192524488688193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18990911353461682992458795 28486367030192524488688193)
                ·
                  refine ⟨21364775272644393366516145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28486367030192524488688193 21364775272644393366516145)
                  ·
                    refine ⟨16023581454483295024887109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21364775272644393366516145 16023581454483295024887109)
                    ·
                      refine ⟨3004421522715617817166333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16023581454483295024887109 3004421522715617817166333)
                      ·
                        rfl

theorem cell23_5851090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5851090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851090 prefixEnd_5851090 := by exact prefixLift 5851090
  have htrace : WordTrace (prefixWord ++ tailWord_5851090) baseStart_5851090 baseEnd_5851090 := by
    simpa [prefixWord, tailWord_5851090, baseEnd_5851090] using wordTrace_append hprefix tailTrace_5851090
  have hstable : (prefixWord ++ tailWord_5851090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851090).length < 2 ^ (prefixWord ++ tailWord_5851090).sum := by decide
  have hdescent : baseEnd_5851090 < baseStart_5851090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851093 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5851093 : Nat := 118140960795 + 5851093 * 2 ^ 59
def prefixEnd_5851093 : Nat := 4983230072969 + 3 ^ 40 * 5851093 * 2
def baseEnd_5851093 : Nat := 3004423063157581305428819

theorem tailTrace_5851093 : CollatzResearch.WordTrace tailWord_5851093 prefixEnd_5851093 3004423063157581305428819 := by
  unfold tailWord_5851093
  simp only [CollatzResearch.WordTrace]
  refine ⟨213406893791496822972197933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142271262527664548648131955 213406893791496822972197933)
  ·
    refine ⟨80027585171811308614574225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213406893791496822972197933 80027585171811308614574225)
    ·
      refine ⟨60020688878858481460930669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80027585171811308614574225 60020688878858481460930669)
      ·
        refine ⟨22507758329571930547849001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60020688878858481460930669 22507758329571930547849001)
        ·
          refine ⟨16880818747178947910886751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22507758329571930547849001 16880818747178947910886751)
          ·
            refine ⟨25321228120768421866330127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16880818747178947910886751 25321228120768421866330127)
            ·
              refine ⟨37981842181152632799495191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25321228120768421866330127 37981842181152632799495191)
              ·
                refine ⟨56972763271728949199242787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37981842181152632799495191 56972763271728949199242787)
                ·
                  refine ⟨85459144907593423798864181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56972763271728949199242787 85459144907593423798864181)
                  ·
                    refine ⟨8011794835086883481143517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85459144907593423798864181 8011794835086883481143517)
                    ·
                      refine ⟨3004423063157581305428819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011794835086883481143517 3004423063157581305428819)
                      ·
                        rfl

theorem cell23_5851093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5851093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851093 prefixEnd_5851093 := by exact prefixLift 5851093
  have htrace : WordTrace (prefixWord ++ tailWord_5851093) baseStart_5851093 baseEnd_5851093 := by
    simpa [prefixWord, tailWord_5851093, baseEnd_5851093] using wordTrace_append hprefix tailTrace_5851093
  have hstable : (prefixWord ++ tailWord_5851093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851093).length < 2 ^ (prefixWord ++ tailWord_5851093).sum := by decide
  have hdescent : baseEnd_5851093 < baseStart_5851093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851094 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_5851094 : Nat := 118140960795 + 5851094 * 2 ^ 59
def prefixEnd_5851094 : Nat := 4983230072969 + 3 ^ 40 * 5851094 * 2
def baseEnd_5851094 : Nat := 3004423576638235801516315

theorem tailTrace_5851094 : CollatzResearch.WordTrace tailWord_5851094 prefixEnd_5851094 3004423576638235801516315 := by
  unfold tailWord_5851094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337933141530825008936521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142271286842995466761989557 13337933141530825008936521)
  ·
    refine ⟨10003449856148118756702391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13337933141530825008936521 10003449856148118756702391)
    ·
      refine ⟨15005174784222178135053587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10003449856148118756702391 15005174784222178135053587)
      ·
        refine ⟨22507762176333267202580381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15005174784222178135053587 22507762176333267202580381)
        ·
          refine ⟨8440410816124975200967643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22507762176333267202580381 8440410816124975200967643)
          ·
            refine ⟨12660616224187462801451465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440410816124975200967643 12660616224187462801451465)
            ·
              refine ⟨9495462168140597101088599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12660616224187462801451465 9495462168140597101088599)
              ·
                refine ⟨14243193252210895651632899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495462168140597101088599 14243193252210895651632899)
                ·
                  refine ⟨21364789878316343477449349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14243193252210895651632899 21364789878316343477449349)
                  ·
                    refine ⟨4005898102184314402021753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21364789878316343477449349 4005898102184314402021753)
                    ·
                      refine ⟨3004423576638235801516315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005898102184314402021753 3004423576638235801516315)
                      ·
                        rfl

theorem cell23_5851094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_5851094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851094 prefixEnd_5851094 := by exact prefixLift 5851094
  have htrace : WordTrace (prefixWord ++ tailWord_5851094) baseStart_5851094 baseEnd_5851094 := by
    simpa [prefixWord, tailWord_5851094, baseEnd_5851094] using wordTrace_append hprefix tailTrace_5851094
  have hstable : (prefixWord ++ tailWord_5851094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851094).length < 2 ^ (prefixWord ++ tailWord_5851094).sum := by decide
  have hdescent : baseEnd_5851094 < baseStart_5851094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851096 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 1, 7]
def baseStart_5851096 : Nat := 118140960795 + 5851096 * 2 ^ 59
def prefixEnd_5851096 : Nat := 4983230072969 + 3 ^ 40 * 5851096 * 2
def baseEnd_5851096 : Nat := 1001474867866514931230435

theorem tailTrace_5851096 : CollatzResearch.WordTrace tailWord_5851096 prefixEnd_5851096 1001474867866514931230435 := by
  unfold tailWord_5851096
  simp only [CollatzResearch.WordTrace]
  refine ⟨106703501605242977242278571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142271335473657302989704761 106703501605242977242278571)
  ·
    refine ⟨160055252407864465863417857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106703501605242977242278571 160055252407864465863417857)
    ·
      refine ⟨120041439305898349397563393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160055252407864465863417857 120041439305898349397563393)
      ·
        refine ⟨90031079479423762048172545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120041439305898349397563393 90031079479423762048172545)
        ·
          refine ⟨67523309609567821536129409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90031079479423762048172545 67523309609567821536129409)
          ·
            refine ⟨50642482207175866152097057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67523309609567821536129409 50642482207175866152097057)
            ·
              refine ⟨37981861655381899614072793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50642482207175866152097057 37981861655381899614072793)
              ·
                refine ⟨28486396241536424710554595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37981861655381899614072793 28486396241536424710554595)
                ·
                  refine ⟨42729594362304637065831893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28486396241536424710554595 42729594362304637065831893)
                  ·
                    refine ⟨1001474867866514931230435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42729594362304637065831893 1001474867866514931230435)
                    ·
                      rfl

theorem cell23_5851096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_5851096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851096 prefixEnd_5851096 := by exact prefixLift 5851096
  have htrace : WordTrace (prefixWord ++ tailWord_5851096) baseStart_5851096 baseEnd_5851096 := by
    simpa [prefixWord, tailWord_5851096, baseEnd_5851096] using wordTrace_append hprefix tailTrace_5851096
  have hstable : (prefixWord ++ tailWord_5851096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851096).length < 2 ^ (prefixWord ++ tailWord_5851096).sum := by decide
  have hdescent : baseEnd_5851096 < baseStart_5851096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851133 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_5851133 : Nat := 118140960795 + 5851133 * 2 ^ 59
def prefixEnd_5851133 : Nat := 4983230072969 + 3 ^ 40 * 5851133 * 2
def baseEnd_5851133 : Nat := 3004443602383761148928635

theorem tailTrace_5851133 : CollatzResearch.WordTrace tailWord_5851133 prefixEnd_5851133 3004443602383761148928635 := by
  unfold tailWord_5851133
  simp only [CollatzResearch.WordTrace]
  refine ⟨213408352711351909803654053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142272235140901273202436035 213408352711351909803654053)
  ·
    refine ⟨40014066133378483088185135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213408352711351909803654053 40014066133378483088185135)
    ·
      refine ⟨60021099200067724632277703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40014066133378483088185135 60021099200067724632277703)
      ·
        refine ⟨90031648800101586948416555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60021099200067724632277703 90031648800101586948416555)
        ·
          refine ⟨135047473200152380422624833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90031648800101586948416555 135047473200152380422624833)
          ·
            refine ⟨101285604900114285316968625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135047473200152380422624833 101285604900114285316968625)
            ·
              refine ⟨75964203675085713987726469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101285604900114285316968625 75964203675085713987726469)
              ·
                refine ⟨14243288189078571372698713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75964203675085713987726469 14243288189078571372698713)
                ·
                  refine ⟨10682466141808928529524035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14243288189078571372698713 10682466141808928529524035)
                  ·
                    refine ⟨16023699212713392794286053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10682466141808928529524035 16023699212713392794286053)
                    ·
                      refine ⟨3004443602383761148928635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16023699212713392794286053 3004443602383761148928635)
                      ·
                        rfl

theorem cell23_5851133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_5851133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851133 prefixEnd_5851133 := by exact prefixLift 5851133
  have htrace : WordTrace (prefixWord ++ tailWord_5851133) baseStart_5851133 baseEnd_5851133 := by
    simpa [prefixWord, tailWord_5851133, baseEnd_5851133] using wordTrace_append hprefix tailTrace_5851133
  have hstable : (prefixWord ++ tailWord_5851133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851133).length < 2 ^ (prefixWord ++ tailWord_5851133).sum := by decide
  have hdescent : baseEnd_5851133 < baseStart_5851133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851150 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_5851150 : Nat := 118140960795 + 5851150 * 2 ^ 59
def prefixEnd_5851150 : Nat := 4983230072969 + 3 ^ 40 * 5851150 * 2
def baseEnd_5851150 : Nat := 3004452331554887582416057

theorem tailTrace_5851150 : CollatzResearch.WordTrace tailWord_5851150 prefixEnd_5851150 3004452331554887582416057 := by
  unfold tailWord_5851150
  simp only [CollatzResearch.WordTrace]
  refine ⟨26676121594036290213377863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142272648501526881138015269 26676121594036290213377863)
  ·
    refine ⟨40014182391054435320066795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26676121594036290213377863 40014182391054435320066795)
    ·
      refine ⟨60021273586581652980100193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40014182391054435320066795 60021273586581652980100193)
      ·
        refine ⟨45015955189936239735075145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60021273586581652980100193 45015955189936239735075145)
        ·
          refine ⟨33761966392452179801306359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45015955189936239735075145 33761966392452179801306359)
          ·
            refine ⟨50642949588678269701959539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33761966392452179801306359 50642949588678269701959539)
            ·
              refine ⟨75964424383017404552939309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50642949588678269701959539 75964424383017404552939309)
              ·
                refine ⟨28486659143631526707352241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75964424383017404552939309 28486659143631526707352241)
                ·
                  refine ⟨21364994357723645030514181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28486659143631526707352241 21364994357723645030514181)
                  ·
                    refine ⟨4005936442073183443221409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21364994357723645030514181 4005936442073183443221409)
                    ·
                      refine ⟨3004452331554887582416057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005936442073183443221409 3004452331554887582416057)
                      ·
                        rfl

theorem cell23_5851150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_5851150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851150 prefixEnd_5851150 := by exact prefixLift 5851150
  have htrace : WordTrace (prefixWord ++ tailWord_5851150) baseStart_5851150 baseEnd_5851150 := by
    simpa [prefixWord, tailWord_5851150, baseEnd_5851150] using wordTrace_append hprefix tailTrace_5851150
  have hstable : (prefixWord ++ tailWord_5851150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851150).length < 2 ^ (prefixWord ++ tailWord_5851150).sum := by decide
  have hdescent : baseEnd_5851150 < baseStart_5851150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851170 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_5851170 : Nat := 118140960795 + 5851170 * 2 ^ 59
def prefixEnd_5851170 : Nat := 4983230072969 + 3 ^ 40 * 5851170 * 2
def baseEnd_5851170 : Nat := 3004462601167977504165965

theorem tailTrace_5851170 : CollatzResearch.WordTrace tailWord_5851170 prefixEnd_5851170 3004462601167977504165965 := by
  unfold tailWord_5851170
  simp only [CollatzResearch.WordTrace]
  refine ⟨53352425553054466280687741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142273134808145243415167309 53352425553054466280687741)
  ·
    refine ⟨20007159582395424855257903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53352425553054466280687741 20007159582395424855257903)
    ·
      refine ⟨30010739373593137282886855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20007159582395424855257903 30010739373593137282886855)
      ·
        refine ⟨45016109060389705924330283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30010739373593137282886855 45016109060389705924330283)
        ·
          refine ⟨67524163590584558886495425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45016109060389705924330283 67524163590584558886495425)
          ·
            refine ⟨50643122692938419164871569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67524163590584558886495425 50643122692938419164871569)
            ·
              refine ⟨37982342019703814373653677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50643122692938419164871569 37982342019703814373653677)
              ·
                refine ⟨14243378257388930390120129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37982342019703814373653677 14243378257388930390120129)
                ·
                  refine ⟨10682533693041697792590097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14243378257388930390120129 10682533693041697792590097)
                  ·
                    refine ⟨8011900269781273344442573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10682533693041697792590097 8011900269781273344442573)
                    ·
                      refine ⟨3004462601167977504165965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8011900269781273344442573 3004462601167977504165965)
                      ·
                        rfl

theorem cell23_5851170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_5851170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851170 prefixEnd_5851170 := by exact prefixLift 5851170
  have htrace : WordTrace (prefixWord ++ tailWord_5851170) baseStart_5851170 baseEnd_5851170 := by
    simpa [prefixWord, tailWord_5851170, baseEnd_5851170] using wordTrace_append hprefix tailTrace_5851170
  have hstable : (prefixWord ++ tailWord_5851170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851170).length < 2 ^ (prefixWord ++ tailWord_5851170).sum := by decide
  have hdescent : baseEnd_5851170 < baseStart_5851170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851190 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_5851190 : Nat := 118140960795 + 5851190 * 2 ^ 59
def prefixEnd_5851190 : Nat := 4983230072969 + 3 ^ 40 * 5851190 * 2
def baseEnd_5851190 : Nat := 333830318975674158435097

theorem tailTrace_5851190 : CollatzResearch.WordTrace tailWord_5851190 prefixEnd_5851190 333830318975674158435097 := by
  unfold tailWord_5851190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13338151979509088033654939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142273621114763605692319349 13338151979509088033654939)
  ·
    refine ⟨20007227969263632050482409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13338151979509088033654939 20007227969263632050482409)
    ·
      refine ⟨15005420976947724037861807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20007227969263632050482409 15005420976947724037861807)
      ·
        refine ⟨22508131465421586056792711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15005420976947724037861807 22508131465421586056792711)
        ·
          refine ⟨33762197198132379085189067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22508131465421586056792711 33762197198132379085189067)
          ·
            refine ⟨50643295797198568627783601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33762197198132379085189067 50643295797198568627783601)
            ·
              refine ⟨37982471847898926470837701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50643295797198568627783601 37982471847898926470837701)
              ·
                refine ⟨7121713471481048713282069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37982471847898926470837701 7121713471481048713282069)
                ·
                  refine ⟨333830318975674158435097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7121713471481048713282069 333830318975674158435097)
                  ·
                    rfl

theorem cell23_5851190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_5851190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851190 prefixEnd_5851190 := by exact prefixLift 5851190
  have htrace : WordTrace (prefixWord ++ tailWord_5851190) baseStart_5851190 baseEnd_5851190 := by
    simpa [prefixWord, tailWord_5851190, baseEnd_5851190] using wordTrace_append hprefix tailTrace_5851190
  have hstable : (prefixWord ++ tailWord_5851190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851190).length < 2 ^ (prefixWord ++ tailWord_5851190).sum := by decide
  have hdescent : baseEnd_5851190 < baseStart_5851190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851210 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_5851210 : Nat := 118140960795 + 5851210 * 2 ^ 59
def prefixEnd_5851210 : Nat := 4983230072969 + 3 ^ 40 * 5851210 * 2
def baseEnd_5851210 : Nat := 3004483140394157347665781

theorem tailTrace_5851210 : CollatzResearch.WordTrace tailWord_5851210 prefixEnd_5851210 3004483140394157347665781 := by
  unfold tailWord_5851210
  simp only [CollatzResearch.WordTrace]
  refine ⟨53352790283018237988551771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142274107421381967969471389 53352790283018237988551771)
  ·
    refine ⟨80029185424527356982827657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53352790283018237988551771 80029185424527356982827657)
    ·
      refine ⟨60021889068395517737120743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80029185424527356982827657 60021889068395517737120743)
      ·
        refine ⟨90032833602593276605681115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60021889068395517737120743 90032833602593276605681115)
        ·
          refine ⟨135049250403889914908521673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90032833602593276605681115 135049250403889914908521673)
          ·
            refine ⟨101286937802917436181391255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135049250403889914908521673 101286937802917436181391255)
            ·
              refine ⟨151930406704376154272086883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101286937802917436181391255 151930406704376154272086883)
              ·
                refine ⟨227895610056564231408130325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151930406704376154272086883 227895610056564231408130325)
                ·
                  refine ⟨10682606721401448347256109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 227895610056564231408130325 10682606721401448347256109)
                  ·
                    refine ⟨4005977520525543130221041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10682606721401448347256109 4005977520525543130221041)
                    ·
                      refine ⟨3004483140394157347665781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4005977520525543130221041 3004483140394157347665781)
                      ·
                        rfl

theorem cell23_5851210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_5851210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851210 prefixEnd_5851210 := by exact prefixLift 5851210
  have htrace : WordTrace (prefixWord ++ tailWord_5851210) baseStart_5851210 baseEnd_5851210 := by
    simpa [prefixWord, tailWord_5851210, baseEnd_5851210] using wordTrace_append hprefix tailTrace_5851210
  have hstable : (prefixWord ++ tailWord_5851210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851210).length < 2 ^ (prefixWord ++ tailWord_5851210).sum := by decide
  have hdescent : baseEnd_5851210 < baseStart_5851210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851237 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_5851237 : Nat := 118140960795 + 5851237 * 2 ^ 59
def prefixEnd_5851237 : Nat := 4983230072969 + 3 ^ 40 * 5851237 * 2
def baseEnd_5851237 : Nat := 1001499001457276247342719

theorem tailTrace_5851237 : CollatzResearch.WordTrace tailWord_5851237 prefixEnd_5851237 1001499001457276247342719 := by
  unfold tailWord_5851237
  simp only [CollatzResearch.WordTrace]
  refine ⟨213412145902975135565439965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142274763935316757043626643 213412145902975135565439965)
  ·
    refine ⟨80029554713615675837039987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213412145902975135565439965 80029554713615675837039987)
    ·
      refine ⟨120044332070423513755559981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80029554713615675837039987 120044332070423513755559981)
      ·
        refine ⟨45016624526408817658334993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120044332070423513755559981 45016624526408817658334993)
        ·
          refine ⟨33762468394806613243751245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45016624526408817658334993 33762468394806613243751245)
          ·
            refine ⟨12660925648052479966406717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33762468394806613243751245 12660925648052479966406717)
            ·
              refine ⟨4747847118019679987402519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12660925648052479966406717 4747847118019679987402519)
              ·
                refine ⟨7121770677029519981103779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747847118019679987402519 7121770677029519981103779)
                ·
                  refine ⟨10682656015544279971655669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7121770677029519981103779 10682656015544279971655669)
                  ·
                    refine ⟨1001499001457276247342719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10682656015544279971655669 1001499001457276247342719)
                    ·
                      rfl

theorem cell23_5851237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_5851237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851237 prefixEnd_5851237 := by exact prefixLift 5851237
  have htrace : WordTrace (prefixWord ++ tailWord_5851237) baseStart_5851237 baseEnd_5851237 := by
    simpa [prefixWord, tailWord_5851237, baseEnd_5851237] using wordTrace_append hprefix tailTrace_5851237
  have hstable : (prefixWord ++ tailWord_5851237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851237).length < 2 ^ (prefixWord ++ tailWord_5851237).sum := by decide
  have hdescent : baseEnd_5851237 < baseStart_5851237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851260 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_5851260 : Nat := 118140960795 + 5851260 * 2 ^ 59
def prefixEnd_5851260 : Nat := 4983230072969 + 3 ^ 40 * 5851260 * 2
def baseEnd_5851260 : Nat := 3004508814426882152040551

theorem tailTrace_5851260 : CollatzResearch.WordTrace tailWord_5851260 prefixEnd_5851260 3004508814426882152040551 := by
  unfold tailWord_5851260
  simp only [CollatzResearch.WordTrace]
  refine ⟨106706492390945905246763617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142275323187927873662351489 106706492390945905246763617)
  ·
    refine ⟨80029869293209428935072713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106706492390945905246763617 80029869293209428935072713)
    ·
      refine ⟨60022401969907071701304535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80029869293209428935072713 60022401969907071701304535)
      ·
        refine ⟨90033602954860607551956803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60022401969907071701304535 90033602954860607551956803)
        ·
          refine ⟨135050404432290911327935205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90033602954860607551956803 135050404432290911327935205)
          ·
            refine ⟨25321950831054545873987851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135050404432290911327935205 25321950831054545873987851)
            ·
              refine ⟨37982926246581818810981777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25321950831054545873987851 37982926246581818810981777)
              ·
                refine ⟨28487194684936364108236333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37982926246581818810981777 28487194684936364108236333)
                ·
                  refine ⟨10682698006851136540588625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28487194684936364108236333 10682698006851136540588625)
                  ·
                    refine ⟨8012023505138352405441469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10682698006851136540588625 8012023505138352405441469)
                    ·
                      refine ⟨3004508814426882152040551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8012023505138352405441469 3004508814426882152040551)
                      ·
                        rfl

theorem cell23_5851260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_5851260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851260 prefixEnd_5851260 := by exact prefixLift 5851260
  have htrace : WordTrace (prefixWord ++ tailWord_5851260) baseStart_5851260 baseEnd_5851260 := by
    simpa [prefixWord, tailWord_5851260, baseEnd_5851260] using wordTrace_append hprefix tailTrace_5851260
  have hstable : (prefixWord ++ tailWord_5851260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851260).length < 2 ^ (prefixWord ++ tailWord_5851260).sum := by decide
  have hdescent : baseEnd_5851260 < baseStart_5851260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851274 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_5851274 : Nat := 118140960795 + 5851274 * 2 ^ 59
def prefixEnd_5851274 : Nat := 4983230072969 + 3 ^ 40 * 5851274 * 2
def baseEnd_5851274 : Nat := 3004516003156045097265487

theorem tailTrace_5851274 : CollatzResearch.WordTrace tailWord_5851274 prefixEnd_5851274 3004516003156045097265487 := by
  unfold tailWord_5851274
  simp only [CollatzResearch.WordTrace]
  refine ⟨53353373850960272721134219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142275663602560727256357917 53353373850960272721134219)
  ·
    refine ⟨80030060776440409081701329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53353373850960272721134219 80030060776440409081701329)
    ·
      refine ⟨60022545582330306811275997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80030060776440409081701329 60022545582330306811275997)
      ·
        refine ⟨22508454593373865054228499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60022545582330306811275997 22508454593373865054228499)
        ·
          refine ⟨33762681890060797581342749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22508454593373865054228499 33762681890060797581342749)
          ·
            refine ⟨12661005708772799093003531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33762681890060797581342749 12661005708772799093003531)
            ·
              refine ⟨18991508563159198639505297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12661005708772799093003531 18991508563159198639505297)
              ·
                refine ⟨14243631422369398979628973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18991508563159198639505297 14243631422369398979628973)
                ·
                  refine ⟨5341361783388524617360865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14243631422369398979628973 5341361783388524617360865)
                  ·
                    refine ⟨4006021337541393463020649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341361783388524617360865 4006021337541393463020649)
                    ·
                      refine ⟨3004516003156045097265487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006021337541393463020649 3004516003156045097265487)
                      ·
                        rfl

theorem cell23_5851274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_5851274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851274 prefixEnd_5851274 := by exact prefixLift 5851274
  have htrace : WordTrace (prefixWord ++ tailWord_5851274) baseStart_5851274 baseEnd_5851274 := by
    simpa [prefixWord, tailWord_5851274, baseEnd_5851274] using wordTrace_append hprefix tailTrace_5851274
  have hstable : (prefixWord ++ tailWord_5851274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851274).length < 2 ^ (prefixWord ++ tailWord_5851274).sum := by decide
  have hdescent : baseEnd_5851274 < baseStart_5851274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851323 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 2, 6]
def baseStart_5851323 : Nat := 118140960795 + 5851323 * 2 ^ 59
def prefixEnd_5851323 : Nat := 4983230072969 + 3 ^ 40 * 5851323 * 2
def baseEnd_5851323 : Nat := 1001513721236038468517587

theorem tailTrace_5851323 : CollatzResearch.WordTrace tailWord_5851323 prefixEnd_5851323 1001513721236038468517587 := by
  unfold tailWord_5851323
  simp only [CollatzResearch.WordTrace]
  refine ⟨213415282580663572253070623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142276855053775714835380415 213415282580663572253070623)
  ·
    refine ⟨320122923870995358379605935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213415282580663572253070623 320122923870995358379605935)
    ·
      refine ⟨480184385806493037569408903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320122923870995358379605935 480184385806493037569408903)
      ·
        refine ⟨720276578709739556354113355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480184385806493037569408903 720276578709739556354113355)
        ·
          refine ⟨1080414868064609334531170033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720276578709739556354113355 1080414868064609334531170033)
          ·
            refine ⟨810311151048457000898377525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080414868064609334531170033 810311151048457000898377525)
            ·
              refine ⟨75966670410792843834222893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 810311151048457000898377525 75966670410792843834222893)
              ·
                refine ⟨28487501404047316437833585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75966670410792843834222893 28487501404047316437833585)
                ·
                  refine ⟨21365626053035487328375189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28487501404047316437833585 21365626053035487328375189)
                  ·
                    refine ⟨1001513721236038468517587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21365626053035487328375189 1001513721236038468517587)
                    ·
                      rfl

theorem cell23_5851323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 6].length) (baseStart_5851323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851323 prefixEnd_5851323 := by exact prefixLift 5851323
  have htrace : WordTrace (prefixWord ++ tailWord_5851323) baseStart_5851323 baseEnd_5851323 := by
    simpa [prefixWord, tailWord_5851323, baseEnd_5851323] using wordTrace_append hprefix tailTrace_5851323
  have hstable : (prefixWord ++ tailWord_5851323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851323).length < 2 ^ (prefixWord ++ tailWord_5851323).sum := by decide
  have hdescent : baseEnd_5851323 < baseStart_5851323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851324 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5851324 : Nat := 118140960795 + 5851324 * 2 ^ 59
def prefixEnd_5851324 : Nat := 4983230072969 + 3 ^ 40 * 5851324 * 2
def baseEnd_5851324 : Nat := 3004541677188769901640257

theorem tailTrace_5851324 : CollatzResearch.WordTrace tailWord_5851324 prefixEnd_5851324 3004541677188769901640257 := by
  unfold tailWord_5851324
  simp only [CollatzResearch.WordTrace]
  refine ⟨106707659526829974711928513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142276879369106632949238017 106707659526829974711928513)
  ·
    refine ⟨80030744645122481033946385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106707659526829974711928513 80030744645122481033946385)
    ·
      refine ⟨60023058483841860775459789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80030744645122481033946385 60023058483841860775459789)
      ·
        refine ⟨22508646931440697790797421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60023058483841860775459789 22508646931440697790797421)
        ·
          refine ⟨8440742599290261671549033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22508646931440697790797421 8440742599290261671549033)
          ·
            refine ⟨6330556949467696253661775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8440742599290261671549033 6330556949467696253661775)
            ·
              refine ⟨9495835424201544380492663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330556949467696253661775 9495835424201544380492663)
              ·
                refine ⟨14243753136302316570738995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495835424201544380492663 14243753136302316570738995)
                ·
                  refine ⟨21365629704453474856108493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14243753136302316570738995 21365629704453474856108493)
                  ·
                    refine ⟨8012111139170053071040685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21365629704453474856108493 8012111139170053071040685)
                    ·
                      refine ⟨3004541677188769901640257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8012111139170053071040685 3004541677188769901640257)
                      ·
                        rfl

theorem cell23_5851324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5851324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851324 prefixEnd_5851324 := by exact prefixLift 5851324
  have htrace : WordTrace (prefixWord ++ tailWord_5851324) baseStart_5851324 baseEnd_5851324 := by
    simpa [prefixWord, tailWord_5851324, baseEnd_5851324] using wordTrace_append hprefix tailTrace_5851324
  have hstable : (prefixWord ++ tailWord_5851324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851324).length < 2 ^ (prefixWord ++ tailWord_5851324).sum := by decide
  have hdescent : baseEnd_5851324 < baseStart_5851324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851353 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 9]
def baseStart_5851353 : Nat := 118140960795 + 5851353 * 2 ^ 59
def prefixEnd_5851353 : Nat := 4983230072969 + 3 ^ 40 * 5851353 * 2
def baseEnd_5851353 : Nat := 333839618680861143130847

theorem tailTrace_5851353 : CollatzResearch.WordTrace tailWord_5851353 prefixEnd_5851353 333839618680861143130847 := by
  unfold tailWord_5851353
  simp only [CollatzResearch.WordTrace]
  refine ⟨213416376770554887376662713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142277584513703258251108475 213416376770554887376662713)
  ·
    refine ⟨160062282577916165532497035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213416376770554887376662713 160062282577916165532497035)
    ·
      refine ⟨240093423866874248298745553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160062282577916165532497035 240093423866874248298745553)
      ·
        refine ⟨180070067900155686224059165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240093423866874248298745553 180070067900155686224059165)
        ·
          refine ⟨67526275462558382334022187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180070067900155686224059165 67526275462558382334022187)
          ·
            refine ⟨101289413193837573501033281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67526275462558382334022187 101289413193837573501033281)
            ·
              refine ⟨75967059895378180125774961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101289413193837573501033281 75967059895378180125774961)
              ·
                refine ⟨56975294921533635094331221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75967059895378180125774961 56975294921533635094331221)
                ·
                  refine ⟨333839618680861143130847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56975294921533635094331221 333839618680861143130847)
                  ·
                    rfl

theorem cell23_5851353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_5851353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851353 prefixEnd_5851353 := by exact prefixLift 5851353
  have htrace : WordTrace (prefixWord ++ tailWord_5851353) baseStart_5851353 baseEnd_5851353 := by
    simpa [prefixWord, tailWord_5851353, baseEnd_5851353] using wordTrace_append hprefix tailTrace_5851353
  have hstable : (prefixWord ++ tailWord_5851353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851353).length < 2 ^ (prefixWord ++ tailWord_5851353).sum := by decide
  have hdescent : baseEnd_5851353 < baseStart_5851353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851364 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_5851364 : Nat := 118140960795 + 5851364 * 2 ^ 59
def prefixEnd_5851364 : Nat := 4983230072969 + 3 ^ 40 * 5851364 * 2
def baseEnd_5851364 : Nat := 3004562216414949745140073

theorem tailTrace_5851364 : CollatzResearch.WordTrace tailWord_5851364 prefixEnd_5851364 3004562216414949745140073 := by
  unfold tailWord_5851364
  simp only [CollatzResearch.WordTrace]
  refine ⟨106708388986757518127656573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142277851982343357503542097 106708388986757518127656573)
  ·
    refine ⟨40015645870034069297871215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106708388986757518127656573 40015645870034069297871215)
    ·
      refine ⟨60023468805051103946806823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40015645870034069297871215 60023468805051103946806823)
      ·
        refine ⟨90035203207576655920210235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60023468805051103946806823 90035203207576655920210235)
        ·
          refine ⟨135052804811364983880315353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90035203207576655920210235 135052804811364983880315353)
          ·
            refine ⟨101289603608523737910236515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135052804811364983880315353 101289603608523737910236515)
            ·
              refine ⟨151934405412785606865354773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101289603608523737910236515 151934405412785606865354773)
              ·
                refine ⟨7121925253724325321813505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151934405412785606865354773 7121925253724325321813505)
                ·
                  refine ⟨5341443940293243991360129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7121925253724325321813505 5341443940293243991360129)
                  ·
                    refine ⟨4006082955219932993520097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341443940293243991360129 4006082955219932993520097)
                    ·
                      refine ⟨3004562216414949745140073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006082955219932993520097 3004562216414949745140073)
                      ·
                        rfl

theorem cell23_5851364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_5851364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851364 prefixEnd_5851364 := by exact prefixLift 5851364
  have htrace : WordTrace (prefixWord ++ tailWord_5851364) baseStart_5851364 baseEnd_5851364 := by
    simpa [prefixWord, tailWord_5851364, baseEnd_5851364] using wordTrace_append hprefix tailTrace_5851364
  have hstable : (prefixWord ++ tailWord_5851364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851364).length < 2 ^ (prefixWord ++ tailWord_5851364).sum := by decide
  have hdescent : baseEnd_5851364 < baseStart_5851364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851420 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_5851420 : Nat := 118140960795 + 5851420 * 2 ^ 59
def prefixEnd_5851420 : Nat := 4983230072969 + 3 ^ 40 * 5851420 * 2
def baseEnd_5851420 : Nat := 3004590971331601526039815

theorem tailTrace_5851420 : CollatzResearch.WordTrace tailWord_5851420 prefixEnd_5851420 3004590971331601526039815 := by
  unfold tailWord_5851420
  simp only [CollatzResearch.WordTrace]
  refine ⟨106709410230656078909675857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142279213640874771879567809 106709410230656078909675857)
  ·
    refine ⟨80032057672992059182256893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106709410230656078909675857 80032057672992059182256893)
    ·
      refine ⟨30012021627372022193346335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80032057672992059182256893 30012021627372022193346335)
      ·
        refine ⟨45018032441058033290019503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30012021627372022193346335 45018032441058033290019503)
        ·
          refine ⟨67527048661587049935029255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45018032441058033290019503 67527048661587049935029255)
          ·
            refine ⟨101290572992380574902543883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67527048661587049935029255 101290572992380574902543883)
            ·
              refine ⟨151935859488570862353815825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101290572992380574902543883 151935859488570862353815825)
              ·
                refine ⟨113951894616428146765361869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151935859488570862353815825 113951894616428146765361869)
                ·
                  refine ⟨42731960481160555037010701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113951894616428146765361869 42731960481160555037010701)
                  ·
                    refine ⟨16024485180435208138879013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42731960481160555037010701 16024485180435208138879013)
                    ·
                      refine ⟨3004590971331601526039815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16024485180435208138879013 3004590971331601526039815)
                      ·
                        rfl

theorem cell23_5851420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_5851420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851420 prefixEnd_5851420 := by exact prefixLift 5851420
  have htrace : WordTrace (prefixWord ++ tailWord_5851420) baseStart_5851420 baseEnd_5851420 := by
    simpa [prefixWord, tailWord_5851420, baseEnd_5851420] using wordTrace_append hprefix tailTrace_5851420
  have hstable : (prefixWord ++ tailWord_5851420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851420).length < 2 ^ (prefixWord ++ tailWord_5851420).sum := by decide
  have hdescent : baseEnd_5851420 < baseStart_5851420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851454 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_5851454 : Nat := 118140960795 + 5851454 * 2 ^ 59
def prefixEnd_5851454 : Nat := 4983230072969 + 3 ^ 40 * 5851454 * 2
def baseEnd_5851454 : Nat := 3004608429673854393014659

theorem tailTrace_5851454 : CollatzResearch.WordTrace tailWord_5851454 prefixEnd_5851454 3004608429673854393014659 := by
  unfold tailWord_5851454
  simp only [CollatzResearch.WordTrace]
  refine ⟨26677507567898622703261177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142280040362125987750726277 26677507567898622703261177)
  ·
    refine ⟨20008130675923967027445883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26677507567898622703261177 20008130675923967027445883)
    ·
      refine ⟨30012196013885950541168825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20008130675923967027445883 30012196013885950541168825)
      ·
        refine ⟨22509147010414462905876619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30012196013885950541168825 22509147010414462905876619)
        ·
          refine ⟨33763720515621694358814929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22509147010414462905876619 33763720515621694358814929)
          ·
            refine ⟨25322790386716270769111197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33763720515621694358814929 25322790386716270769111197)
            ·
              refine ⟨9496046395018601538416699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25322790386716270769111197 9496046395018601538416699)
              ·
                refine ⟨14244069592527902307625049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9496046395018601538416699 14244069592527902307625049)
                ·
                  refine ⟨10683052194395926730718787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14244069592527902307625049 10683052194395926730718787)
                  ·
                    refine ⟨16024578291593890096078181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10683052194395926730718787 16024578291593890096078181)
                    ·
                      refine ⟨3004608429673854393014659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16024578291593890096078181 3004608429673854393014659)
                      ·
                        rfl

theorem cell23_5851454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_5851454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851454 prefixEnd_5851454 := by exact prefixLift 5851454
  have htrace : WordTrace (prefixWord ++ tailWord_5851454) baseStart_5851454 baseEnd_5851454 := by
    simpa [prefixWord, tailWord_5851454, baseEnd_5851454] using wordTrace_append hprefix tailTrace_5851454
  have hstable : (prefixWord ++ tailWord_5851454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851454).length < 2 ^ (prefixWord ++ tailWord_5851454).sum := by decide
  have hdescent : baseEnd_5851454 < baseStart_5851454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851464 : List Nat := [2, 1, 3, 1, 1, 2, 3, 5, 1, 4]
def baseStart_5851464 : Nat := 118140960795 + 5851464 * 2 ^ 59
def prefixEnd_5851464 : Nat := 4983230072969 + 3 ^ 40 * 5851464 * 2
def baseEnd_5851464 : Nat := 1001537854826799784629871

theorem tailTrace_5851464 : CollatzResearch.WordTrace tailWord_5851464 prefixEnd_5851464 1001537854826799784629871 := by
  unfold tailWord_5851464
  simp only [CollatzResearch.WordTrace]
  refine ⟨106710212636576376666976723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142280283515435168889302297 106710212636576376666976723)
  ·
    refine ⟨160065318954864565000465085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106710212636576376666976723 160065318954864565000465085)
    ·
      refine ⟨60024494608074211875174407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160065318954864565000465085 60024494608074211875174407)
      ·
        refine ⟨90036741912111317812761611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60024494608074211875174407 90036741912111317812761611)
        ·
          refine ⟨135055112868166976719142417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90036741912111317812761611 135055112868166976719142417)
          ·
            refine ⟨101291334651125232539356813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135055112868166976719142417 101291334651125232539356813)
            ·
              refine ⟨37984250494171962202258805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101291334651125232539356813 37984250494171962202258805)
              ·
                refine ⟨3561023483828621456461763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37984250494171962202258805 3561023483828621456461763)
                ·
                  refine ⟨5341535225742932184692645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561023483828621456461763 5341535225742932184692645)
                  ·
                    refine ⟨1001537854826799784629871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5341535225742932184692645 1001537854826799784629871)
                    ·
                      rfl

theorem cell23_5851464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_5851464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851464 prefixEnd_5851464 := by exact prefixLift 5851464
  have htrace : WordTrace (prefixWord ++ tailWord_5851464) baseStart_5851464 baseEnd_5851464 := by
    simpa [prefixWord, tailWord_5851464, baseEnd_5851464] using wordTrace_append hprefix tailTrace_5851464
  have hstable : (prefixWord ++ tailWord_5851464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851464).length < 2 ^ (prefixWord ++ tailWord_5851464).sum := by decide
  have hdescent : baseEnd_5851464 < baseStart_5851464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851477 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 8]
def baseStart_5851477 : Nat := 118140960795 + 5851477 * 2 ^ 59
def prefixEnd_5851477 : Nat := 4983230072969 + 3 ^ 40 * 5851477 * 2
def baseEnd_5851477 : Nat := 333846693303211978114117

theorem tailTrace_5851477 : CollatzResearch.WordTrace tailWord_5851477 prefixEnd_5851477 333846693303211978114117 := by
  unfold tailWord_5851477
  simp only [CollatzResearch.WordTrace]
  refine ⟨213420899422105656554176685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142280599614737104369451123 213420899422105656554176685)
  ·
    refine ⟨80032837283289621207816257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213420899422105656554176685 80032837283289621207816257)
    ·
      refine ⟨60024627962467215905862193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80032837283289621207816257 60024627962467215905862193)
      ·
        refine ⟨45018470971850411929396645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60024627962467215905862193 45018470971850411929396645)
        ·
          refine ⟨8440963307221952236761871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45018470971850411929396645 8440963307221952236761871)
          ·
            refine ⟨12661444960832928355142807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440963307221952236761871 12661444960832928355142807)
            ·
              refine ⟨18992167441249392532714211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12661444960832928355142807 18992167441249392532714211)
              ·
                refine ⟨28488251161874088799071317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18992167441249392532714211 28488251161874088799071317)
                ·
                  refine ⟨333846693303211978114117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28488251161874088799071317 333846693303211978114117)
                  ·
                    rfl

theorem cell23_5851477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_5851477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851477 prefixEnd_5851477 := by exact prefixLift 5851477
  have htrace : WordTrace (prefixWord ++ tailWord_5851477) baseStart_5851477 baseEnd_5851477 := by
    simpa [prefixWord, tailWord_5851477, baseEnd_5851477] using wordTrace_append hprefix tailTrace_5851477
  have hstable : (prefixWord ++ tailWord_5851477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851477).length < 2 ^ (prefixWord ++ tailWord_5851477).sum := by decide
  have hdescent : baseEnd_5851477 < baseStart_5851477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851497 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 3, 5, 2]
def baseStart_5851497 : Nat := 118140960795 + 5851497 * 2 ^ 59
def prefixEnd_5851497 : Nat := 4983230072969 + 3 ^ 40 * 5851497 * 2
def baseEnd_5851497 : Nat := 3004630509341997724776961

theorem tailTrace_5851497 : CollatzResearch.WordTrace tailWord_5851497 prefixEnd_5851497 3004630509341997724776961 := by
  unfold tailWord_5851497
  simp only [CollatzResearch.WordTrace]
  refine ⟨213421628882033199969904745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142281085921355466646603163 213421628882033199969904745)
  ·
    refine ⟨160066221661524899977428559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213421628882033199969904745 160066221661524899977428559)
    ·
      refine ⟨240099332492287349966142839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160066221661524899977428559 240099332492287349966142839)
      ·
        refine ⟨360148998738431024949214259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240099332492287349966142839 360148998738431024949214259)
        ·
          refine ⟨540223498107646537423821389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360148998738431024949214259 540223498107646537423821389)
          ·
            refine ⟨202583811790367451533933021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540223498107646537423821389 202583811790367451533933021)
            ·
              refine ⟨75968929421387794325224883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202583811790367451533933021 75968929421387794325224883)
              ·
                refine ⟨113953394132081691487837325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75968929421387794325224883 113953394132081691487837325)
                ·
                  refine ⟨42732522799530634307938997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113953394132081691487837325 42732522799530634307938997)
                  ·
                    refine ⟨4006174012455996966369281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42732522799530634307938997 4006174012455996966369281)
                    ·
                      refine ⟨3004630509341997724776961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006174012455996966369281 3004630509341997724776961)
                      ·
                        rfl

theorem cell23_5851497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 5, 2].length) (baseStart_5851497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851497 prefixEnd_5851497 := by exact prefixLift 5851497
  have htrace : WordTrace (prefixWord ++ tailWord_5851497) baseStart_5851497 baseEnd_5851497 := by
    simpa [prefixWord, tailWord_5851497, baseEnd_5851497] using wordTrace_append hprefix tailTrace_5851497
  have hstable : (prefixWord ++ tailWord_5851497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851497).length < 2 ^ (prefixWord ++ tailWord_5851497).sum := by decide
  have hdescent : baseEnd_5851497 < baseStart_5851497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851504 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 3, 1, 3]
def baseStart_5851504 : Nat := 118140960795 + 5851504 * 2 ^ 59
def prefixEnd_5851504 : Nat := 4983230072969 + 3 ^ 40 * 5851504 * 2
def baseEnd_5851504 : Nat := 3004634103706579197389429

theorem tailTrace_5851504 : CollatzResearch.WordTrace tailWord_5851504 prefixEnd_5851504 3004634103706579197389429 := by
  unfold tailWord_5851504
  simp only [CollatzResearch.WordTrace]
  refine ⟨106710942096503920082704783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142281256128671893443606377 106710942096503920082704783)
  ·
    refine ⟨160066413144755880124057175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106710942096503920082704783 160066413144755880124057175)
    ·
      refine ⟨240099619717133820186085763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160066413144755880124057175 240099619717133820186085763)
      ·
        refine ⟨360149429575700730279128645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240099619717133820186085763 360149429575700730279128645)
        ·
          refine ⟨67528018045443886927336621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360149429575700730279128645 67528018045443886927336621)
          ·
            refine ⟨25323006767041457597751233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67528018045443886927336621 25323006767041457597751233)
            ·
              refine ⟨18992255075281093198313425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25323006767041457597751233 18992255075281093198313425)
              ·
                refine ⟨14244191306460819898735069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18992255075281093198313425 14244191306460819898735069)
                ·
                  refine ⟨5341571739922807462025651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14244191306460819898735069 5341571739922807462025651)
                  ·
                    refine ⟨8012357609884211193038477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5341571739922807462025651 8012357609884211193038477)
                    ·
                      refine ⟨3004634103706579197389429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8012357609884211193038477 3004634103706579197389429)
                      ·
                        rfl

theorem cell23_5851504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 1, 3].length) (baseStart_5851504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851504 prefixEnd_5851504 := by exact prefixLift 5851504
  have htrace : WordTrace (prefixWord ++ tailWord_5851504) baseStart_5851504 baseEnd_5851504 := by
    simpa [prefixWord, tailWord_5851504, baseEnd_5851504] using wordTrace_append hprefix tailTrace_5851504
  have hstable : (prefixWord ++ tailWord_5851504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851504).length < 2 ^ (prefixWord ++ tailWord_5851504).sum := by decide
  have hdescent : baseEnd_5851504 < baseStart_5851504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851557 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_5851557 : Nat := 118140960795 + 5851557 * 2 ^ 59
def prefixEnd_5851557 : Nat := 4983230072969 + 3 ^ 40 * 5851557 * 2
def baseEnd_5851557 : Nat := 3004661318181267490026685

theorem tailTrace_5851557 : CollatzResearch.WordTrace tailWord_5851557 prefixEnd_5851557 3004661318181267490026685 := by
  unfold tailWord_5851557
  simp only [CollatzResearch.WordTrace]
  refine ⟨213423817261815830217088925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142282544841210553478059283 213423817261815830217088925)
  ·
    refine ⟨80033931473180936331408347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213423817261815830217088925 80033931473180936331408347)
    ·
      refine ⟨120050897209771404497112521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80033931473180936331408347 120050897209771404497112521)
      ·
        refine ⟨90038172907328553372834391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120050897209771404497112521 90038172907328553372834391)
        ·
          refine ⟨135057259360992830059251587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90038172907328553372834391 135057259360992830059251587)
          ·
            refine ⟨202585889041489245088877381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135057259360992830059251587 202585889041489245088877381)
            ·
              refine ⟨37984854195279233454164509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202585889041489245088877381 37984854195279233454164509)
              ·
                refine ⟨14244320323229712545311691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37984854195279233454164509 14244320323229712545311691)
                ·
                  refine ⟨21366480484844568817967537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14244320323229712545311691 21366480484844568817967537)
                  ·
                    refine ⟨16024860363633426613475653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21366480484844568817967537 16024860363633426613475653)
                    ·
                      refine ⟨3004661318181267490026685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16024860363633426613475653 3004661318181267490026685)
                      ·
                        rfl

theorem cell23_5851557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_5851557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851557 prefixEnd_5851557 := by exact prefixLift 5851557
  have htrace : WordTrace (prefixWord ++ tailWord_5851557) baseStart_5851557 baseEnd_5851557 := by
    simpa [prefixWord, tailWord_5851557, baseEnd_5851557] using wordTrace_append hprefix tailTrace_5851557
  have hstable : (prefixWord ++ tailWord_5851557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851557).length < 2 ^ (prefixWord ++ tailWord_5851557).sum := by decide
  have hdescent : baseEnd_5851557 < baseStart_5851557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851588 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5851588 : Nat := 118140960795 + 5851588 * 2 ^ 59
def prefixEnd_5851588 : Nat := 4983230072969 + 3 ^ 40 * 5851588 * 2
def baseEnd_5851588 : Nat := 1001559078693852289579681

theorem tailTrace_5851588 : CollatzResearch.WordTrace tailWord_5851588 prefixEnd_5851588 1001559078693852289579681 := by
  unfold tailWord_5851588
  simp only [CollatzResearch.WordTrace]
  refine ⟨106712473962351761255733709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142283298616469015007644945 106712473962351761255733709)
  ·
    refine ⟨40017177735881910470900141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106712473962351761255733709 40017177735881910470900141)
    ·
      refine ⟨15006441650955716426587553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40017177735881910470900141 15006441650955716426587553)
      ·
        refine ⟨11254831238216787319940665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15006441650955716426587553 11254831238216787319940665)
        ·
          refine ⟨8441123428662590489955499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11254831238216787319940665 8441123428662590489955499)
          ·
            refine ⟨12661685142993885734933249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441123428662590489955499 12661685142993885734933249)
            ·
              refine ⟨9496263857245414301199937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12661685142993885734933249 9496263857245414301199937)
              ·
                refine ⟨7122197892934060725899953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9496263857245414301199937 7122197892934060725899953)
                ·
                  refine ⟨5341648419700545544424965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7122197892934060725899953 5341648419700545544424965)
                  ·
                    refine ⟨1001559078693852289579681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5341648419700545544424965 1001559078693852289579681)
                    ·
                      rfl

theorem cell23_5851588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5851588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851588 prefixEnd_5851588 := by exact prefixLift 5851588
  have htrace : WordTrace (prefixWord ++ tailWord_5851588) baseStart_5851588 baseEnd_5851588 := by
    simpa [prefixWord, tailWord_5851588, baseEnd_5851588] using wordTrace_append hprefix tailTrace_5851588
  have hstable : (prefixWord ++ tailWord_5851588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851588).length < 2 ^ (prefixWord ++ tailWord_5851588).sum := by decide
  have hdescent : baseEnd_5851588 < baseStart_5851588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851617 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_5851617 : Nat := 118140960795 + 5851617 * 2 ^ 59
def prefixEnd_5851617 : Nat := 4983230072969 + 3 ^ 40 * 5851617 * 2
def baseEnd_5851617 : Nat := 3004692127020537255276409

theorem tailTrace_5851617 : CollatzResearch.WordTrace tailWord_5851617 prefixEnd_5851617 3004692127020537255276409 := by
  unfold tailWord_5851617
  simp only [CollatzResearch.WordTrace]
  refine ⟨213426005641598460464273105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142284003761065640309515403 213426005641598460464273105)
  ·
    refine ⟨160069504231198845348204829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213426005641598460464273105 160069504231198845348204829)
    ·
      refine ⟨60026064086699567005576811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160069504231198845348204829 60026064086699567005576811)
      ·
        refine ⟨90039096130049350508365217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60026064086699567005576811 90039096130049350508365217)
        ·
          refine ⟨67529322097537012881273913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90039096130049350508365217 67529322097537012881273913)
          ·
            refine ⟨50646991573152759660955435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67529322097537012881273913 50646991573152759660955435)
            ·
              refine ⟨75970487359729139491433153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50646991573152759660955435 75970487359729139491433153)
              ·
                refine ⟨56977865519796854618574865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75970487359729139491433153 56977865519796854618574865)
                ·
                  refine ⟨42733399139847640963931149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56977865519796854618574865 42733399139847640963931149)
                  ·
                    refine ⟨16025024677442865361474181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42733399139847640963931149 16025024677442865361474181)
                    ·
                      refine ⟨3004692127020537255276409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16025024677442865361474181 3004692127020537255276409)
                      ·
                        rfl

theorem cell23_5851617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_5851617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851617 prefixEnd_5851617 := by exact prefixLift 5851617
  have htrace : WordTrace (prefixWord ++ tailWord_5851617) baseStart_5851617 baseEnd_5851617 := by
    simpa [prefixWord, tailWord_5851617, baseEnd_5851617] using wordTrace_append hprefix tailTrace_5851617
  have hstable : (prefixWord ++ tailWord_5851617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851617).length < 2 ^ (prefixWord ++ tailWord_5851617).sum := by decide
  have hdescent : baseEnd_5851617 < baseStart_5851617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851618 : List Nat := [3, 3, 3, 2, 1, 1, 3, 7]
def baseStart_5851618 : Nat := 118140960795 + 5851618 * 2 ^ 59
def prefixEnd_5851618 : Nat := 4983230072969 + 3 ^ 40 * 5851618 * 2
def baseEnd_5851618 : Nat := 111284912611155250050515

theorem tailTrace_5851618 : CollatzResearch.WordTrace tailWord_5851618 prefixEnd_5851618 111284912611155250050515 := by
  unfold tailWord_5851618
  simp only [CollatzResearch.WordTrace]
  refine ⟨53356510528648709408764877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142284028076396558423373005 53356510528648709408764877)
  ·
    refine ⟨20008691448243266028286829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53356510528648709408764877 20008691448243266028286829)
    ·
      refine ⟨7503259293091224760607561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20008691448243266028286829 7503259293091224760607561)
      ·
        refine ⟨5627444469818418570455671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7503259293091224760607561 5627444469818418570455671)
        ·
          refine ⟨8441166704727627855683507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627444469818418570455671 8441166704727627855683507)
          ·
            refine ⟨12661750057091441783525261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441166704727627855683507 12661750057091441783525261)
            ·
              refine ⟨4748156271409290668821973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12661750057091441783525261 4748156271409290668821973)
              ·
                refine ⟨111284912611155250050515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4748156271409290668821973 111284912611155250050515)
                ·
                  rfl

theorem cell23_5851618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 7].length) (baseStart_5851618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851618 prefixEnd_5851618 := by exact prefixLift 5851618
  have htrace : WordTrace (prefixWord ++ tailWord_5851618) baseStart_5851618 baseEnd_5851618 := by
    simpa [prefixWord, tailWord_5851618, baseEnd_5851618] using wordTrace_append hprefix tailTrace_5851618
  have hstable : (prefixWord ++ tailWord_5851618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851618).length < 2 ^ (prefixWord ++ tailWord_5851618).sum := by decide
  have hdescent : baseEnd_5851618 < baseStart_5851618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851638 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_5851638 : Nat := 118140960795 + 5851638 * 2 ^ 59
def prefixEnd_5851638 : Nat := 4983230072969 + 3 ^ 40 * 5851638 * 2
def baseEnd_5851638 : Nat := 3004702910114281673113813

theorem tailTrace_5851638 : CollatzResearch.WordTrace tailWord_5851638 prefixEnd_5851638 3004702910114281673113813 := by
  unfold tailWord_5851638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339173223407648815674223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142284514383014920700525045 13339173223407648815674223)
  ·
    refine ⟨20008759835111473223511335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13339173223407648815674223 20008759835111473223511335)
    ·
      refine ⟨30013139752667209835267003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20008759835111473223511335 30013139752667209835267003)
      ·
        refine ⟨45019709629000814752900505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30013139752667209835267003 45019709629000814752900505)
        ·
          refine ⟨33764782221750611064675379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45019709629000814752900505 33764782221750611064675379)
          ·
            refine ⟨50647173332625916597013069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33764782221750611064675379 50647173332625916597013069)
            ·
              refine ⟨18992689999734718723879901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50647173332625916597013069 18992689999734718723879901)
              ·
                refine ⟨7122258749900519521454963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18992689999734718723879901 7122258749900519521454963)
                ·
                  refine ⟨10683388124850779282182445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122258749900519521454963 10683388124850779282182445)
                  ·
                    refine ⟨4006270546819042230818417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10683388124850779282182445 4006270546819042230818417)
                    ·
                      refine ⟨3004702910114281673113813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006270546819042230818417 3004702910114281673113813)
                      ·
                        rfl

theorem cell23_5851638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_5851638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851638 prefixEnd_5851638 := by exact prefixLift 5851638
  have htrace : WordTrace (prefixWord ++ tailWord_5851638) baseStart_5851638 baseEnd_5851638 := by
    simpa [prefixWord, tailWord_5851638, baseEnd_5851638] using wordTrace_append hprefix tailTrace_5851638
  have hstable : (prefixWord ++ tailWord_5851638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851638).length < 2 ^ (prefixWord ++ tailWord_5851638).sum := by decide
  have hdescent : baseEnd_5851638 < baseStart_5851638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851647 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_5851647 : Nat := 118140960795 + 5851647 * 2 ^ 59
def prefixEnd_5851647 : Nat := 4983230072969 + 3 ^ 40 * 5851647 * 2
def baseEnd_5851647 : Nat := 3004707531440172137901271

theorem tailTrace_5851647 : CollatzResearch.WordTrace tailWord_5851647 prefixEnd_5851647 3004707531440172137901271 := by
  unfold tailWord_5851647
  simp only [CollatzResearch.WordTrace]
  refine ⟨213427099831489775587865195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142284733220993183725243463 213427099831489775587865195)
  ·
    refine ⟨320140649747234663381797793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213427099831489775587865195 320140649747234663381797793)
    ·
      refine ⟨240105487310425997536348345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320140649747234663381797793 240105487310425997536348345)
      ·
        refine ⟨180079115482819498152261259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240105487310425997536348345 180079115482819498152261259)
        ·
          refine ⟨270118673224229247228391889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180079115482819498152261259 270118673224229247228391889)
          ·
            refine ⟨202589004918171935421293917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270118673224229247228391889 202589004918171935421293917)
            ·
              refine ⟨75970876844314475782985219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202589004918171935421293917 75970876844314475782985219)
              ·
                refine ⟨113956315266471713674477829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75970876844314475782985219 113956315266471713674477829)
                ·
                  refine ⟨21366809112463446313964593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113956315266471713674477829 21366809112463446313964593)
                  ·
                    refine ⟨16025106834347584735473445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21366809112463446313964593 16025106834347584735473445)
                    ·
                      refine ⟨3004707531440172137901271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16025106834347584735473445 3004707531440172137901271)
                      ·
                        rfl

theorem cell23_5851647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_5851647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851647 prefixEnd_5851647 := by exact prefixLift 5851647
  have htrace : WordTrace (prefixWord ++ tailWord_5851647) baseStart_5851647 baseEnd_5851647 := by
    simpa [prefixWord, tailWord_5851647, baseEnd_5851647] using wordTrace_append hprefix tailTrace_5851647
  have hstable : (prefixWord ++ tailWord_5851647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851647).length < 2 ^ (prefixWord ++ tailWord_5851647).sum := by decide
  have hdescent : baseEnd_5851647 < baseStart_5851647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851651 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 4, 2, 2]
def baseStart_5851651 : Nat := 118140960795 + 5851651 * 2 ^ 59
def prefixEnd_5851651 : Nat := 4983230072969 + 3 ^ 40 * 5851651 * 2
def baseEnd_5851651 : Nat := 3004709585362790122251253

theorem tailTrace_5851651 : CollatzResearch.WordTrace tailWord_5851651 prefixEnd_5851651 3004709585362790122251253 := by
  unfold tailWord_5851651
  simp only [CollatzResearch.WordTrace]
  refine ⟨213427245723475284271010807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142284830482316856180673871 213427245723475284271010807)
  ·
    refine ⟨320140868585212926406516211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213427245723475284271010807 320140868585212926406516211)
    ·
      refine ⟨480211302877819389609774317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320140868585212926406516211 480211302877819389609774317)
      ·
        refine ⟨180079238579182271103665369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480211302877819389609774317 180079238579182271103665369)
        ·
          refine ⟨135059428934386703327749027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180079238579182271103665369 135059428934386703327749027)
          ·
            refine ⟨202589143401580054991623541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135059428934386703327749027 202589143401580054991623541)
            ·
              refine ⟨18992732193898130155464707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202589143401580054991623541 18992732193898130155464707)
              ·
                refine ⟨28489098290847195233197061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18992732193898130155464707 28489098290847195233197061)
                ·
                  refine ⟨5341705929533849106224449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28489098290847195233197061 5341705929533849106224449)
                  ·
                    refine ⟨4006279447150386829668337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341705929533849106224449 4006279447150386829668337)
                    ·
                      refine ⟨3004709585362790122251253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006279447150386829668337 3004709585362790122251253)
                      ·
                        rfl

theorem cell23_5851651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_5851651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851651 prefixEnd_5851651 := by exact prefixLift 5851651
  have htrace : WordTrace (prefixWord ++ tailWord_5851651) baseStart_5851651 baseEnd_5851651 := by
    simpa [prefixWord, tailWord_5851651, baseEnd_5851651] using wordTrace_append hprefix tailTrace_5851651
  have hstable : (prefixWord ++ tailWord_5851651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851651).length < 2 ^ (prefixWord ++ tailWord_5851651).sum := by decide
  have hdescent : baseEnd_5851651 < baseStart_5851651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851704 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 2, 5]
def baseStart_5851704 : Nat := 118140960795 + 5851704 * 2 ^ 59
def prefixEnd_5851704 : Nat := 4983230072969 + 3 ^ 40 * 5851704 * 2
def baseEnd_5851704 : Nat := 1001578933279159471629503

theorem tailTrace_5851704 : CollatzResearch.WordTrace tailWord_5851704 prefixEnd_5851704 1001578933279159471629503 := by
  unfold tailWord_5851704
  simp only [CollatzResearch.WordTrace]
  refine ⟨106714589396141637161345083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142286119194855516215126777 106714589396141637161345083)
  ·
    refine ⟨160071884094212455742017625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106714589396141637161345083 160071884094212455742017625)
    ·
      refine ⟨120053913070659341806513219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160071884094212455742017625 120053913070659341806513219)
      ·
        refine ⟨180080869605989012709769829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120053913070659341806513219 180080869605989012709769829)
        ·
          refine ⟨33765163051122939883081843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180080869605989012709769829 33765163051122939883081843)
          ·
            refine ⟨50647744576684409824622765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33765163051122939883081843 50647744576684409824622765)
            ·
              refine ⟨18992904216256653684233537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50647744576684409824622765 18992904216256653684233537)
              ·
                refine ⟨14244678162192490263175153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18992904216256653684233537 14244678162192490263175153)
                ·
                  refine ⟨10683508621644367697381365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14244678162192490263175153 10683508621644367697381365)
                  ·
                    refine ⟨1001578933279159471629503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10683508621644367697381365 1001578933279159471629503)
                    ·
                      rfl

theorem cell23_5851704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_5851704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851704 prefixEnd_5851704 := by exact prefixLift 5851704
  have htrace : WordTrace (prefixWord ++ tailWord_5851704) baseStart_5851704 baseEnd_5851704 := by
    simpa [prefixWord, tailWord_5851704, baseEnd_5851704] using wordTrace_append hprefix tailTrace_5851704
  have hstable : (prefixWord ++ tailWord_5851704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851704).length < 2 ^ (prefixWord ++ tailWord_5851704).sum := by decide
  have hdescent : baseEnd_5851704 < baseStart_5851704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851708 : List Nat := [2, 2, 2, 2, 3, 2, 3, 2, 5]
def baseStart_5851708 : Nat := 118140960795 + 5851708 * 2 ^ 59
def prefixEnd_5851708 : Nat := 4983230072969 + 3 ^ 40 * 5851708 * 2
def baseEnd_5851708 : Nat := 333859872640010711026499

theorem tailTrace_5851708 : CollatzResearch.WordTrace tailWord_5851708 prefixEnd_5851708 333859872640010711026499 := by
  unfold tailWord_5851708
  simp only [CollatzResearch.WordTrace]
  refine ⟨106714662342134391502917889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142286216456179188670557185 106714662342134391502917889)
  ·
    refine ⟨80035996756600793627188417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106714662342134391502917889 80035996756600793627188417)
    ·
      refine ⟨60026997567450595220391313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80035996756600793627188417 60026997567450595220391313)
      ·
        refine ⟨45020248175587946415293485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60026997567450595220391313 45020248175587946415293485)
        ·
          refine ⟨16882593065845479905735057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45020248175587946415293485 16882593065845479905735057)
          ·
            refine ⟨12661944799384109929301293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16882593065845479905735057 12661944799384109929301293)
            ·
              refine ⟨4748229299769041223487985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12661944799384109929301293 4748229299769041223487985)
              ·
                refine ⟨3561171974826780917615989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4748229299769041223487985 3561171974826780917615989)
                ·
                  refine ⟨333859872640010711026499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3561171974826780917615989 333859872640010711026499)
                  ·
                    rfl

theorem cell23_5851708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_5851708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851708 prefixEnd_5851708 := by exact prefixLift 5851708
  have htrace : WordTrace (prefixWord ++ tailWord_5851708) baseStart_5851708 baseEnd_5851708 := by
    simpa [prefixWord, tailWord_5851708, baseEnd_5851708] using wordTrace_append hprefix tailTrace_5851708
  have hstable : (prefixWord ++ tailWord_5851708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851708).length < 2 ^ (prefixWord ++ tailWord_5851708).sum := by decide
  have hdescent : baseEnd_5851708 < baseStart_5851708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851724 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5851724 : Nat := 118140960795 + 5851724 * 2 ^ 59
def prefixEnd_5851724 : Nat := 4983230072969 + 3 ^ 40 * 5851724 * 2
def baseEnd_5851724 : Nat := 3004747069450568336638417

theorem tailTrace_5851724 : CollatzResearch.WordTrace tailWord_5851724 prefixEnd_5851724 3004747069450568336638417 := by
  unfold tailWord_5851724
  simp only [CollatzResearch.WordTrace]
  refine ⟨106714954126105408869209113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142286605501473878492278817 106714954126105408869209113)
  ·
    refine ⟨80036215594579056651906835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106714954126105408869209113 80036215594579056651906835)
    ·
      refine ⟨120054323391868584977860253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80036215594579056651906835 120054323391868584977860253)
      ·
        refine ⟨45020371271950719366697595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120054323391868584977860253 45020371271950719366697595)
        ·
          refine ⟨67530556907926079050046393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45020371271950719366697595 67530556907926079050046393)
          ·
            refine ⟨50647917680944559287534795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67530556907926079050046393 50647917680944559287534795)
            ·
              refine ⟨75971876521416838931302193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50647917680944559287534795 75971876521416838931302193)
              ·
                refine ⟨56978907391062629198476645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75971876521416838931302193 56978907391062629198476645)
                ·
                  refine ⟨10683545135824242974714371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56978907391062629198476645 10683545135824242974714371)
                  ·
                    refine ⟨16025317703736364462071557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10683545135824242974714371 16025317703736364462071557)
                    ·
                      refine ⟨3004747069450568336638417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16025317703736364462071557 3004747069450568336638417)
                      ·
                        rfl

theorem cell23_5851724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5851724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851724 prefixEnd_5851724 := by exact prefixLift 5851724
  have htrace : WordTrace (prefixWord ++ tailWord_5851724) baseStart_5851724 baseEnd_5851724 := by
    simpa [prefixWord, tailWord_5851724, baseEnd_5851724] using wordTrace_append hprefix tailTrace_5851724
  have hstable : (prefixWord ++ tailWord_5851724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851724).length < 2 ^ (prefixWord ++ tailWord_5851724).sum := by decide
  have hdescent : baseEnd_5851724 < baseStart_5851724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851737 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_5851737 : Nat := 118140960795 + 5851737 * 2 ^ 59
def prefixEnd_5851737 : Nat := 4983230072969 + 3 ^ 40 * 5851737 * 2
def baseEnd_5851737 : Nat := 3004753744699076785775857

theorem tailTrace_5851737 : CollatzResearch.WordTrace tailWord_5851737 prefixEnd_5851737 3004753744699076785775857 := by
  unfold tailWord_5851737
  simp only [CollatzResearch.WordTrace]
  refine ⟨213430382401163720958641465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142286921600775813972427643 213430382401163720958641465)
  ·
    refine ⟨160072786800872790718981099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213430382401163720958641465 160072786800872790718981099)
    ·
      refine ⟨240109180201309186078471649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160072786800872790718981099 240109180201309186078471649)
      ·
        refine ⟨180081885150981889558853737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240109180201309186078471649 180081885150981889558853737)
        ·
          refine ⟨135061413863236417169140303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180081885150981889558853737 135061413863236417169140303)
          ·
            refine ⟨202592120794854625753710455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135061413863236417169140303 202592120794854625753710455)
            ·
              refine ⟨303888181192281938630565683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202592120794854625753710455 303888181192281938630565683)
              ·
                refine ⟨455832271788422907945848525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303888181192281938630565683 455832271788422907945848525)
                ·
                  refine ⟨170937101920658590479693197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455832271788422907945848525 170937101920658590479693197)
                  ·
                    refine ⟨64101413220246971429884949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170937101920658590479693197 64101413220246971429884949)
                    ·
                      refine ⟨3004753744699076785775857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64101413220246971429884949 3004753744699076785775857)
                      ·
                        rfl

theorem cell23_5851737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_5851737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851737 prefixEnd_5851737 := by exact prefixLift 5851737
  have htrace : WordTrace (prefixWord ++ tailWord_5851737) baseStart_5851737 baseEnd_5851737 := by
    simpa [prefixWord, tailWord_5851737, baseEnd_5851737] using wordTrace_append hprefix tailTrace_5851737
  have hstable : (prefixWord ++ tailWord_5851737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851737).length < 2 ^ (prefixWord ++ tailWord_5851737).sum := by decide
  have hdescent : baseEnd_5851737 < baseStart_5851737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851744 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3]
def baseStart_5851744 : Nat := 118140960795 + 5851744 * 2 ^ 59
def prefixEnd_5851744 : Nat := 4983230072969 + 3 ^ 40 * 5851744 * 2
def baseEnd_5851744 : Nat := 3004757339063658258388325

theorem tailTrace_5851744 : CollatzResearch.WordTrace tailWord_5851744 prefixEnd_5851744 3004757339063658258388325 := by
  unfold tailWord_5851744
  simp only [CollatzResearch.WordTrace]
  refine ⟨106715318856069180577073143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142287091808092240769430857 106715318856069180577073143)
  ·
    refine ⟨160072978284103770865609715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106715318856069180577073143 160072978284103770865609715)
    ·
      refine ⟨240109467426155656298414573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160072978284103770865609715 240109467426155656298414573)
      ·
        refine ⟨90041050284808371111905465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240109467426155656298414573 90041050284808371111905465)
        ·
          refine ⟨67530787713606278333929099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90041050284808371111905465 67530787713606278333929099)
          ·
            refine ⟨101296181570409417500893649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67530787713606278333929099 101296181570409417500893649)
            ·
              refine ⟨75972136177807063125670237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101296181570409417500893649 75972136177807063125670237)
              ·
                refine ⟨28489551066677648672126339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75972136177807063125670237 28489551066677648672126339)
                ·
                  refine ⟨42734326600016473008189509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28489551066677648672126339 42734326600016473008189509)
                  ·
                    refine ⟨8012686237503088689035533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42734326600016473008189509 8012686237503088689035533)
                    ·
                      refine ⟨3004757339063658258388325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8012686237503088689035533 3004757339063658258388325)
                      ·
                        rfl

theorem cell23_5851744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_5851744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851744 prefixEnd_5851744 := by exact prefixLift 5851744
  have htrace : WordTrace (prefixWord ++ tailWord_5851744) baseStart_5851744 baseEnd_5851744 := by
    simpa [prefixWord, tailWord_5851744, baseEnd_5851744] using wordTrace_append hprefix tailTrace_5851744
  have hstable : (prefixWord ++ tailWord_5851744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851744).length < 2 ^ (prefixWord ++ tailWord_5851744).sum := by decide
  have hdescent : baseEnd_5851744 < baseStart_5851744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851754 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5851754 : Nat := 118140960795 + 5851754 * 2 ^ 59
def prefixEnd_5851754 : Nat := 4983230072969 + 3 ^ 40 * 5851754 * 2
def baseEnd_5851754 : Nat := 3004762473870203219263279

theorem tailTrace_5851754 : CollatzResearch.WordTrace tailWord_5851754 prefixEnd_5851754 3004762473870203219263279 := by
  unfold tailWord_5851754
  simp only [CollatzResearch.WordTrace]
  refine ⟨53357750610525533215502579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142287334961401421908006877 53357750610525533215502579)
  ·
    refine ⟨80036625915788299823253869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53357750610525533215502579 80036625915788299823253869)
    ·
      refine ⟨30013734718420612433720201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80036625915788299823253869 30013734718420612433720201)
      ·
        refine ⟨22510301038815459325290151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30013734718420612433720201 22510301038815459325290151)
        ·
          refine ⟨33765451558223188987935227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22510301038815459325290151 33765451558223188987935227)
          ·
            refine ⟨50648177337334783481902841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33765451558223188987935227 50648177337334783481902841)
            ·
              refine ⟨37986133003001087611427131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50648177337334783481902841 37986133003001087611427131)
              ·
                refine ⟨56979199504501631417140697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37986133003001087611427131 56979199504501631417140697)
                ·
                  refine ⟨42734399628376223562855523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56979199504501631417140697 42734399628376223562855523)
                  ·
                    refine ⟨64101599442564335344283285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42734399628376223562855523 64101599442564335344283285)
                    ·
                      refine ⟨3004762473870203219263279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64101599442564335344283285 3004762473870203219263279)
                      ·
                        rfl

theorem cell23_5851754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5851754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851754 prefixEnd_5851754 := by exact prefixLift 5851754
  have htrace : WordTrace (prefixWord ++ tailWord_5851754) baseStart_5851754 baseEnd_5851754 := by
    simpa [prefixWord, tailWord_5851754, baseEnd_5851754] using wordTrace_append hprefix tailTrace_5851754
  have hstable : (prefixWord ++ tailWord_5851754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851754).length < 2 ^ (prefixWord ++ tailWord_5851754).sum := by decide
  have hdescent : baseEnd_5851754 < baseStart_5851754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851791 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 3]
def baseStart_5851791 : Nat := 118140960795 + 5851791 * 2 ^ 59
def prefixEnd_5851791 : Nat := 4983230072969 + 3 ^ 40 * 5851791 * 2
def baseEnd_5851791 : Nat := 3004781472654419574500609

theorem tailTrace_5851791 : CollatzResearch.WordTrace tailWord_5851791 prefixEnd_5851791 3004781472654419574500609 := by
  unfold tailWord_5851791
  simp only [CollatzResearch.WordTrace]
  refine ⟨213432351942968088181107227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142288234628645392120738151 213432351942968088181107227)
  ·
    refine ⟨320148527914452132271660841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213432351942968088181107227 320148527914452132271660841)
    ·
      refine ⟨240111395935839099203745631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320148527914452132271660841 240111395935839099203745631)
      ·
        refine ⟨360167093903758648805618447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240111395935839099203745631 360167093903758648805618447)
        ·
          refine ⟨540250640855637973208427671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360167093903758648805618447 540250640855637973208427671)
          ·
            refine ⟨810375961283456959812641507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540250640855637973208427671 810375961283456959812641507)
            ·
              refine ⟨1215563941925185439718962261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810375961283456959812641507 1215563941925185439718962261)
              ·
                refine ⟨14244889944435766871706589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1215563941925185439718962261 14244889944435766871706589)
                ·
                  refine ⟨5341833729163412576889971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14244889944435766871706589 5341833729163412576889971)
                  ·
                    refine ⟨8012750593745118865334957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5341833729163412576889971 8012750593745118865334957)
                    ·
                      refine ⟨3004781472654419574500609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8012750593745118865334957 3004781472654419574500609)
                      ·
                        rfl

theorem cell23_5851791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 3].length) (baseStart_5851791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851791 prefixEnd_5851791 := by exact prefixLift 5851791
  have htrace : WordTrace (prefixWord ++ tailWord_5851791) baseStart_5851791 baseEnd_5851791 := by
    simpa [prefixWord, tailWord_5851791, baseEnd_5851791] using wordTrace_append hprefix tailTrace_5851791
  have hstable : (prefixWord ++ tailWord_5851791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851791).length < 2 ^ (prefixWord ++ tailWord_5851791).sum := by decide
  have hdescent : baseEnd_5851791 < baseStart_5851791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851801 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 1, 5, 2]
def baseStart_5851801 : Nat := 118140960795 + 5851801 * 2 ^ 59
def prefixEnd_5851801 : Nat := 4983230072969 + 3 ^ 40 * 5851801 * 2
def baseEnd_5851801 : Nat := 3004786607460964535375563

theorem tailTrace_5851801 : CollatzResearch.WordTrace tailWord_5851801 prefixEnd_5851801 3004786607460964535375563 := by
  unfold tailWord_5851801
  simp only [CollatzResearch.WordTrace]
  refine ⟨213432716672931859888971257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142288477781954573259314171 213432716672931859888971257)
  ·
    refine ⟨160074537504698894916728443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213432716672931859888971257 160074537504698894916728443)
    ·
      refine ⟨240111806257048342375092665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160074537504698894916728443 240111806257048342375092665)
      ·
        refine ⟨180083854692786256781319499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240111806257048342375092665 180083854692786256781319499)
        ·
          refine ⟨270125782039179385171979249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180083854692786256781319499 270125782039179385171979249)
          ·
            refine ⟨202594336529384538878984437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270125782039179385171979249 202594336529384538878984437)
            ·
              refine ⟨18993219049629800519904791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202594336529384538878984437 18993219049629800519904791)
              ·
                refine ⟨28489828574444700779857187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18993219049629800519904791 28489828574444700779857187)
                ·
                  refine ⟨42734742861667051169785781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28489828574444700779857187 42734742861667051169785781)
                  ·
                    refine ⟨4006382143281286047167417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42734742861667051169785781 4006382143281286047167417)
                    ·
                      refine ⟨3004786607460964535375563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006382143281286047167417 3004786607460964535375563)
                      ·
                        rfl

theorem cell23_5851801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_5851801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851801 prefixEnd_5851801 := by exact prefixLift 5851801
  have htrace : WordTrace (prefixWord ++ tailWord_5851801) baseStart_5851801 baseEnd_5851801 := by
    simpa [prefixWord, tailWord_5851801, baseEnd_5851801] using wordTrace_append hprefix tailTrace_5851801
  have hstable : (prefixWord ++ tailWord_5851801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851801).length < 2 ^ (prefixWord ++ tailWord_5851801).sum := by decide
  have hdescent : baseEnd_5851801 < baseStart_5851801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851802 : List Nat := [3, 1, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_5851802 : Nat := 118140960795 + 5851802 * 2 ^ 59
def prefixEnd_5851802 : Nat := 4983230072969 + 3 ^ 40 * 5851802 * 2
def baseEnd_5851802 : Nat := 1001595706980539677154353

theorem tailTrace_5851802 : CollatzResearch.WordTrace tailWord_5851802 prefixEnd_5851802 1001595706980539677154353 := by
  unfold tailWord_5851802
  simp only [CollatzResearch.WordTrace]
  refine ⟨53358188286482059264939415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142288502097285491373171773 53358188286482059264939415)
  ·
    refine ⟨80037282429723088897409123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53358188286482059264939415 80037282429723088897409123)
    ·
      refine ⟨120055923644584633346113685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80037282429723088897409123 120055923644584633346113685)
      ·
        refine ⟨5627621420839904688099079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120055923644584633346113685 5627621420839904688099079)
        ·
          refine ⟨8441432131259857032148619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627621420839904688099079 8441432131259857032148619)
          ·
            refine ⟨12662148196889785548222929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441432131259857032148619 12662148196889785548222929)
            ·
              refine ⟨9496611147667339161167197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12662148196889785548222929 9496611147667339161167197)
              ·
                refine ⟨3561229180375252185437699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9496611147667339161167197 3561229180375252185437699)
                ·
                  refine ⟨5341843770562878278156549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561229180375252185437699 5341843770562878278156549)
                  ·
                    refine ⟨1001595706980539677154353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5341843770562878278156549 1001595706980539677154353)
                    ·
                      rfl

theorem cell23_5851802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_5851802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851802 prefixEnd_5851802 := by exact prefixLift 5851802
  have htrace : WordTrace (prefixWord ++ tailWord_5851802) baseStart_5851802 baseEnd_5851802 := by
    simpa [prefixWord, tailWord_5851802, baseEnd_5851802] using wordTrace_append hprefix tailTrace_5851802
  have hstable : (prefixWord ++ tailWord_5851802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851802).length < 2 ^ (prefixWord ++ tailWord_5851802).sum := by decide
  have hdescent : baseEnd_5851802 < baseStart_5851802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851815 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 6]
def baseStart_5851815 : Nat := 118140960795 + 5851815 * 2 ^ 59
def prefixEnd_5851815 : Nat := 4983230072969 + 3 ^ 40 * 5851815 * 2
def baseEnd_5851815 : Nat := 333865977354458608955611

theorem tailTrace_5851815 : CollatzResearch.WordTrace tailWord_5851815 prefixEnd_5851815 333865977354458608955611 := by
  unfold tailWord_5851815
  simp only [CollatzResearch.WordTrace]
  refine ⟨213433227294881140279980899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142288818196587426853320599 213433227294881140279980899)
  ·
    refine ⟨320149840942321710419971349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213433227294881140279980899 320149840942321710419971349)
    ·
      refine ⟨15007023794171330175936157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 320149840942321710419971349 15007023794171330175936157)
      ·
        refine ⟨5627633922814248815976059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15007023794171330175936157 5627633922814248815976059)
        ·
          refine ⟨8441450884221373223964089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627633922814248815976059 8441450884221373223964089)
          ·
            refine ⟨6331088163166029917973067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8441450884221373223964089 6331088163166029917973067)
            ·
              refine ⟨9496632244749044876959601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331088163166029917973067 9496632244749044876959601)
              ·
                refine ⟨7122474183561783657719701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9496632244749044876959601 7122474183561783657719701)
                ·
                  refine ⟨333865977354458608955611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7122474183561783657719701 333865977354458608955611)
                  ·
                    rfl

theorem cell23_5851815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 6].length) (baseStart_5851815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851815 prefixEnd_5851815 := by exact prefixLift 5851815
  have htrace : WordTrace (prefixWord ++ tailWord_5851815) baseStart_5851815 baseEnd_5851815 := by
    simpa [prefixWord, tailWord_5851815, baseEnd_5851815] using wordTrace_append hprefix tailTrace_5851815
  have hstable : (prefixWord ++ tailWord_5851815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851815).length < 2 ^ (prefixWord ++ tailWord_5851815).sum := by decide
  have hdescent : baseEnd_5851815 < baseStart_5851815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851848 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_5851848 : Nat := 118140960795 + 5851848 * 2 ^ 59
def prefixEnd_5851848 : Nat := 4983230072969 + 3 ^ 40 * 5851848 * 2
def baseEnd_5851848 : Nat := 3004810741051725851487847

theorem tailTrace_5851848 : CollatzResearch.WordTrace tailWord_5851848 prefixEnd_5851848 3004810741051725851487847 := by
  unfold tailWord_5851848
  simp only [CollatzResearch.WordTrace]
  refine ⟨106717215451880793457966099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142289620602507724610621465 106717215451880793457966099)
  ·
    refine ⟨160075823177821190186949149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106717215451880793457966099 160075823177821190186949149)
    ·
      refine ⟨60028433691682946320105931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160075823177821190186949149 60028433691682946320105931)
      ·
        refine ⟨90042650537524419480158897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60028433691682946320105931 90042650537524419480158897)
        ·
          refine ⟨67531987903143314610119173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90042650537524419480158897 67531987903143314610119173)
          ·
            refine ⟨12662247731839371489397345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67531987903143314610119173 12662247731839371489397345)
            ·
              refine ⟨9496685798879528617048009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12662247731839371489397345 9496685798879528617048009)
              ·
                refine ⟨7122514349159646462786007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9496685798879528617048009 7122514349159646462786007)
                ·
                  refine ⟨10683771523739469694179011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122514349159646462786007 10683771523739469694179011)
                  ·
                    refine ⟨16025657285609204541268517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10683771523739469694179011 16025657285609204541268517)
                    ·
                      refine ⟨3004810741051725851487847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16025657285609204541268517 3004810741051725851487847)
                      ·
                        rfl

theorem cell23_5851848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_5851848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851848 prefixEnd_5851848 := by exact prefixLift 5851848
  have htrace : WordTrace (prefixWord ++ tailWord_5851848) baseStart_5851848 baseEnd_5851848 := by
    simpa [prefixWord, tailWord_5851848, baseEnd_5851848] using wordTrace_append hprefix tailTrace_5851848
  have hstable : (prefixWord ++ tailWord_5851848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851848).length < 2 ^ (prefixWord ++ tailWord_5851848).sum := by decide
  have hdescent : baseEnd_5851848 < baseStart_5851848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851868 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5851868 : Nat := 118140960795 + 5851868 * 2 ^ 59
def prefixEnd_5851868 : Nat := 4983230072969 + 3 ^ 40 * 5851868 * 2
def baseEnd_5851868 : Nat := 3004821010664815773237755

theorem tailTrace_5851868 : CollatzResearch.WordTrace tailWord_5851868 prefixEnd_5851868 3004821010664815773237755 := by
  unfold tailWord_5851868
  simp only [CollatzResearch.WordTrace]
  refine ⟨106717580181844565165830129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142290106909126086887773505 106717580181844565165830129)
  ·
    refine ⟨80038185136383423874372597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106717580181844565165830129 80038185136383423874372597)
    ·
      refine ⟨7503579856535945988222431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80038185136383423874372597 7503579856535945988222431)
      ·
        refine ⟨11255369784803918982333647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7503579856535945988222431 11255369784803918982333647)
        ·
          refine ⟨16883054677205878473500471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11255369784803918982333647 16883054677205878473500471)
          ·
            refine ⟨25324582015808817710250707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16883054677205878473500471 25324582015808817710250707)
            ·
              refine ⟨37986873023713226565376061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25324582015808817710250707 37986873023713226565376061)
              ·
                refine ⟨14245077383892459962016023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37986873023713226565376061 14245077383892459962016023)
                ·
                  refine ⟨21367616075838689943024035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14245077383892459962016023 21367616075838689943024035)
                  ·
                    refine ⟨32051424113758034914536053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21367616075838689943024035 32051424113758034914536053)
                    ·
                      refine ⟨3004821010664815773237755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32051424113758034914536053 3004821010664815773237755)
                      ·
                        rfl

theorem cell23_5851868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5851868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851868 prefixEnd_5851868 := by exact prefixLift 5851868
  have htrace : WordTrace (prefixWord ++ tailWord_5851868) baseStart_5851868 baseEnd_5851868 := by
    simpa [prefixWord, tailWord_5851868, baseEnd_5851868] using wordTrace_append hprefix tailTrace_5851868
  have hstable : (prefixWord ++ tailWord_5851868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851868).length < 2 ^ (prefixWord ++ tailWord_5851868).sum := by decide
  have hdescent : baseEnd_5851868 < baseStart_5851868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851884 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_5851884 : Nat := 118140960795 + 5851884 * 2 ^ 59
def prefixEnd_5851884 : Nat := 4983230072969 + 3 ^ 40 * 5851884 * 2
def baseEnd_5851884 : Nat := 1001609742118429236879227

theorem tailTrace_5851884 : CollatzResearch.WordTrace tailWord_5851884 prefixEnd_5851884 1001609742118429236879227 := by
  unfold tailWord_5851884
  simp only [CollatzResearch.WordTrace]
  refine ⟨106717871965815582532121353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142290495954420776709495137 106717871965815582532121353)
  ·
    refine ⟨80038403974361686899091015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106717871965815582532121353 80038403974361686899091015)
    ·
      refine ⟨120057605961542530348636523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80038403974361686899091015 120057605961542530348636523)
      ·
        refine ⟨180086408942313795522954785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120057605961542530348636523 180086408942313795522954785)
        ·
          refine ⟨135064806706735346642216089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180086408942313795522954785 135064806706735346642216089)
          ·
            refine ⟨101298605030051509981662067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135064806706735346642216089 101298605030051509981662067)
            ·
              refine ⟨151947907545077264972493101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101298605030051509981662067 151947907545077264972493101)
              ·
                refine ⟨56980465329403974364684913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151947907545077264972493101 56980465329403974364684913)
                ·
                  refine ⟨42735348997052980773513685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56980465329403974364684913 42735348997052980773513685)
                  ·
                    refine ⟨1001609742118429236879227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42735348997052980773513685 1001609742118429236879227)
                    ·
                      rfl

theorem cell23_5851884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_5851884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851884 prefixEnd_5851884 := by exact prefixLift 5851884
  have htrace : WordTrace (prefixWord ++ tailWord_5851884) baseStart_5851884 baseEnd_5851884 := by
    simpa [prefixWord, tailWord_5851884, baseEnd_5851884] using wordTrace_append hprefix tailTrace_5851884
  have hstable : (prefixWord ++ tailWord_5851884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851884).length < 2 ^ (prefixWord ++ tailWord_5851884).sum := by decide
  have hdescent : baseEnd_5851884 < baseStart_5851884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851891 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 7, 2]
def baseStart_5851891 : Nat := 118140960795 + 5851891 * 2 ^ 59
def prefixEnd_5851891 : Nat := 4983230072969 + 3 ^ 40 * 5851891 * 2
def baseEnd_5851891 : Nat := 3004832820719869183250149

theorem tailTrace_5851891 : CollatzResearch.WordTrace tailWord_5851891 prefixEnd_5851891 3004832820719869183250149 := by
  unfold tailWord_5851891
  simp only [CollatzResearch.WordTrace]
  refine ⟨213435999242605805259747527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142290666161737203506498351 213435999242605805259747527)
  ·
    refine ⟨320153998863908707889621291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213435999242605805259747527 320153998863908707889621291)
    ·
      refine ⟨480230998295863061834431937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320153998863908707889621291 480230998295863061834431937)
      ·
        refine ⟨360173248721897296375823953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480230998295863061834431937 360173248721897296375823953)
        ·
          refine ⟨270129936541422972281867965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360173248721897296375823953 270129936541422972281867965)
          ·
            refine ⟨101298726203033614605700487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270129936541422972281867965 101298726203033614605700487)
            ·
              refine ⟨151948089304550421908550731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101298726203033614605700487 151948089304550421908550731)
              ·
                refine ⟨227922133956825632862826097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151948089304550421908550731 227922133956825632862826097)
                ·
                  refine ⟨170941600467619224647119573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227922133956825632862826097 170941600467619224647119573)
                  ·
                    refine ⟨4006443760959825577666865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 170941600467619224647119573 4006443760959825577666865)
                    ·
                      refine ⟨3004832820719869183250149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006443760959825577666865 3004832820719869183250149)
                      ·
                        rfl

theorem cell23_5851891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7, 2].length) (baseStart_5851891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851891 prefixEnd_5851891 := by exact prefixLift 5851891
  have htrace : WordTrace (prefixWord ++ tailWord_5851891) baseStart_5851891 baseEnd_5851891 := by
    simpa [prefixWord, tailWord_5851891, baseEnd_5851891] using wordTrace_append hprefix tailTrace_5851891
  have hstable : (prefixWord ++ tailWord_5851891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851891).length < 2 ^ (prefixWord ++ tailWord_5851891).sum := by decide
  have hdescent : baseEnd_5851891 < baseStart_5851891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851902 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5851902 : Nat := 118140960795 + 5851902 * 2 ^ 59
def prefixEnd_5851902 : Nat := 4983230072969 + 3 ^ 40 * 5851902 * 2
def baseEnd_5851902 : Nat := 3004838469007068640212599

theorem tailTrace_5851902 : CollatzResearch.WordTrace tailWord_5851902 prefixEnd_5851902 3004838469007068640212599 := by
  unfold tailWord_5851902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26679550055695744267299745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142290933630377302758931973 26679550055695744267299745)
  ·
    refine ⟨20009662541771808200474809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26679550055695744267299745 20009662541771808200474809)
    ·
      refine ⟨15007246906328856150356107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20009662541771808200474809 15007246906328856150356107)
      ·
        refine ⟨22510870359493284225534161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15007246906328856150356107 22510870359493284225534161)
        ·
          refine ⟨16883152769619963169150621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22510870359493284225534161 16883152769619963169150621)
          ·
            refine ⟨6331182288607486188431483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16883152769619963169150621 6331182288607486188431483)
            ·
              refine ⟨9496773432911229282647225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331182288607486188431483 9496773432911229282647225)
              ·
                refine ⟨7122580074683421961985419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9496773432911229282647225 7122580074683421961985419)
                ·
                  refine ⟨10683870112025132942978129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122580074683421961985419 10683870112025132942978129)
                  ·
                    refine ⟨8012902584018849707233597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10683870112025132942978129 8012902584018849707233597)
                    ·
                      refine ⟨3004838469007068640212599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8012902584018849707233597 3004838469007068640212599)
                      ·
                        rfl

theorem cell23_5851902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5851902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851902 prefixEnd_5851902 := by exact prefixLift 5851902
  have htrace : WordTrace (prefixWord ++ tailWord_5851902) baseStart_5851902 baseEnd_5851902 := by
    simpa [prefixWord, tailWord_5851902, baseEnd_5851902] using wordTrace_append hprefix tailTrace_5851902
  have hstable : (prefixWord ++ tailWord_5851902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851902).length < 2 ^ (prefixWord ++ tailWord_5851902).sum := by decide
  have hdescent : baseEnd_5851902 < baseStart_5851902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851933 : List Nat := [1, 4, 2, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5851933 : Nat := 118140960795 + 5851933 * 2 ^ 59
def prefixEnd_5851933 : Nat := 4983230072969 + 3 ^ 40 * 5851933 * 2
def baseEnd_5851933 : Nat := 3004854386907358018924957

theorem tailTrace_5851933 : CollatzResearch.WordTrace tailWord_5851933 prefixEnd_5851933 3004854386907358018924957 := by
  unfold tailWord_5851933
  simp only [CollatzResearch.WordTrace]
  refine ⟨213437531108453646432776453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142291687405635764288517635 213437531108453646432776453)
  ·
    refine ⟨40019537082835058706145585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213437531108453646432776453 40019537082835058706145585)
    ·
      refine ⟨30014652812126294029609189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40019537082835058706145585 30014652812126294029609189)
      ·
        refine ⟨5627747402273680130551723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30014652812126294029609189 5627747402273680130551723)
        ·
          refine ⟨8441621103410520195827585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627747402273680130551723 8441621103410520195827585)
          ·
            refine ⟨6331215827557890146870689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8441621103410520195827585 6331215827557890146870689)
            ·
              refine ⟨4748411870668417610153017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6331215827557890146870689 4748411870668417610153017)
              ·
                refine ⟨3561308903001313207614763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4748411870668417610153017 3561308903001313207614763)
                ·
                  refine ⟨5341963354501969811422145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561308903001313207614763 5341963354501969811422145)
                  ·
                    refine ⟨4006472515876477358566609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341963354501969811422145 4006472515876477358566609)
                    ·
                      refine ⟨3004854386907358018924957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006472515876477358566609 3004854386907358018924957)
                      ·
                        rfl

theorem cell23_5851933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5851933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851933 prefixEnd_5851933 := by exact prefixLift 5851933
  have htrace : WordTrace (prefixWord ++ tailWord_5851933) baseStart_5851933 baseEnd_5851933 := by
    simpa [prefixWord, tailWord_5851933, baseEnd_5851933] using wordTrace_append hprefix tailTrace_5851933
  have hstable : (prefixWord ++ tailWord_5851933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851933).length < 2 ^ (prefixWord ++ tailWord_5851933).sum := by decide
  have hdescent : baseEnd_5851933 < baseStart_5851933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851941 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_5851941 : Nat := 118140960795 + 5851941 * 2 ^ 59
def prefixEnd_5851941 : Nat := 4983230072969 + 3 ^ 40 * 5851941 * 2
def baseEnd_5851941 : Nat := 3004858494752593987624919

theorem tailTrace_5851941 : CollatzResearch.WordTrace tailWord_5851941 prefixEnd_5851941 3004858494752593987624919 := by
  unfold tailWord_5851941
  simp only [CollatzResearch.WordTrace]
  refine ⟨213437822892424663799067677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142291881928283109199378451 213437822892424663799067677)
  ·
    refine ⟨80039183584659248924650379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213437822892424663799067677 80039183584659248924650379)
    ·
      refine ⟨120058775376988873386975569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80039183584659248924650379 120058775376988873386975569)
      ·
        refine ⟨90044081532741655040231677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120058775376988873386975569 90044081532741655040231677)
        ·
          refine ⟨33766530574778120640086879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90044081532741655040231677 33766530574778120640086879)
          ·
            refine ⟨50649795862167180960130319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33766530574778120640086879 50649795862167180960130319)
            ·
              refine ⟨75974693793250771440195479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50649795862167180960130319 75974693793250771440195479)
              ·
                refine ⟨113962040689876157160293219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75974693793250771440195479 113962040689876157160293219)
                ·
                  refine ⟨170943061034814235740439829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113962040689876157160293219 170943061034814235740439829)
                  ·
                    refine ⟨8012955986006917300333117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170943061034814235740439829 8012955986006917300333117)
                    ·
                      refine ⟨3004858494752593987624919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8012955986006917300333117 3004858494752593987624919)
                      ·
                        rfl

theorem cell23_5851941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_5851941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851941 prefixEnd_5851941 := by exact prefixLift 5851941
  have htrace : WordTrace (prefixWord ++ tailWord_5851941) baseStart_5851941 baseEnd_5851941 := by
    simpa [prefixWord, tailWord_5851941, baseEnd_5851941] using wordTrace_append hprefix tailTrace_5851941
  have hstable : (prefixWord ++ tailWord_5851941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851941).length < 2 ^ (prefixWord ++ tailWord_5851941).sum := by decide
  have hdescent : baseEnd_5851941 < baseStart_5851941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851955 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 1, 4, 2]
def baseStart_5851955 : Nat := 118140960795 + 5851955 * 2 ^ 59
def prefixEnd_5851955 : Nat := 4983230072969 + 3 ^ 40 * 5851955 * 2
def baseEnd_5851955 : Nat := 3004865683481756932849855

theorem tailTrace_5851955 : CollatzResearch.WordTrace tailWord_5851955 prefixEnd_5851955 3004865683481756932849855 := by
  unfold tailWord_5851955
  simp only [CollatzResearch.WordTrace]
  refine ⟨213438333514373944190077319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142292222342915962793384879 213438333514373944190077319)
  ·
    refine ⟨320157500271560916285115979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213438333514373944190077319 320157500271560916285115979)
    ·
      refine ⟨480236250407341374427673969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320157500271560916285115979 480236250407341374427673969)
      ·
        refine ⟨360177187805506030820755477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480236250407341374427673969 360177187805506030820755477)
        ·
          refine ⟨16883305678383095194722913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 360177187805506030820755477 16883305678383095194722913)
          ·
            refine ⟨12662479258787321396042185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16883305678383095194722913 12662479258787321396042185)
            ·
              refine ⟨9496859444090491047031639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12662479258787321396042185 9496859444090491047031639)
              ·
                refine ⟨14245289166135736570547459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9496859444090491047031639 14245289166135736570547459)
                ·
                  refine ⟨21367933749203604855821189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14245289166135736570547459 21367933749203604855821189)
                  ·
                    refine ⟨4006487577975675910466473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21367933749203604855821189 4006487577975675910466473)
                    ·
                      refine ⟨3004865683481756932849855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006487577975675910466473 3004865683481756932849855)
                      ·
                        rfl

theorem cell23_5851955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4, 2].length) (baseStart_5851955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851955 prefixEnd_5851955 := by exact prefixLift 5851955
  have htrace : WordTrace (prefixWord ++ tailWord_5851955) baseStart_5851955 baseEnd_5851955 := by
    simpa [prefixWord, tailWord_5851955, baseEnd_5851955] using wordTrace_append hprefix tailTrace_5851955
  have hstable : (prefixWord ++ tailWord_5851955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851955).length < 2 ^ (prefixWord ++ tailWord_5851955).sum := by decide
  have hdescent : baseEnd_5851955 < baseStart_5851955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5851971 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 3]
def baseStart_5851971 : Nat := 118140960795 + 5851971 * 2 ^ 59
def prefixEnd_5851971 : Nat := 4983230072969 + 3 ^ 40 * 5851971 * 2
def baseEnd_5851971 : Nat := 3004873899172228870249781

theorem tailTrace_5851971 : CollatzResearch.WordTrace tailWord_5851971 prefixEnd_5851971 3004873899172228870249781 := by
  unfold tailWord_5851971
  simp only [CollatzResearch.WordTrace]
  refine ⟨213438917082315978922659767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142292611388210652615106511 213438917082315978922659767)
  ·
    refine ⟨320158375623473968383989651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213438917082315978922659767 320158375623473968383989651)
    ·
      refine ⟨480237563435210952575984477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320158375623473968383989651 480237563435210952575984477)
      ·
        refine ⟨180089086288204107215994179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480237563435210952575984477 180089086288204107215994179)
        ·
          refine ⟨270133629432306160823991269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180089086288204107215994179 270133629432306160823991269)
          ·
            refine ⟨50650055518557405154498363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270133629432306160823991269 50650055518557405154498363)
            ·
              refine ⟨75975083277836107731747545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50650055518557405154498363 75975083277836107731747545)
              ·
                refine ⟨56981312458377080798810659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75975083277836107731747545 56981312458377080798810659)
                ·
                  refine ⟨85471968687565621198215989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56981312458377080798810659 85471968687565621198215989)
                  ·
                    refine ⟨8012997064459276987332749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85471968687565621198215989 8012997064459276987332749)
                    ·
                      refine ⟨3004873899172228870249781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8012997064459276987332749 3004873899172228870249781)
                      ·
                        rfl

theorem cell23_5851971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_5851971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5851971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5851971 prefixEnd_5851971 := by exact prefixLift 5851971
  have htrace : WordTrace (prefixWord ++ tailWord_5851971) baseStart_5851971 baseEnd_5851971 := by
    simpa [prefixWord, tailWord_5851971, baseEnd_5851971] using wordTrace_append hprefix tailTrace_5851971
  have hstable : (prefixWord ++ tailWord_5851971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5851971).length < 2 ^ (prefixWord ++ tailWord_5851971).sum := by decide
  have hdescent : baseEnd_5851971 < baseStart_5851971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5851971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852011 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4]
def baseStart_5852011 : Nat := 118140960795 + 5852011 * 2 ^ 59
def prefixEnd_5852011 : Nat := 4983230072969 + 3 ^ 40 * 5852011 * 2
def baseEnd_5852011 : Nat := 3004894438398408713749597

theorem tailTrace_5852011 : CollatzResearch.WordTrace tailWord_5852011 prefixEnd_5852011 3004894438398408713749597 := by
  unfold tailWord_5852011
  simp only [CollatzResearch.WordTrace]
  refine ⟨213440376002171065754115887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142293584001447377169410591 213440376002171065754115887)
  ·
    refine ⟨320160564003256598631173831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213440376002171065754115887 320160564003256598631173831)
    ·
      refine ⟨480240846004884897946760747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320160564003256598631173831 480240846004884897946760747)
      ·
        refine ⟨720361269007327346920141121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480240846004884897946760747 720361269007327346920141121)
        ·
          refine ⟨540270951755495510190105841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 720361269007327346920141121 540270951755495510190105841)
          ·
            refine ⟨405203213816621632642579381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540270951755495510190105841 405203213816621632642579381)
            ·
              refine ⟨37987801295308278060241817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 405203213816621632642579381 37987801295308278060241817)
              ·
                refine ⟨28490850971481208545181363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37987801295308278060241817 28490850971481208545181363)
                ·
                  refine ⟨42736276457221812817772045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28490850971481208545181363 42736276457221812817772045)
                  ·
                    refine ⟨16026103671458179806664517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42736276457221812817772045 16026103671458179806664517)
                    ·
                      refine ⟨3004894438398408713749597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16026103671458179806664517 3004894438398408713749597)
                      ·
                        rfl

theorem cell23_5852011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_5852011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852011 prefixEnd_5852011 := by exact prefixLift 5852011
  have htrace : WordTrace (prefixWord ++ tailWord_5852011) baseStart_5852011 baseEnd_5852011 := by
    simpa [prefixWord, tailWord_5852011, baseEnd_5852011] using wordTrace_append hprefix tailTrace_5852011
  have hstable : (prefixWord ++ tailWord_5852011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852011).length < 2 ^ (prefixWord ++ tailWord_5852011).sum := by decide
  have hdescent : baseEnd_5852011 < baseStart_5852011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852028 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_5852028 : Nat := 118140960795 + 5852028 * 2 ^ 59
def prefixEnd_5852028 : Nat := 4983230072969 + 3 ^ 40 * 5852028 * 2
def baseEnd_5852028 : Nat := 3004903167569535147237019

theorem tailTrace_5852028 : CollatzResearch.WordTrace tailWord_5852028 prefixEnd_5852028 3004903167569535147237019 := by
  unfold tailWord_5852028
  simp only [CollatzResearch.WordTrace]
  refine ⟨106720498021554738828742369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142293997362072985104989825 106720498021554738828742369)
  ·
    refine ⟨80040373516166054121556777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106720498021554738828742369 80040373516166054121556777)
    ·
      refine ⟨60030280137124540591167583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80040373516166054121556777 60030280137124540591167583)
      ·
        refine ⟨90045420205686810886751375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60030280137124540591167583 90045420205686810886751375)
        ·
          refine ⟨135068130308530216330127063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90045420205686810886751375 135068130308530216330127063)
          ·
            refine ⟨202602195462795324495190595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135068130308530216330127063 202602195462795324495190595)
            ·
              refine ⟨303903293194192986742785893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202602195462795324495190595 303903293194192986742785893)
              ·
                refine ⟨56981867473911185014272355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303903293194192986742785893 56981867473911185014272355)
                ·
                  refine ⟨85472801210866777521408533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56981867473911185014272355 85472801210866777521408533)
                  ·
                    refine ⟨4006537556759380196316025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85472801210866777521408533 4006537556759380196316025)
                    ·
                      refine ⟨3004903167569535147237019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006537556759380196316025 3004903167569535147237019)
                      ·
                        rfl

theorem cell23_5852028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_5852028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852028 prefixEnd_5852028 := by exact prefixLift 5852028
  have htrace : WordTrace (prefixWord ++ tailWord_5852028) baseStart_5852028 baseEnd_5852028 := by
    simpa [prefixWord, tailWord_5852028, baseEnd_5852028] using wordTrace_append hprefix tailTrace_5852028
  have hstable : (prefixWord ++ tailWord_5852028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852028).length < 2 ^ (prefixWord ++ tailWord_5852028).sum := by decide
  have hdescent : baseEnd_5852028 < baseStart_5852028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852068 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 6]
def baseStart_5852068 : Nat := 118140960795 + 5852068 * 2 ^ 59
def prefixEnd_5852068 : Nat := 4983230072969 + 3 ^ 40 * 5852068 * 2
def baseEnd_5852068 : Nat := 333880411866190554526315

theorem tailTrace_5852068 : CollatzResearch.WordTrace tailWord_5852068 prefixEnd_5852068 333880411866190554526315 := by
  unfold tailWord_5852068
  simp only [CollatzResearch.WordTrace]
  refine ⟨106721227481482282244470429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142294969975309709659293905 106721227481482282244470429)
  ·
    refine ⟨40020460305555855841676411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106721227481482282244470429 40020460305555855841676411)
    ·
      refine ⟨60030690458333783762514617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40020460305555855841676411 60030690458333783762514617)
      ·
        refine ⟨45023017843750337821885963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60030690458333783762514617 45023017843750337821885963)
        ·
          refine ⟨67534526765625506732828945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45023017843750337821885963 67534526765625506732828945)
          ·
            refine ⟨50650895074219130049621709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67534526765625506732828945 50650895074219130049621709)
            ·
              refine ⟨18994085652832173768608141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50650895074219130049621709 18994085652832173768608141)
              ·
                refine ⟨7122782119812065163228053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18994085652832173768608141 7122782119812065163228053)
                ·
                  refine ⟨333880411866190554526315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7122782119812065163228053 333880411866190554526315)
                  ·
                    rfl

theorem cell23_5852068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_5852068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852068 prefixEnd_5852068 := by exact prefixLift 5852068
  have htrace : WordTrace (prefixWord ++ tailWord_5852068) baseStart_5852068 baseEnd_5852068 := by
    simpa [prefixWord, tailWord_5852068, baseEnd_5852068] using wordTrace_append hprefix tailTrace_5852068
  have hstable : (prefixWord ++ tailWord_5852068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852068).length < 2 ^ (prefixWord ++ tailWord_5852068).sum := by decide
  have hdescent : baseEnd_5852068 < baseStart_5852068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852128 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 8, 4]
def baseStart_5852128 : Nat := 118140960795 + 5852128 * 2 ^ 59
def prefixEnd_5852128 : Nat := 4983230072969 + 3 ^ 40 * 5852128 * 2
def baseEnd_5852128 : Nat := 1001651505211661585328853

theorem tailTrace_5852128 : CollatzResearch.WordTrace tailWord_5852128 prefixEnd_5852128 1001651505211661585328853 := by
  unfold tailWord_5852128
  simp only [CollatzResearch.WordTrace]
  refine ⟨106722321671373597368062519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142296428895164796490750025 106722321671373597368062519)
  ·
    refine ⟨160083482507060396052093779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106722321671373597368062519 160083482507060396052093779)
    ·
      refine ⟨240125223760590594078140669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160083482507060396052093779 240125223760590594078140669)
      ·
        refine ⟨90046958910221472779302751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240125223760590594078140669 90046958910221472779302751)
        ·
          refine ⟨135070438365332209168954127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90046958910221472779302751 135070438365332209168954127)
          ·
            refine ⟨202605657547998313753431191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135070438365332209168954127 202605657547998313753431191)
            ·
              refine ⟨303908486321997470630146787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202605657547998313753431191 303908486321997470630146787)
              ·
                refine ⟨455862729482996205945220181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303908486321997470630146787 455862729482996205945220181)
                ·
                  refine ⟨5342141361128861788420549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 455862729482996205945220181 5342141361128861788420549)
                  ·
                    refine ⟨1001651505211661585328853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5342141361128861788420549 1001651505211661585328853)
                    ·
                      rfl

theorem cell23_5852128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_5852128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852128 prefixEnd_5852128 := by exact prefixLift 5852128
  have htrace : WordTrace (prefixWord ++ tailWord_5852128) baseStart_5852128 baseEnd_5852128 := by
    simpa [prefixWord, tailWord_5852128, baseEnd_5852128] using wordTrace_append hprefix tailTrace_5852128
  have hstable : (prefixWord ++ tailWord_5852128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852128).length < 2 ^ (prefixWord ++ tailWord_5852128).sum := by decide
  have hdescent : baseEnd_5852128 < baseStart_5852128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852135 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5852135 : Nat := 118140960795 + 5852135 * 2 ^ 59
def prefixEnd_5852135 : Nat := 4983230072969 + 3 ^ 40 * 5852135 * 2
def baseEnd_5852135 : Nat := 3004958109999566228599027

theorem tailTrace_5852135 : CollatzResearch.WordTrace tailWord_5852135 prefixEnd_5852135 3004958109999566228599027 := by
  unfold tailWord_5852135
  simp only [CollatzResearch.WordTrace]
  refine ⟨213444898653721834931629859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142296599102481223287753239 213444898653721834931629859)
  ·
    refine ⟨320167347980582752397444789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213444898653721834931629859 320167347980582752397444789)
    ·
      refine ⟨30015688873179633037260449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320167347980582752397444789 30015688873179633037260449)
      ·
        refine ⟨22511766654884724777945337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30015688873179633037260449 22511766654884724777945337)
        ·
          refine ⟨16883824991163543583459003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22511766654884724777945337 16883824991163543583459003)
          ·
            refine ⟨25325737486745315375188505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16883824991163543583459003 25325737486745315375188505)
            ·
              refine ⟨18994303115058986531391379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25325737486745315375188505 18994303115058986531391379)
              ·
                refine ⟨28491454672588479797087069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18994303115058986531391379 28491454672588479797087069)
                ·
                  refine ⟨10684295502220679923907651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28491454672588479797087069 10684295502220679923907651)
                  ·
                    refine ⟨16026443253331019885861477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10684295502220679923907651 16026443253331019885861477)
                    ·
                      refine ⟨3004958109999566228599027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16026443253331019885861477 3004958109999566228599027)
                      ·
                        rfl

theorem cell23_5852135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5852135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852135 prefixEnd_5852135 := by exact prefixLift 5852135
  have htrace : WordTrace (prefixWord ++ tailWord_5852135) baseStart_5852135 baseEnd_5852135 := by
    simpa [prefixWord, tailWord_5852135, baseEnd_5852135] using wordTrace_append hprefix tailTrace_5852135
  have hstable : (prefixWord ++ tailWord_5852135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852135).length < 2 ^ (prefixWord ++ tailWord_5852135).sum := by decide
  have hdescent : baseEnd_5852135 < baseStart_5852135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852149 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_5852149 : Nat := 118140960795 + 5852149 * 2 ^ 59
def prefixEnd_5852149 : Nat := 4983230072969 + 3 ^ 40 * 5852149 * 2
def baseEnd_5852149 : Nat := 1001655099576243057941321

theorem tailTrace_5852149 : CollatzResearch.WordTrace tailWord_5852149 prefixEnd_5852149 1001655099576243057941321 := by
  unfold tailWord_5852149
  simp only [CollatzResearch.WordTrace]
  refine ⟨213445409275671115322639501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142296939517114076881759667 213445409275671115322639501)
  ·
    refine ⟨80042028478376668245989813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213445409275671115322639501 80042028478376668245989813)
    ·
      refine ⟨7503940169847812648061545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80042028478376668245989813 7503940169847812648061545)
      ·
        refine ⟨5627955127385859486046159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7503940169847812648061545 5627955127385859486046159)
        ·
          refine ⟨8441932691078789229069239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627955127385859486046159 8441932691078789229069239)
          ·
            refine ⟨12662899036618183843603859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441932691078789229069239 12662899036618183843603859)
            ·
              refine ⟨18994348554927275765405789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12662899036618183843603859 18994348554927275765405789)
              ·
                refine ⟨7122880708097728412027171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18994348554927275765405789 7122880708097728412027171)
                ·
                  refine ⟨10684321062146592618040757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122880708097728412027171 10684321062146592618040757)
                  ·
                    refine ⟨1001655099576243057941321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10684321062146592618040757 1001655099576243057941321)
                    ·
                      rfl

theorem cell23_5852149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_5852149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852149 prefixEnd_5852149 := by exact prefixLift 5852149
  have htrace : WordTrace (prefixWord ++ tailWord_5852149) baseStart_5852149 baseEnd_5852149 := by
    simpa [prefixWord, tailWord_5852149, baseEnd_5852149] using wordTrace_append hprefix tailTrace_5852149
  have hstable : (prefixWord ++ tailWord_5852149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852149).length < 2 ^ (prefixWord ++ tailWord_5852149).sum := by decide
  have hdescent : baseEnd_5852149 < baseStart_5852149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852185 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 3]
def baseStart_5852185 : Nat := 118140960795 + 5852185 * 2 ^ 59
def prefixEnd_5852185 : Nat := 4983230072969 + 3 ^ 40 * 5852185 * 2
def baseEnd_5852185 : Nat := 3004983784032291032973797

theorem tailTrace_5852185 : CollatzResearch.WordTrace tailWord_5852185 prefixEnd_5852185 3004983784032291032973797 := by
  unfold tailWord_5852185
  simp only [CollatzResearch.WordTrace]
  refine ⟨213446722303540693470950009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142297814869027128980633339 213446722303540693470950009)
  ·
    refine ⟨160085041727655520103212507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213446722303540693470950009 160085041727655520103212507)
    ·
      refine ⟨240127562591483280154818761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160085041727655520103212507 240127562591483280154818761)
      ·
        refine ⟨180095671943612460116114071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240127562591483280154818761 180095671943612460116114071)
        ·
          refine ⟨270143507915418690174171107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180095671943612460116114071 270143507915418690174171107)
          ·
            refine ⟨405215261873128035261256661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270143507915418690174171107 405215261873128035261256661)
            ·
              refine ⟨9497232700151438326435703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 405215261873128035261256661 9497232700151438326435703)
              ·
                refine ⟨14245849050227157489653555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9497232700151438326435703 14245849050227157489653555)
                ·
                  refine ⟨21368773575340736234480333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14245849050227157489653555 21368773575340736234480333)
                  ·
                    refine ⟨8013290090752776087930125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21368773575340736234480333 8013290090752776087930125)
                    ·
                      refine ⟨3004983784032291032973797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8013290090752776087930125 3004983784032291032973797)
                      ·
                        rfl

theorem cell23_5852185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_5852185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852185 prefixEnd_5852185 := by exact prefixLift 5852185
  have htrace : WordTrace (prefixWord ++ tailWord_5852185) baseStart_5852185 baseEnd_5852185 := by
    simpa [prefixWord, tailWord_5852185, baseEnd_5852185] using wordTrace_append hprefix tailTrace_5852185
  have hstable : (prefixWord ++ tailWord_5852185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852185).length < 2 ^ (prefixWord ++ tailWord_5852185).sum := by decide
  have hdescent : baseEnd_5852185 < baseStart_5852185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852189 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_5852189 : Nat := 118140960795 + 5852189 * 2 ^ 59
def prefixEnd_5852189 : Nat := 4983230072969 + 3 ^ 40 * 5852189 * 2
def baseEnd_5852189 : Nat := 3004985837954909017323779

theorem tailTrace_5852189 : CollatzResearch.WordTrace tailWord_5852189 prefixEnd_5852189 3004985837954909017323779 := by
  unfold tailWord_5852189
  simp only [CollatzResearch.WordTrace]
  refine ⟨213446868195526202154095621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142297912130350801436063747 213446868195526202154095621)
  ·
    refine ⟨40021287786661162903892929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213446868195526202154095621 40021287786661162903892929)
    ·
      refine ⟨30015965839995872177919697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40021287786661162903892929 30015965839995872177919697)
      ·
        refine ⟨22511974379996904133439773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30015965839995872177919697 22511974379996904133439773)
        ·
          refine ⟨8441990392498839050039915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22511974379996904133439773 8441990392498839050039915)
          ·
            refine ⟨12662985588748258575059873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441990392498839050039915 12662985588748258575059873)
            ·
              refine ⟨9497239191561193931294905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12662985588748258575059873 9497239191561193931294905)
              ·
                refine ⟨7122929393670895448471179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9497239191561193931294905 7122929393670895448471179)
                ·
                  refine ⟨10684394090506343172706769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122929393670895448471179 10684394090506343172706769)
                  ·
                    refine ⟨8013295567879757379530077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10684394090506343172706769 8013295567879757379530077)
                    ·
                      refine ⟨3004985837954909017323779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8013295567879757379530077 3004985837954909017323779)
                      ·
                        rfl

theorem cell23_5852189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_5852189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852189 prefixEnd_5852189 := by exact prefixLift 5852189
  have htrace : WordTrace (prefixWord ++ tailWord_5852189) baseStart_5852189 baseEnd_5852189 := by
    simpa [prefixWord, tailWord_5852189, baseEnd_5852189] using wordTrace_append hprefix tailTrace_5852189
  have hstable : (prefixWord ++ tailWord_5852189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852189).length < 2 ^ (prefixWord ++ tailWord_5852189).sum := by decide
  have hdescent : baseEnd_5852189 < baseStart_5852189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852218 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_5852218 : Nat := 118140960795 + 5852218 * 2 ^ 59
def prefixEnd_5852218 : Nat := 4983230072969 + 3 ^ 40 * 5852218 * 2
def baseEnd_5852218 : Nat := 1001666909631296467953715

theorem tailTrace_5852218 : CollatzResearch.WordTrace tailWord_5852218 prefixEnd_5852218 1001666909631296467953715 := by
  unfold tailWord_5852218
  simp only [CollatzResearch.WordTrace]
  refine ⟨53361981478105285026725327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142298617274947426737934205 53361981478105285026725327)
  ·
    refine ⟨80042972217157927540087991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53361981478105285026725327 80042972217157927540087991)
    ·
      refine ⟨120064458325736891310131987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80042972217157927540087991 120064458325736891310131987)
      ·
        refine ⟨180096687488605336965197981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120064458325736891310131987 180096687488605336965197981)
        ·
          refine ⟨67536257808227001361949243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180096687488605336965197981 67536257808227001361949243)
          ·
            refine ⟨101304386712340502042923865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67536257808227001361949243 101304386712340502042923865)
            ·
              refine ⟨75978290034255376532192899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101304386712340502042923865 75978290034255376532192899)
              ·
                refine ⟨113967435051383064798289349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75978290034255376532192899 113967435051383064798289349)
                ·
                  refine ⟨21368894072134324649679253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113967435051383064798289349 21368894072134324649679253)
                  ·
                    refine ⟨1001666909631296467953715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21368894072134324649679253 1001666909631296467953715)
                    ·
                      rfl

theorem cell23_5852218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_5852218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852218 prefixEnd_5852218 := by exact prefixLift 5852218
  have htrace : WordTrace (prefixWord ++ tailWord_5852218) baseStart_5852218 baseEnd_5852218 := by
    simpa [prefixWord, tailWord_5852218, baseEnd_5852218] using wordTrace_append hprefix tailTrace_5852218
  have hstable : (prefixWord ++ tailWord_5852218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852218).length < 2 ^ (prefixWord ++ tailWord_5852218).sum := by decide
  have hdescent : baseEnd_5852218 < baseStart_5852218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852248 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 9]
def baseStart_5852248 : Nat := 118140960795 + 5852248 * 2 ^ 59
def prefixEnd_5852248 : Nat := 4983230072969 + 3 ^ 40 * 5852248 * 2
def baseEnd_5852248 : Nat := 333890681479280476276223

theorem tailTrace_5852248 : CollatzResearch.WordTrace tailWord_5852248 prefixEnd_5852248 333890681479280476276223 := by
  unfold tailWord_5852248
  simp only [CollatzResearch.WordTrace]
  refine ⟨106724510051156227615246699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142299346734874970153662265 106724510051156227615246699)
  ·
    refine ⟨160086765076734341422870049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106724510051156227615246699 160086765076734341422870049)
    ·
      refine ⟨120065073807550756067152537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160086765076734341422870049 120065073807550756067152537)
      ·
        refine ⟨90048805355663067050364403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120065073807550756067152537 90048805355663067050364403)
        ·
          refine ⟨135073208033494600575546605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90048805355663067050364403 135073208033494600575546605)
          ·
            refine ⟨50652453012560475215829977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135073208033494600575546605 50652453012560475215829977)
            ·
              refine ⟨37989339759420356411872483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50652453012560475215829977 37989339759420356411872483)
              ·
                refine ⟨56984009639130534617808725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37989339759420356411872483 56984009639130534617808725)
                ·
                  refine ⟨333890681479280476276223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56984009639130534617808725 333890681479280476276223)
                  ·
                    rfl

theorem cell23_5852248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 9].length) (baseStart_5852248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852248 prefixEnd_5852248 := by exact prefixLift 5852248
  have htrace : WordTrace (prefixWord ++ tailWord_5852248) baseStart_5852248 baseEnd_5852248 := by
    simpa [prefixWord, tailWord_5852248, baseEnd_5852248] using wordTrace_append hprefix tailTrace_5852248
  have hstable : (prefixWord ++ tailWord_5852248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852248).length < 2 ^ (prefixWord ++ tailWord_5852248).sum := by decide
  have hdescent : baseEnd_5852248 < baseStart_5852248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852286 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5852286 : Nat := 118140960795 + 5852286 * 2 ^ 59
def prefixEnd_5852286 : Nat := 4983230072969 + 3 ^ 40 * 5852286 * 2
def baseEnd_5852286 : Nat := 1001678548526131712603611

theorem tailTrace_5852286 : CollatzResearch.WordTrace tailWord_5852286 prefixEnd_5852286 1001678548526131712603611 := by
  unfold tailWord_5852286
  simp only [CollatzResearch.WordTrace]
  refine ⟨26681300759521848465047089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142300270717449858480251141 26681300759521848465047089)
  ·
    refine ⟨20010975569641386348785317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26681300759521848465047089 20010975569641386348785317)
    ·
      refine ⟨3752057919307759940397247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20010975569641386348785317 3752057919307759940397247)
      ·
        refine ⟨5628086878961639910595871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752057919307759940397247 5628086878961639910595871)
        ·
          refine ⟨8442130318442459865893807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628086878961639910595871 8442130318442459865893807)
          ·
            refine ⟨12663195477663689798840711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8442130318442459865893807 12663195477663689798840711)
            ·
              refine ⟨18994793216495534698261067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12663195477663689798840711 18994793216495534698261067)
              ·
                refine ⟨28492189824743302047391601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18994793216495534698261067 28492189824743302047391601)
                ·
                  refine ⟨21369142368557476535543701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28492189824743302047391601 21369142368557476535543701)
                  ·
                    refine ⟨1001678548526131712603611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21369142368557476535543701 1001678548526131712603611)
                    ·
                      rfl

theorem cell23_5852286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5852286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852286 prefixEnd_5852286 := by exact prefixLift 5852286
  have htrace : WordTrace (prefixWord ++ tailWord_5852286) baseStart_5852286 baseEnd_5852286 := by
    simpa [prefixWord, tailWord_5852286, baseEnd_5852286] using wordTrace_append hprefix tailTrace_5852286
  have hstable : (prefixWord ++ tailWord_5852286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852286).length < 2 ^ (prefixWord ++ tailWord_5852286).sum := by decide
  have hdescent : baseEnd_5852286 < baseStart_5852286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852292 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_5852292 : Nat := 118140960795 + 5852292 * 2 ^ 59
def prefixEnd_5852292 : Nat := 4983230072969 + 3 ^ 40 * 5852292 * 2
def baseEnd_5852292 : Nat := 3005038726462322114335805

theorem tailTrace_5852292 : CollatzResearch.WordTrace tailWord_5852292 prefixEnd_5852292 3005038726462322114335805 := by
  unfold tailWord_5852292
  simp only [CollatzResearch.WordTrace]
  refine ⟨106725312457076525372547565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142300416609435367163396753 106725312457076525372547565)
  ·
    refine ⟨40021992171403697014705337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106725312457076525372547565 40021992171403697014705337)
    ·
      refine ⟨30016494128552772761029003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40021992171403697014705337 30016494128552772761029003)
      ·
        refine ⟨45024741192829159141543505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30016494128552772761029003 45024741192829159141543505)
        ·
          refine ⟨33768555894621869356157629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45024741192829159141543505 33768555894621869356157629)
          ·
            refine ⟨12663208460483201008559111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33768555894621869356157629 12663208460483201008559111)
            ·
              refine ⟨18994812690724801512838667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12663208460483201008559111 18994812690724801512838667)
              ·
                refine ⟨28492219036087202269258001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18994812690724801512838667 28492219036087202269258001)
                ·
                  refine ⟨21369164277065401701943501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28492219036087202269258001 21369164277065401701943501)
                  ·
                    refine ⟨8013436603899525638228813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21369164277065401701943501 8013436603899525638228813)
                    ·
                      refine ⟨3005038726462322114335805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8013436603899525638228813 3005038726462322114335805)
                      ·
                        rfl

theorem cell23_5852292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_5852292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852292 prefixEnd_5852292 := by exact prefixLift 5852292
  have htrace : WordTrace (prefixWord ++ tailWord_5852292) baseStart_5852292 baseEnd_5852292 := by
    simpa [prefixWord, tailWord_5852292, baseEnd_5852292] using wordTrace_append hprefix tailTrace_5852292
  have hstable : (prefixWord ++ tailWord_5852292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852292).length < 2 ^ (prefixWord ++ tailWord_5852292).sum := by decide
  have hdescent : baseEnd_5852292 < baseStart_5852292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852312 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 2, 5]
def baseStart_5852312 : Nat := 118140960795 + 5852312 * 2 ^ 59
def prefixEnd_5852312 : Nat := 4983230072969 + 3 ^ 40 * 5852312 * 2
def baseEnd_5852312 : Nat := 1001682998691804012028571

theorem tailTrace_5852312 : CollatzResearch.WordTrace tailWord_5852312 prefixEnd_5852312 1001682998691804012028571 := by
  unfold tailWord_5852312
  simp only [CollatzResearch.WordTrace]
  refine ⟨106725677187040297080411595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142300902916053729440548793 106725677187040297080411595)
  ·
    refine ⟨160088515780560445620617393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106725677187040297080411595 160088515780560445620617393)
    ·
      refine ⟨120066386835420334215463045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160088515780560445620617393 120066386835420334215463045)
      ·
        refine ⟨22512447531641312665399321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120066386835420334215463045 22512447531641312665399321)
        ·
          refine ⟨16884335648730984499049491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22512447531641312665399321 16884335648730984499049491)
          ·
            refine ⟨25326503473096476748574237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16884335648730984499049491 25326503473096476748574237)
            ·
              refine ⟨9497438802411178780715339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25326503473096476748574237 9497438802411178780715339)
              ·
                refine ⟨14246158203616768171073009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9497438802411178780715339 14246158203616768171073009)
                ·
                  refine ⟨10684618652712576128304757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14246158203616768171073009 10684618652712576128304757)
                  ·
                    refine ⟨1001682998691804012028571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10684618652712576128304757 1001682998691804012028571)
                    ·
                      rfl

theorem cell23_5852312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_5852312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852312 prefixEnd_5852312 := by exact prefixLift 5852312
  have htrace : WordTrace (prefixWord ++ tailWord_5852312) baseStart_5852312 baseEnd_5852312 := by
    simpa [prefixWord, tailWord_5852312, baseEnd_5852312] using wordTrace_append hprefix tailTrace_5852312
  have hstable : (prefixWord ++ tailWord_5852312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852312).length < 2 ^ (prefixWord ++ tailWord_5852312).sum := by decide
  have hdescent : baseEnd_5852312 < baseStart_5852312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852419 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 1, 5]
def baseStart_5852419 : Nat := 118140960795 + 5852419 * 2 ^ 59
def prefixEnd_5852419 : Nat := 4983230072969 + 3 ^ 40 * 5852419 * 2
def baseEnd_5852419 : Nat := 1001701312835147705815907

theorem tailTrace_5852419 : CollatzResearch.WordTrace tailWord_5852419 prefixEnd_5852419 1001701312835147705815907 := by
  unfold tailWord_5852419
  simp only [CollatzResearch.WordTrace]
  refine ⟨213455256984692951434968311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142303504656461967623312207 213455256984692951434968311)
  ·
    refine ⟨320182885477039427152452467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213455256984692951434968311 320182885477039427152452467)
    ·
      refine ⟨480274328215559140728678701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320182885477039427152452467 480274328215559140728678701)
      ·
        refine ⟨180102873080834677773254513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480274328215559140728678701 180102873080834677773254513)
        ·
          refine ⟨135077154810626008329940885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180102873080834677773254513 135077154810626008329940885)
          ·
            refine ⟨6331741631748094140465979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135077154810626008329940885 6331741631748094140465979)
            ·
              refine ⟨9497612447622141210698969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331741631748094140465979 9497612447622141210698969)
              ·
                refine ⟨7123209335716605908024227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9497612447622141210698969 7123209335716605908024227)
                ·
                  refine ⟨10684814003574908862036341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7123209335716605908024227 10684814003574908862036341)
                  ·
                    refine ⟨1001701312835147705815907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10684814003574908862036341 1001701312835147705815907)
                    ·
                      rfl

theorem cell23_5852419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 5].length) (baseStart_5852419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852419 prefixEnd_5852419 := by exact prefixLift 5852419
  have htrace : WordTrace (prefixWord ++ tailWord_5852419) baseStart_5852419 baseEnd_5852419 := by
    simpa [prefixWord, tailWord_5852419, baseEnd_5852419] using wordTrace_append hprefix tailTrace_5852419
  have hstable : (prefixWord ++ tailWord_5852419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852419).length < 2 ^ (prefixWord ++ tailWord_5852419).sum := by decide
  have hdescent : baseEnd_5852419 < baseStart_5852419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852452 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_5852452 : Nat := 118140960795 + 5852452 * 2 ^ 59
def prefixEnd_5852452 : Nat := 4983230072969 + 3 ^ 40 * 5852452 * 2
def baseEnd_5852452 : Nat := 3005120883367041488335069

theorem tailTrace_5852452 : CollatzResearch.WordTrace tailWord_5852452 prefixEnd_5852452 3005120883367041488335069 := by
  unfold tailWord_5852452
  simp only [CollatzResearch.WordTrace]
  refine ⟨106728230296786699035459805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142304307062382265380613073 106728230296786699035459805)
  ·
    refine ⟨40023086361295012138297427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106728230296786699035459805 40023086361295012138297427)
    ·
      refine ⟨60034629541942518207446141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40023086361295012138297427 60034629541942518207446141)
      ·
        refine ⟨22512986078228444327792303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60034629541942518207446141 22512986078228444327792303)
        ·
          refine ⟨33769479117342666491688455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22512986078228444327792303 33769479117342666491688455)
          ·
            refine ⟨50654218676013999737532683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33769479117342666491688455 50654218676013999737532683)
            ·
              refine ⟨75981328014020999606299025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50654218676013999737532683 75981328014020999606299025)
              ·
                refine ⟨56985996010515749704724269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75981328014020999606299025 56985996010515749704724269)
                ·
                  refine ⟨21369748503943406139271601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56985996010515749704724269 21369748503943406139271601)
                  ·
                    refine ⟨16027311377957554604453701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21369748503943406139271601 16027311377957554604453701)
                    ·
                      refine ⟨3005120883367041488335069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16027311377957554604453701 3005120883367041488335069)
                      ·
                        rfl

theorem cell23_5852452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_5852452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852452 prefixEnd_5852452 := by exact prefixLift 5852452
  have htrace : WordTrace (prefixWord ++ tailWord_5852452) baseStart_5852452 baseEnd_5852452 := by
    simpa [prefixWord, tailWord_5852452, baseEnd_5852452] using wordTrace_append hprefix tailTrace_5852452
  have hstable : (prefixWord ++ tailWord_5852452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852452).length < 2 ^ (prefixWord ++ tailWord_5852452).sum := by decide
  have hdescent : baseEnd_5852452 < baseStart_5852452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852469 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_5852469 : Nat := 118140960795 + 5852469 * 2 ^ 59
def prefixEnd_5852469 : Nat := 4983230072969 + 3 ^ 40 * 5852469 * 2
def baseEnd_5852469 : Nat := 3005129612538167921822491

theorem tailTrace_5852469 : CollatzResearch.WordTrace tailWord_5852469 prefixEnd_5852469 3005129612538167921822491 := by
  unfold tailWord_5852469
  simp only [CollatzResearch.WordTrace]
  refine ⟨213457080634511809974288461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142304720423007873316192307 213457080634511809974288461)
  ·
    refine ⟨80046405237941928740358173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213457080634511809974288461 80046405237941928740358173)
    ·
      refine ⟨30017401964228223277634315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80046405237941928740358173 30017401964228223277634315)
      ·
        refine ⟨45026102946342334916451473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30017401964228223277634315 45026102946342334916451473)
        ·
          refine ⟨33769577209756751187338605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45026102946342334916451473 33769577209756751187338605)
          ·
            refine ⟨12663591453658781695251977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33769577209756751187338605 12663591453658781695251977)
            ·
              refine ⟨9497693590244086271438983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12663591453658781695251977 9497693590244086271438983)
              ·
                refine ⟨14246540385366129407158475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9497693590244086271438983 14246540385366129407158475)
                ·
                  refine ⟨21369810578049194110737713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14246540385366129407158475 21369810578049194110737713)
                  ·
                    refine ⟨16027357933536895583053285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21369810578049194110737713 16027357933536895583053285)
                    ·
                      refine ⟨3005129612538167921822491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16027357933536895583053285 3005129612538167921822491)
                      ·
                        rfl

theorem cell23_5852469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_5852469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852469 prefixEnd_5852469 := by exact prefixLift 5852469
  have htrace : WordTrace (prefixWord ++ tailWord_5852469) baseStart_5852469 baseEnd_5852469 := by
    simpa [prefixWord, tailWord_5852469, baseEnd_5852469] using wordTrace_append hprefix tailTrace_5852469
  have hstable : (prefixWord ++ tailWord_5852469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852469).length < 2 ^ (prefixWord ++ tailWord_5852469).sum := by decide
  have hdescent : baseEnd_5852469 < baseStart_5852469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852473 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5852473 : Nat := 118140960795 + 5852473 * 2 ^ 59
def prefixEnd_5852473 : Nat := 4983230072969 + 3 ^ 40 * 5852473 * 2
def baseEnd_5852473 : Nat := 3005131666460785906172473

theorem tailTrace_5852473 : CollatzResearch.WordTrace tailWord_5852473 prefixEnd_5852473 3005131666460785906172473 := by
  unfold tailWord_5852473
  simp only [CollatzResearch.WordTrace]
  refine ⟨213457226526497318657434073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142304817684331545771622715 213457226526497318657434073)
  ·
    refine ⟨160092919894872988993075555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213457226526497318657434073 160092919894872988993075555)
    ·
      refine ⟨240139379842309483489613333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160092919894872988993075555 240139379842309483489613333)
      ·
        refine ⟨11256533430108257038575625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 240139379842309483489613333 11256533430108257038575625)
        ·
          refine ⟨8442400072581192778931719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11256533430108257038575625 8442400072581192778931719)
          ·
            refine ⟨12663600108871789168397579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8442400072581192778931719 12663600108871789168397579)
            ·
              refine ⟨18995400163307683752596369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12663600108871789168397579 18995400163307683752596369)
              ·
                refine ⟨14246550122480762814447277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18995400163307683752596369 14246550122480762814447277)
                ·
                  refine ⟨5342456295930286055417729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14246550122480762814447277 5342456295930286055417729)
                  ·
                    refine ⟨4006842221947714541563297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5342456295930286055417729 4006842221947714541563297)
                    ·
                      refine ⟨3005131666460785906172473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4006842221947714541563297 3005131666460785906172473)
                      ·
                        rfl

theorem cell23_5852473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5852473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852473 prefixEnd_5852473 := by exact prefixLift 5852473
  have htrace : WordTrace (prefixWord ++ tailWord_5852473) baseStart_5852473 baseEnd_5852473 := by
    simpa [prefixWord, tailWord_5852473, baseEnd_5852473] using wordTrace_append hprefix tailTrace_5852473
  have hstable : (prefixWord ++ tailWord_5852473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852473).length < 2 ^ (prefixWord ++ tailWord_5852473).sum := by decide
  have hdescent : baseEnd_5852473 < baseStart_5852473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852506 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_5852506 : Nat := 118140960795 + 5852506 * 2 ^ 59
def prefixEnd_5852506 : Nat := 4983230072969 + 3 ^ 40 * 5852506 * 2
def baseEnd_5852506 : Nat := 3005148611322384277059821

theorem tailTrace_5852506 : CollatzResearch.WordTrace tailWord_5852506 prefixEnd_5852506 3005148611322384277059821 := by
  unfold tailWord_5852506
  simp only [CollatzResearch.WordTrace]
  refine ⟨53364607533844441323346343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142305620090251843528923581 53364607533844441323346343)
  ·
    refine ⟨80046911300766661985019515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53364607533844441323346343 80046911300766661985019515)
    ·
      refine ⟨120070366951149992977529273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80046911300766661985019515 120070366951149992977529273)
      ·
        refine ⟨90052775213362494733146955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120070366951149992977529273 90052775213362494733146955)
        ·
          refine ⟨135079162820043742099720433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90052775213362494733146955 135079162820043742099720433)
          ·
            refine ⟨101309372115032806574790325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135079162820043742099720433 101309372115032806574790325)
            ·
              refine ⟨9497753635784325616386593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101309372115032806574790325 9497753635784325616386593)
              ·
                refine ⟨7123315226838244212289945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9497753635784325616386593 7123315226838244212289945)
                ·
                  refine ⟨5342486420128683159217459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7123315226838244212289945 5342486420128683159217459)
                  ·
                    refine ⟨8013729630193024738826189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5342486420128683159217459 8013729630193024738826189)
                    ·
                      refine ⟨3005148611322384277059821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8013729630193024738826189 3005148611322384277059821)
                      ·
                        rfl

theorem cell23_5852506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_5852506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852506 prefixEnd_5852506 := by exact prefixLift 5852506
  have htrace : WordTrace (prefixWord ++ tailWord_5852506) baseStart_5852506 baseEnd_5852506 := by
    simpa [prefixWord, tailWord_5852506, baseEnd_5852506] using wordTrace_append hprefix tailTrace_5852506
  have hstable : (prefixWord ++ tailWord_5852506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852506).length < 2 ^ (prefixWord ++ tailWord_5852506).sum := by decide
  have hdescent : baseEnd_5852506 < baseStart_5852506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852569 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 7]
def baseStart_5852569 : Nat := 118140960795 + 5852569 * 2 ^ 59
def prefixEnd_5852569 : Nat := 4983230072969 + 3 ^ 40 * 5852569 * 2
def baseEnd_5852569 : Nat := 333908995622624170063559

theorem tailTrace_5852569 : CollatzResearch.WordTrace tailWord_5852569 prefixEnd_5852569 333908995622624170063559 := by
  unfold tailWord_5852569
  simp only [CollatzResearch.WordTrace]
  refine ⟨213460727934149527052928761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142307151956099684701952507 213460727934149527052928761)
  ·
    refine ⟨160095545950612145289696571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213460727934149527052928761 160095545950612145289696571)
    ·
      refine ⟨240143318925918217934544857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160095545950612145289696571 240143318925918217934544857)
      ·
        refine ⟨180107489194438663450908643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240143318925918217934544857 180107489194438663450908643)
        ·
          refine ⟨270161233791657995176362965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180107489194438663450908643 270161233791657995176362965)
          ·
            refine ⟨6331903916991984261946007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 270161233791657995176362965 6331903916991984261946007)
            ·
              refine ⟨9497855875487976392919011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331903916991984261946007 9497855875487976392919011)
              ·
                refine ⟨14246783813231964589378517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9497855875487976392919011 14246783813231964589378517)
                ·
                  refine ⟨333908995622624170063559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14246783813231964589378517 333908995622624170063559)
                  ·
                    rfl

theorem cell23_5852569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 7].length) (baseStart_5852569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852569 prefixEnd_5852569 := by exact prefixLift 5852569
  have htrace : WordTrace (prefixWord ++ tailWord_5852569) baseStart_5852569 baseEnd_5852569 := by
    simpa [prefixWord, tailWord_5852569, baseEnd_5852569] using wordTrace_append hprefix tailTrace_5852569
  have hstable : (prefixWord ++ tailWord_5852569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852569).length < 2 ^ (prefixWord ++ tailWord_5852569).sum := by decide
  have hdescent : baseEnd_5852569 < baseStart_5852569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852574 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5852574 : Nat := 118140960795 + 5852574 * 2 ^ 59
def prefixEnd_5852574 : Nat := 4983230072969 + 3 ^ 40 * 5852574 * 2
def baseEnd_5852574 : Nat := 3005183528006890011009509

theorem tailTrace_5852574 : CollatzResearch.WordTrace tailWord_5852574 prefixEnd_5852574 3005183528006890011009509 := by
  unfold tailWord_5852574
  simp only [CollatzResearch.WordTrace]
  refine ⟨26682613787391426613357597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142307273532754275271240517 26682613787391426613357597)
  ·
    refine ⟨10005980170271784980009099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26682613787391426613357597 10005980170271784980009099)
    ·
      refine ⟨15008970255407677470013649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10005980170271784980009099 15008970255407677470013649)
      ·
        refine ⟨11256727691555758102510237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15008970255407677470013649 11256727691555758102510237)
        ·
          refine ⟨4221272884333409288441339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11256727691555758102510237 4221272884333409288441339)
          ·
            refine ⟨6331909326500113932662009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221272884333409288441339 6331909326500113932662009)
            ·
              refine ⟨4748931994875085449496507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6331909326500113932662009 4748931994875085449496507)
              ·
                refine ⟨7123397992312628174244761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4748931994875085449496507 7123397992312628174244761)
                ·
                  refine ⟨5342548494234471130683571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7123397992312628174244761 5342548494234471130683571)
                  ·
                    refine ⟨8013822741351706696025357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5342548494234471130683571 8013822741351706696025357)
                    ·
                      refine ⟨3005183528006890011009509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8013822741351706696025357 3005183528006890011009509)
                      ·
                        rfl

theorem cell23_5852574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5852574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852574 prefixEnd_5852574 := by exact prefixLift 5852574
  have htrace : WordTrace (prefixWord ++ tailWord_5852574) baseStart_5852574 baseEnd_5852574 := by
    simpa [prefixWord, tailWord_5852574, baseEnd_5852574] using wordTrace_append hprefix tailTrace_5852574
  have hstable : (prefixWord ++ tailWord_5852574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852574).length < 2 ^ (prefixWord ++ tailWord_5852574).sum := by decide
  have hdescent : baseEnd_5852574 < baseStart_5852574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852599 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 2, 5]
def baseStart_5852599 : Nat := 118140960795 + 5852599 * 2 ^ 59
def prefixEnd_5852599 : Nat := 4983230072969 + 3 ^ 40 * 5852599 * 2
def baseEnd_5852599 : Nat := 1001732121674417471065631

theorem tailTrace_5852599 : CollatzResearch.WordTrace tailWord_5852599 prefixEnd_5852599 1001732121674417471065631 := by
  unfold tailWord_5852599
  simp only [CollatzResearch.WordTrace]
  refine ⟨213461822124040842176520851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142307881416027228117680567 213461822124040842176520851)
  ·
    refine ⟨320192733186061263264781277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213461822124040842176520851 320192733186061263264781277)
    ·
      refine ⟨120072274944772973724292979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320192733186061263264781277 120072274944772973724292979)
      ·
        refine ⟨180108412417159460586439469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120072274944772973724292979 180108412417159460586439469)
        ·
          refine ⟨67540654656434797719914801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180108412417159460586439469 67540654656434797719914801)
          ·
            refine ⟨50655490992326098289936101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67540654656434797719914801 50655490992326098289936101)
            ·
              refine ⟨9497904561061143429363019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50655490992326098289936101 9497904561061143429363019)
              ·
                refine ⟨14246856841591715144044529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9497904561061143429363019 14246856841591715144044529)
                ·
                  refine ⟨10685142631193786358033397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14246856841591715144044529 10685142631193786358033397)
                  ·
                    refine ⟨1001732121674417471065631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10685142631193786358033397 1001732121674417471065631)
                    ·
                      rfl

theorem cell23_5852599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_5852599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852599 prefixEnd_5852599 := by exact prefixLift 5852599
  have htrace : WordTrace (prefixWord ++ tailWord_5852599) baseStart_5852599 baseEnd_5852599 := by
    simpa [prefixWord, tailWord_5852599, baseEnd_5852599] using wordTrace_append hprefix tailTrace_5852599
  have hstable : (prefixWord ++ tailWord_5852599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852599).length < 2 ^ (prefixWord ++ tailWord_5852599).sum := by decide
  have hdescent : baseEnd_5852599 < baseStart_5852599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852619 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 4]
def baseStart_5852619 : Nat := 118140960795 + 5852619 * 2 ^ 59
def prefixEnd_5852619 : Nat := 4983230072969 + 3 ^ 40 * 5852619 * 2
def baseEnd_5852619 : Nat := 3005206634636342334946801

theorem tailTrace_5852619 : CollatzResearch.WordTrace tailWord_5852619 prefixEnd_5852619 3005206634636342334946801 := by
  unfold tailWord_5852619
  simp only [CollatzResearch.WordTrace]
  refine ⟨213462551583968385592248911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142308367722645590394832607 213462551583968385592248911)
  ·
    refine ⟨320193827375952578388373367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213462551583968385592248911 320193827375952578388373367)
    ·
      refine ⟨480290741063928867582560051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320193827375952578388373367 480290741063928867582560051)
      ·
        refine ⟨720436111595893301373840077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480290741063928867582560051 720436111595893301373840077)
        ·
          refine ⟨270163541848459988015190029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 720436111595893301373840077 270163541848459988015190029)
          ·
            refine ⟨101311328193172495505696261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270163541848459988015190029 101311328193172495505696261)
            ·
              refine ⟨18995874036219842907318049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101311328193172495505696261 18995874036219842907318049)
              ·
                refine ⟨14246905527164882180488537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18995874036219842907318049 14246905527164882180488537)
                ·
                  refine ⟨10685179145373661635366403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14246905527164882180488537 10685179145373661635366403)
                  ·
                    refine ⟨16027768718060492453049605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10685179145373661635366403 16027768718060492453049605)
                    ·
                      refine ⟨3005206634636342334946801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16027768718060492453049605 3005206634636342334946801)
                      ·
                        rfl

theorem cell23_5852619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 4].length) (baseStart_5852619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852619 prefixEnd_5852619 := by exact prefixLift 5852619
  have htrace : WordTrace (prefixWord ++ tailWord_5852619) baseStart_5852619 baseEnd_5852619 := by
    simpa [prefixWord, tailWord_5852619, baseEnd_5852619] using wordTrace_append hprefix tailTrace_5852619
  have hstable : (prefixWord ++ tailWord_5852619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852619).length < 2 ^ (prefixWord ++ tailWord_5852619).sum := by decide
  have hdescent : baseEnd_5852619 < baseStart_5852619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852639 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 3]
def baseStart_5852639 : Nat := 118140960795 + 5852639 * 2 ^ 59
def prefixEnd_5852639 : Nat := 4983230072969 + 3 ^ 40 * 5852639 * 2
def baseEnd_5852639 : Nat := 3005216904249432256696709

theorem tailTrace_5852639 : CollatzResearch.WordTrace tailWord_5852639 prefixEnd_5852639 3005216904249432256696709 := by
  unfold tailWord_5852639
  simp only [CollatzResearch.WordTrace]
  refine ⟨213463281043895929007976971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142308854029263952671984647 213463281043895929007976971)
  ·
    refine ⟨320194921565843893511965457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213463281043895929007976971 320194921565843893511965457)
    ·
      refine ⟨240146191174382920133974093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320194921565843893511965457 240146191174382920133974093)
      ·
        refine ⟨90054821690393595050240285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240146191174382920133974093 90054821690393595050240285)
        ·
          refine ⟨33770558133897598143840107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90054821690393595050240285 33770558133897598143840107)
          ·
            refine ⟨50655837200846397215760161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33770558133897598143840107 50655837200846397215760161)
            ·
              refine ⟨37991877900634797911820121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50655837200846397215760161 37991877900634797911820121)
              ·
                refine ⟨28493908425476098433865091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37991877900634797911820121 28493908425476098433865091)
                ·
                  refine ⟨42740862638214147650797637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28493908425476098433865091 42740862638214147650797637)
                  ·
                    refine ⟨8013911744665152684524557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42740862638214147650797637 8013911744665152684524557)
                    ·
                      refine ⟨3005216904249432256696709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8013911744665152684524557 3005216904249432256696709)
                      ·
                        rfl

theorem cell23_5852639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_5852639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852639 prefixEnd_5852639 := by exact prefixLift 5852639
  have htrace : WordTrace (prefixWord ++ tailWord_5852639) baseStart_5852639 baseEnd_5852639 := by
    simpa [prefixWord, tailWord_5852639, baseEnd_5852639] using wordTrace_append hprefix tailTrace_5852639
  have hstable : (prefixWord ++ tailWord_5852639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852639).length < 2 ^ (prefixWord ++ tailWord_5852639).sum := by decide
  have hdescent : baseEnd_5852639 < baseStart_5852639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852656 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3]
def baseStart_5852656 : Nat := 118140960795 + 5852656 * 2 ^ 59
def prefixEnd_5852656 : Nat := 4983230072969 + 3 ^ 40 * 5852656 * 2
def baseEnd_5852656 : Nat := 3005225633420558690184131

theorem tailTrace_5852656 : CollatzResearch.WordTrace tailWord_5852656 prefixEnd_5852656 3005225633420558690184131 := by
  unfold tailWord_5852656
  simp only [CollatzResearch.WordTrace]
  refine ⟨106731950542417170455672911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142309267389889560607563881 106731950542417170455672911)
  ·
    refine ⟨160097925813625755683509367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106731950542417170455672911 160097925813625755683509367)
    ·
      refine ⟨240146888720438633525264051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160097925813625755683509367 240146888720438633525264051)
      ·
        refine ⟨360220333080657950287896077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240146888720438633525264051 360220333080657950287896077)
        ·
          refine ⟨135082624905246731357961029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360220333080657950287896077 135082624905246731357961029)
          ·
            refine ⟨25327992169733762129617693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135082624905246731357961029 25327992169733762129617693)
            ·
              refine ⟨9497997063650160798606635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25327992169733762129617693 9497997063650160798606635)
              ·
                refine ⟨14246995595475241197909953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9497997063650160798606635 14246995595475241197909953)
                ·
                  refine ⟨10685246696606430898432465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14246995595475241197909953 10685246696606430898432465)
                  ·
                    refine ⟨8013935022454823173824349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10685246696606430898432465 8013935022454823173824349)
                    ·
                      refine ⟨3005225633420558690184131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8013935022454823173824349 3005225633420558690184131)
                      ·
                        rfl

theorem cell23_5852656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_5852656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852656 prefixEnd_5852656 := by exact prefixLift 5852656
  have htrace : WordTrace (prefixWord ++ tailWord_5852656) baseStart_5852656 baseEnd_5852656 := by
    simpa [prefixWord, tailWord_5852656, baseEnd_5852656] using wordTrace_append hprefix tailTrace_5852656
  have hstable : (prefixWord ++ tailWord_5852656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852656).length < 2 ^ (prefixWord ++ tailWord_5852656).sum := by decide
  have hdescent : baseEnd_5852656 < baseStart_5852656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852676 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 8]
def baseStart_5852676 : Nat := 118140960795 + 5852676 * 2 ^ 59
def prefixEnd_5852676 : Nat := 4983230072969 + 3 ^ 40 * 5852676 * 2
def baseEnd_5852676 : Nat := 333915100337072067992671

theorem tailTrace_5852676 : CollatzResearch.WordTrace tailWord_5852676 prefixEnd_5852676 333915100337072067992671 := by
  unfold tailWord_5852676
  simp only [CollatzResearch.WordTrace]
  refine ⟨106732315272380942163536941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142309753696507922884715921 106732315272380942163536941)
  ·
    refine ⟨40024618227142853311326353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106732315272380942163536941 40024618227142853311326353)
    ·
      refine ⟨30018463670357139983494765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40024618227142853311326353 30018463670357139983494765)
      ·
        refine ⟨11256923876383927493810537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30018463670357139983494765 11256923876383927493810537)
        ·
          refine ⟨8442692907287945620357903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11256923876383927493810537 8442692907287945620357903)
          ·
            refine ⟨12664039360931918430536855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8442692907287945620357903 12664039360931918430536855)
            ·
              refine ⟨18996059041397877645805283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12664039360931918430536855 18996059041397877645805283)
              ·
                refine ⟨28494088562096816468707925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18996059041397877645805283 28494088562096816468707925)
                ·
                  refine ⟨333915100337072067992671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28494088562096816468707925 333915100337072067992671)
                  ·
                    rfl

theorem cell23_5852676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_5852676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852676 prefixEnd_5852676 := by exact prefixLift 5852676
  have htrace : WordTrace (prefixWord ++ tailWord_5852676) baseStart_5852676 baseEnd_5852676 := by
    simpa [prefixWord, tailWord_5852676, baseEnd_5852676] using wordTrace_append hprefix tailTrace_5852676
  have hstable : (prefixWord ++ tailWord_5852676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852676).length < 2 ^ (prefixWord ++ tailWord_5852676).sum := by decide
  have hdescent : baseEnd_5852676 < baseStart_5852676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852679 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5852679 : Nat := 118140960795 + 5852679 * 2 ^ 59
def prefixEnd_5852679 : Nat := 4983230072969 + 3 ^ 40 * 5852679 * 2
def baseEnd_5852679 : Nat := 3005237443475612100196525

theorem tailTrace_5852679 : CollatzResearch.WordTrace tailWord_5852679 prefixEnd_5852679 3005237443475612100196525 := by
  unfold tailWord_5852679
  simp only [CollatzResearch.WordTrace]
  refine ⟨213464739963751015839433091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142309826642500677226288727 213464739963751015839433091)
  ·
    refine ⟨320197109945626523759149637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213464739963751015839433091 320197109945626523759149637)
    ·
      refine ⟨60036958114804973204840557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320197109945626523759149637 60036958114804973204840557)
      ·
        refine ⟨22513859293051864951815209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60036958114804973204840557 22513859293051864951815209)
        ·
          refine ⟨16885394469788898713861407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22513859293051864951815209 16885394469788898713861407)
          ·
            refine ⟨25328091704683348070792111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16885394469788898713861407 25328091704683348070792111)
            ·
              refine ⟨37992137557025022106188167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25328091704683348070792111 37992137557025022106188167)
              ·
                refine ⟨56988206335537533159282251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37992137557025022106188167 56988206335537533159282251)
                ·
                  refine ⟨85482309503306299738923377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56988206335537533159282251 85482309503306299738923377)
                  ·
                    refine ⟨64111732127479724804192533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85482309503306299738923377 64111732127479724804192533)
                    ·
                      refine ⟨3005237443475612100196525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64111732127479724804192533 3005237443475612100196525)
                      ·
                        rfl

theorem cell23_5852679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5852679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852679 prefixEnd_5852679 := by exact prefixLift 5852679
  have htrace : WordTrace (prefixWord ++ tailWord_5852679) baseStart_5852679 baseEnd_5852679 := by
    simpa [prefixWord, tailWord_5852679, baseEnd_5852679] using wordTrace_append hprefix tailTrace_5852679
  have hstable : (prefixWord ++ tailWord_5852679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852679).length < 2 ^ (prefixWord ++ tailWord_5852679).sum := by decide
  have hdescent : baseEnd_5852679 < baseStart_5852679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852706 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_5852706 : Nat := 118140960795 + 5852706 * 2 ^ 59
def prefixEnd_5852706 : Nat := 4983230072969 + 3 ^ 40 * 5852706 * 2
def baseEnd_5852706 : Nat := 1001750435817761164852967

theorem tailTrace_5852706 : CollatzResearch.WordTrace tailWord_5852706 prefixEnd_5852706 1001750435817761164852967 := by
  unfold tailWord_5852706
  simp only [CollatzResearch.WordTrace]
  refine ⟨53366431183663299862666493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142310483156435466300443981 53366431183663299862666493)
  ·
    refine ⟨20012411693873737448499935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53366431183663299862666493 20012411693873737448499935)
    ·
      refine ⟨30018617540810606172749903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20012411693873737448499935 30018617540810606172749903)
      ·
        refine ⟨45027926311215909259124855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30018617540810606172749903 45027926311215909259124855)
        ·
          refine ⟨67541889466823863888687283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45027926311215909259124855 67541889466823863888687283)
          ·
            refine ⟨101312834200235795833030925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67541889466823863888687283 101312834200235795833030925)
            ·
              refine ⟨37992312825088423437386597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101312834200235795833030925 37992312825088423437386597)
              ·
                refine ⟨7123558654704079394509987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37992312825088423437386597 7123558654704079394509987)
                ·
                  refine ⟨10685337982056119091764981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7123558654704079394509987 10685337982056119091764981)
                  ·
                    refine ⟨1001750435817761164852967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10685337982056119091764981 1001750435817761164852967)
                    ·
                      rfl

theorem cell23_5852706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_5852706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852706 prefixEnd_5852706 := by exact prefixLift 5852706
  have htrace : WordTrace (prefixWord ++ tailWord_5852706) baseStart_5852706 baseEnd_5852706 := by
    simpa [prefixWord, tailWord_5852706, baseEnd_5852706] using wordTrace_append hprefix tailTrace_5852706
  have hstable : (prefixWord ++ tailWord_5852706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852706).length < 2 ^ (prefixWord ++ tailWord_5852706).sum := by decide
  have hdescent : baseEnd_5852706 < baseStart_5852706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852736 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 2, 4]
def baseStart_5852736 : Nat := 118140960795 + 5852736 * 2 ^ 59
def prefixEnd_5852736 : Nat := 4983230072969 + 3 ^ 40 * 5852736 * 2
def baseEnd_5852736 : Nat := 1001755570624306125727921

theorem tailTrace_5852736 : CollatzResearch.WordTrace tailWord_5852736 prefixEnd_5852736 1001755570624306125727921 := by
  unfold tailWord_5852736
  simp only [CollatzResearch.WordTrace]
  refine ⟨106733409462272257287129031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142311212616363009716172041 106733409462272257287129031)
  ·
    refine ⟨160100114193408385930693547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106733409462272257287129031 160100114193408385930693547)
    ·
      refine ⟨240150171290112578896040321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160100114193408385930693547 240150171290112578896040321)
      ·
        refine ⟨180112628467584434172030241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240150171290112578896040321 180112628467584434172030241)
        ·
          refine ⟨135084471350688325629022681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180112628467584434172030241 135084471350688325629022681)
          ·
            refine ⟨101313353513016244221767011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135084471350688325629022681 101313353513016244221767011)
            ·
              refine ⟨151970030269524366332650517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101313353513016244221767011 151970030269524366332650517)
              ·
                refine ⟨7123595168883954671842993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151970030269524366332650517 7123595168883954671842993)
                ·
                  refine ⟨5342696376662966003882245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7123595168883954671842993 5342696376662966003882245)
                  ·
                    refine ⟨1001755570624306125727921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5342696376662966003882245 1001755570624306125727921)
                    ·
                      rfl

theorem cell23_5852736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_5852736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852736 prefixEnd_5852736 := by exact prefixLift 5852736
  have htrace : WordTrace (prefixWord ++ tailWord_5852736) baseStart_5852736 baseEnd_5852736 := by
    simpa [prefixWord, tailWord_5852736, baseEnd_5852736] using wordTrace_append hprefix tailTrace_5852736
  have hstable : (prefixWord ++ tailWord_5852736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852736).length < 2 ^ (prefixWord ++ tailWord_5852736).sum := by decide
  have hdescent : baseEnd_5852736 < baseStart_5852736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852737 : List Nat := [1, 2, 5, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_5852737 : Nat := 118140960795 + 5852737 * 2 ^ 59
def prefixEnd_5852737 : Nat := 4983230072969 + 3 ^ 40 * 5852737 * 2
def baseEnd_5852737 : Nat := 3005267225353572873271259

theorem tailTrace_5852737 : CollatzResearch.WordTrace tailWord_5852737 prefixEnd_5852737 3005267225353572873271259 := by
  unfold tailWord_5852737
  simp only [CollatzResearch.WordTrace]
  refine ⟨213466855397540891745044465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142311236931693927830029643 213466855397540891745044465)
  ·
    refine ⟨160100141548155668808783349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213466855397540891745044465 160100141548155668808783349)
    ·
      refine ⟨15009388270139593950823439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160100141548155668808783349 15009388270139593950823439)
      ·
        refine ⟨22514082405209390926235159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15009388270139593950823439 22514082405209390926235159)
        ·
          refine ⟨33771123607814086389352739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22514082405209390926235159 33771123607814086389352739)
          ·
            refine ⟨50656685411721129584029109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33771123607814086389352739 50656685411721129584029109)
            ·
              refine ⟨4749064257348855898502729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50656685411721129584029109 4749064257348855898502729)
              ·
                refine ⟨3561798193011641923877047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4749064257348855898502729 3561798193011641923877047)
                ·
                  refine ⟨5342697289517462885815571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561798193011641923877047 5342697289517462885815571)
                  ·
                    refine ⟨8014045934276194328723357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5342697289517462885815571 8014045934276194328723357)
                    ·
                      refine ⟨3005267225353572873271259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014045934276194328723357 3005267225353572873271259)
                      ·
                        rfl

theorem cell23_5852737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_5852737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852737 prefixEnd_5852737 := by exact prefixLift 5852737
  have htrace : WordTrace (prefixWord ++ tailWord_5852737) baseStart_5852737 baseEnd_5852737 := by
    simpa [prefixWord, tailWord_5852737, baseEnd_5852737] using wordTrace_append hprefix tailTrace_5852737
  have hstable : (prefixWord ++ tailWord_5852737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852737).length < 2 ^ (prefixWord ++ tailWord_5852737).sum := by decide
  have hdescent : baseEnd_5852737 < baseStart_5852737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852746 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_5852746 : Nat := 118140960795 + 5852746 * 2 ^ 59
def prefixEnd_5852746 : Nat := 4983230072969 + 3 ^ 40 * 5852746 * 2
def baseEnd_5852746 : Nat := 3005271846679463338058717

theorem tailTrace_5852746 : CollatzResearch.WordTrace tailWord_5852746 prefixEnd_5852746 3005271846679463338058717 := by
  unfold tailWord_5852746
  simp only [CollatzResearch.WordTrace]
  refine ⟨53366795913627071570530523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142311455769672190854748061 53366795913627071570530523)
  ·
    refine ⟨80050193870440607355795785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53366795913627071570530523 80050193870440607355795785)
    ·
      refine ⟨60037645402830455516846839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80050193870440607355795785 60037645402830455516846839)
      ·
        refine ⟨90056468104245683275270259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60037645402830455516846839 90056468104245683275270259)
        ·
          refine ⟨135084702156368524912905389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90056468104245683275270259 135084702156368524912905389)
          ·
            refine ⟨50656763308638196842339521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135084702156368524912905389 50656763308638196842339521)
            ·
              refine ⟨37992572481478647631754641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50656763308638196842339521 37992572481478647631754641)
              ·
                refine ⟨28494429361108985723815981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37992572481478647631754641 28494429361108985723815981)
                ·
                  refine ⟨10685411010415869646430993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28494429361108985723815981 10685411010415869646430993)
                  ·
                    refine ⟨8014058257811902234823245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10685411010415869646430993 8014058257811902234823245)
                    ·
                      refine ⟨3005271846679463338058717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014058257811902234823245 3005271846679463338058717)
                      ·
                        rfl

theorem cell23_5852746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_5852746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852746 prefixEnd_5852746 := by exact prefixLift 5852746
  have htrace : WordTrace (prefixWord ++ tailWord_5852746) baseStart_5852746 baseEnd_5852746 := by
    simpa [prefixWord, tailWord_5852746, baseEnd_5852746] using wordTrace_append hprefix tailTrace_5852746
  have hstable : (prefixWord ++ tailWord_5852746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852746).length < 2 ^ (prefixWord ++ tailWord_5852746).sum := by decide
  have hdescent : baseEnd_5852746 < baseStart_5852746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852756 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_5852756 : Nat := 118140960795 + 5852756 * 2 ^ 59
def prefixEnd_5852756 : Nat := 4983230072969 + 3 ^ 40 * 5852756 * 2
def baseEnd_5852756 : Nat := 3005276981486008298933671

theorem tailTrace_5852756 : CollatzResearch.WordTrace tailWord_5852756 prefixEnd_5852756 3005276981486008298933671 := by
  unfold tailWord_5852756
  simp only [CollatzResearch.WordTrace]
  refine ⟨106733774192236028994993061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142311698922981371993324081 106733774192236028994993061)
  ·
    refine ⟨20012582661044255436561199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106733774192236028994993061 20012582661044255436561199)
    ·
      refine ⟨30018873991566383154841799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20012582661044255436561199 30018873991566383154841799)
      ·
        refine ⟨45028310987349574732262699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30018873991566383154841799 45028310987349574732262699)
        ·
          refine ⟨67542466481024362098394049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45028310987349574732262699 67542466481024362098394049)
          ·
            refine ⟨50656849860768271573795537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67542466481024362098394049 50656849860768271573795537)
            ·
              refine ⟨37992637395576203680346653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50656849860768271573795537 37992637395576203680346653)
              ·
                refine ⟨14247239023341076380129995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37992637395576203680346653 14247239023341076380129995)
                ·
                  refine ⟨21370858535011614570194993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14247239023341076380129995 21370858535011614570194993)
                  ·
                    refine ⟨16028143901258710927646245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21370858535011614570194993 16028143901258710927646245)
                    ·
                      refine ⟨3005276981486008298933671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16028143901258710927646245 3005276981486008298933671)
                      ·
                        rfl

theorem cell23_5852756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_5852756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852756 prefixEnd_5852756 := by exact prefixLift 5852756
  have htrace : WordTrace (prefixWord ++ tailWord_5852756) baseStart_5852756 baseEnd_5852756 := by
    simpa [prefixWord, tailWord_5852756, baseEnd_5852756] using wordTrace_append hprefix tailTrace_5852756
  have hstable : (prefixWord ++ tailWord_5852756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852756).length < 2 ^ (prefixWord ++ tailWord_5852756).sum := by decide
  have hdescent : baseEnd_5852756 < baseStart_5852756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852809 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 1, 8]
def baseStart_5852809 : Nat := 118140960795 + 5852809 * 2 ^ 59
def prefixEnd_5852809 : Nat := 4983230072969 + 3 ^ 40 * 5852809 * 2
def baseEnd_5852809 : Nat := 1001768065320232197190309

theorem tailTrace_5852809 : CollatzResearch.WordTrace tailWord_5852809 prefixEnd_5852809 1001768065320232197190309 := by
  unfold tailWord_5852809
  simp only [CollatzResearch.WordTrace]
  refine ⟨213469481453280048041665481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142312987635520032027776987 213469481453280048041665481)
  ·
    refine ⟨160102111089960036031249111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213469481453280048041665481 160102111089960036031249111)
    ·
      refine ⟨240153166634940054046873667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160102111089960036031249111 240153166634940054046873667)
      ·
        refine ⟨360229749952410081070310501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240153166634940054046873667 360229749952410081070310501)
        ·
          refine ⟨67543078116076890200683219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360229749952410081070310501 67543078116076890200683219)
          ·
            refine ⟨101314617174115335301024829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67543078116076890200683219 101314617174115335301024829)
            ·
              refine ⟨37992981440293250737884311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101314617174115335301024829 37992981440293250737884311)
              ·
                refine ⟨56989472160439876106826467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37992981440293250737884311 56989472160439876106826467)
                ·
                  refine ⟨85484208240659814160239701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56989472160439876106826467 85484208240659814160239701)
                  ·
                    refine ⟨1001768065320232197190309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85484208240659814160239701 1001768065320232197190309)
                    ·
                      rfl

theorem cell23_5852809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_5852809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852809 prefixEnd_5852809 := by exact prefixLift 5852809
  have htrace : WordTrace (prefixWord ++ tailWord_5852809) baseStart_5852809 baseEnd_5852809 := by
    simpa [prefixWord, tailWord_5852809, baseEnd_5852809] using wordTrace_append hprefix tailTrace_5852809
  have hstable : (prefixWord ++ tailWord_5852809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852809).length < 2 ^ (prefixWord ++ tailWord_5852809).sum := by decide
  have hdescent : baseEnd_5852809 < baseStart_5852809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852810 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_5852810 : Nat := 118140960795 + 5852810 * 2 ^ 59
def prefixEnd_5852810 : Nat := 4983230072969 + 3 ^ 40 * 5852810 * 2
def baseEnd_5852810 : Nat := 3005304709441351087658423

theorem tailTrace_5852810 : CollatzResearch.WordTrace tailWord_5852810 prefixEnd_5852810 3005304709441351087658423 := by
  unfold tailWord_5852810
  simp only [CollatzResearch.WordTrace]
  refine ⟨53367379481569106303112971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142313011950850950141634589 53367379481569106303112971)
  ·
    refine ⟨80051069222353659454669457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53367379481569106303112971 80051069222353659454669457)
    ·
      refine ⟨60038301916765244591002093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80051069222353659454669457 60038301916765244591002093)
      ·
        refine ⟨22514363218786966721625785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60038301916765244591002093 22514363218786966721625785)
        ·
          refine ⟨16885772414090225041219339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22514363218786966721625785 16885772414090225041219339)
          ·
            refine ⟨25328658621135337561829009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16885772414090225041219339 25328658621135337561829009)
            ·
              refine ⟨18996493965851503171371757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25328658621135337561829009 18996493965851503171371757)
              ·
                refine ⟨7123685237194313689264409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18996493965851503171371757 7123685237194313689264409)
                ·
                  refine ⟨5342763927895735266948307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7123685237194313689264409 5342763927895735266948307)
                  ·
                    refine ⟨8014145891843602900422461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5342763927895735266948307 8014145891843602900422461)
                    ·
                      refine ⟨3005304709441351087658423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014145891843602900422461 3005304709441351087658423)
                      ·
                        rfl

theorem cell23_5852810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_5852810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852810 prefixEnd_5852810 := by exact prefixLift 5852810
  have htrace : WordTrace (prefixWord ++ tailWord_5852810) baseStart_5852810 baseEnd_5852810 := by
    simpa [prefixWord, tailWord_5852810, baseEnd_5852810] using wordTrace_append hprefix tailTrace_5852810
  have hstable : (prefixWord ++ tailWord_5852810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852810).length < 2 ^ (prefixWord ++ tailWord_5852810).sum := by decide
  have hdescent : baseEnd_5852810 < baseStart_5852810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852890 : List Nat := [3, 1, 1, 2, 2, 5, 1, 3, 5]
def baseStart_5852890 : Nat := 118140960795 + 5852890 * 2 ^ 59
def prefixEnd_5852890 : Nat := 4983230072969 + 3 ^ 40 * 5852890 * 2
def baseEnd_5852890 : Nat := 333927309765967863850895

theorem tailTrace_5852890 : CollatzResearch.WordTrace tailWord_5852890 prefixEnd_5852890 333927309765967863850895 := by
  unfold tailWord_5852890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53368108941496649718841031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142314957177324399250242749 53368108941496649718841031)
  ·
    refine ⟨80052163412244974578261547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53368108941496649718841031 80052163412244974578261547)
    ·
      refine ⟨120078245118367461867392321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80052163412244974578261547 120078245118367461867392321)
      ·
        refine ⟨90058683838775596400544241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120078245118367461867392321 90058683838775596400544241)
        ·
          refine ⟨67544012879081697300408181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90058683838775596400544241 67544012879081697300408181)
          ·
            refine ⟨6332251207413909121913267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67544012879081697300408181 6332251207413909121913267)
            ·
              refine ⟨9498376811120863682869901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6332251207413909121913267 9498376811120863682869901)
              ·
                refine ⟨3561891304170323881076213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9498376811120863682869901 3561891304170323881076213)
                ·
                  refine ⟨333927309765967863850895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3561891304170323881076213 333927309765967863850895)
                  ·
                    rfl

theorem cell23_5852890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_5852890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852890 prefixEnd_5852890 := by exact prefixLift 5852890
  have htrace : WordTrace (prefixWord ++ tailWord_5852890) baseStart_5852890 baseEnd_5852890 := by
    simpa [prefixWord, tailWord_5852890, baseEnd_5852890] using wordTrace_append hprefix tailTrace_5852890
  have hstable : (prefixWord ++ tailWord_5852890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852890).length < 2 ^ (prefixWord ++ tailWord_5852890).sum := by decide
  have hdescent : baseEnd_5852890 < baseStart_5852890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852958 : List Nat := [4, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_5852958 : Nat := 118140960795 + 5852958 * 2 ^ 59
def prefixEnd_5852958 : Nat := 4983230072969 + 3 ^ 40 * 5852958 * 2
def baseEnd_5852958 : Nat := 333931189397579612067527

theorem tailTrace_5852958 : CollatzResearch.WordTrace tailWord_5852958 prefixEnd_5852958 333931189397579612067527 := by
  unfold tailWord_5852958
  simp only [CollatzResearch.WordTrace]
  refine ⟨26684364491217530811104941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142316610619826830992559685 26684364491217530811104941)
  ·
    refine ⟨10006636684206574054164353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26684364491217530811104941 10006636684206574054164353)
    ·
      refine ⟨7504977513154930540623265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10006636684206574054164353 7504977513154930540623265)
      ·
        refine ⟨5628733134866197905467449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7504977513154930540623265 5628733134866197905467449)
        ·
          refine ⟨4221549851149648429100587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5628733134866197905467449 4221549851149648429100587)
          ·
            refine ⟨6332324776724472643650881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221549851149648429100587 6332324776724472643650881)
            ·
              refine ⟨4749243582543354482738161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6332324776724472643650881 4749243582543354482738161)
              ·
                refine ⟨3561932686907515862053621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4749243582543354482738161 3561932686907515862053621)
                ·
                  refine ⟨333931189397579612067527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3561932686907515862053621 333931189397579612067527)
                  ·
                    rfl

theorem cell23_5852958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_5852958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852958 prefixEnd_5852958 := by exact prefixLift 5852958
  have htrace : WordTrace (prefixWord ++ tailWord_5852958) baseStart_5852958 baseEnd_5852958 := by
    simpa [prefixWord, tailWord_5852958, baseEnd_5852958] using wordTrace_append hprefix tailTrace_5852958
  have hstable : (prefixWord ++ tailWord_5852958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852958).length < 2 ^ (prefixWord ++ tailWord_5852958).sum := by decide
  have hdescent : baseEnd_5852958 < baseStart_5852958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5852980 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 6]
def baseStart_5852980 : Nat := 118140960795 + 5852980 * 2 ^ 59
def prefixEnd_5852980 : Nat := 4983230072969 + 3 ^ 40 * 5852980 * 2
def baseEnd_5852980 : Nat := 333932444572512824725849

theorem tailTrace_5852980 : CollatzResearch.WordTrace tailWord_5852980 prefixEnd_5852980 333932444572512824725849 := by
  unfold tailWord_5852980
  simp only [CollatzResearch.WordTrace]
  refine ⟨106737859167830272123070197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142317145557107029497426929 106737859167830272123070197)
  ·
    refine ⟨10006674296984088011537831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106737859167830272123070197 10006674296984088011537831)
    ·
      refine ⟨15010011445476132017306747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006674296984088011537831 15010011445476132017306747)
      ·
        refine ⟨22515017168214198025960121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15010011445476132017306747 22515017168214198025960121)
        ·
          refine ⟨16886262876160648519470091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22515017168214198025960121 16886262876160648519470091)
          ·
            refine ⟨25329394314240972779205137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16886262876160648519470091 25329394314240972779205137)
            ·
              refine ⟨18997045735680729584403853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25329394314240972779205137 18997045735680729584403853)
              ·
                refine ⟨7123892150880273594151445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18997045735680729584403853 7123892150880273594151445)
                ·
                  refine ⟨333932444572512824725849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7123892150880273594151445 333932444572512824725849)
                  ·
                    rfl

theorem cell23_5852980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_5852980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5852980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5852980 prefixEnd_5852980 := by exact prefixLift 5852980
  have htrace : WordTrace (prefixWord ++ tailWord_5852980) baseStart_5852980 baseEnd_5852980 := by
    simpa [prefixWord, tailWord_5852980, baseEnd_5852980] using wordTrace_append hprefix tailTrace_5852980
  have hstable : (prefixWord ++ tailWord_5852980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5852980).length < 2 ^ (prefixWord ++ tailWord_5852980).sum := by decide
  have hdescent : baseEnd_5852980 < baseStart_5852980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5852980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853000 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_5853000 : Nat := 118140960795 + 5853000 * 2 ^ 59
def prefixEnd_5853000 : Nat := 4983230072969 + 3 ^ 40 * 5853000 * 2
def baseEnd_5853000 : Nat := 3005402270765705344282549

theorem tailTrace_5853000 : CollatzResearch.WordTrace tailWord_5853000 prefixEnd_5853000 3005402270765705344282549 := by
  unfold tailWord_5853000
  simp only [CollatzResearch.WordTrace]
  refine ⟨106738223897794043830934227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142317631863725391774578969 106738223897794043830934227)
  ·
    refine ⟨160107335846691065746401341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106738223897794043830934227 160107335846691065746401341)
    ·
      refine ⟨60040250942509149654900503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160107335846691065746401341 60040250942509149654900503)
      ·
        refine ⟨90060376413763724482350755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60040250942509149654900503 90060376413763724482350755)
        ·
          refine ⟨135090564620645586723526133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90060376413763724482350755 135090564620645586723526133)
          ·
            refine ⟨12664740433185523755330575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135090564620645586723526133 12664740433185523755330575)
            ·
              refine ⟨18997110649778285632995863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12664740433185523755330575 18997110649778285632995863)
              ·
                refine ⟨28495665974667428449493795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18997110649778285632995863 28495665974667428449493795)
                ·
                  refine ⟨42743498962001142674240693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28495665974667428449493795 42743498962001142674240693)
                  ·
                    refine ⟨4007203027687607125710065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42743498962001142674240693 4007203027687607125710065)
                    ·
                      refine ⟨3005402270765705344282549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4007203027687607125710065 3005402270765705344282549)
                      ·
                        rfl

theorem cell23_5853000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_5853000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853000 prefixEnd_5853000 := by exact prefixLift 5853000
  have htrace : WordTrace (prefixWord ++ tailWord_5853000) baseStart_5853000 baseEnd_5853000 := by
    simpa [prefixWord, tailWord_5853000, baseEnd_5853000] using wordTrace_append hprefix tailTrace_5853000
  have hstable : (prefixWord ++ tailWord_5853000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853000).length < 2 ^ (prefixWord ++ tailWord_5853000).sum := by decide
  have hdescent : baseEnd_5853000 < baseStart_5853000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853010 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_5853010 : Nat := 118140960795 + 5853010 * 2 ^ 59
def prefixEnd_5853010 : Nat := 4983230072969 + 3 ^ 40 * 5853010 * 2
def baseEnd_5853010 : Nat := 1001802468524083435052501

theorem tailTrace_5853010 : CollatzResearch.WordTrace tailWord_5853010 prefixEnd_5853010 1001802468524083435052501 := by
  unfold tailWord_5853010
  simp only [CollatzResearch.WordTrace]
  refine ⟨53369203131387964842433121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142317875017034572913154989 53369203131387964842433121)
  ·
    refine ⟨40026902348540973631824841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53369203131387964842433121 40026902348540973631824841)
    ·
      refine ⟨30020176761405730223868631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40026902348540973631824841 30020176761405730223868631)
      ·
        refine ⟨45030265142108595335802947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30020176761405730223868631 45030265142108595335802947)
        ·
          refine ⟨67545397713162893003704421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45030265142108595335802947 67545397713162893003704421)
          ·
            refine ⟨12664762071218042438194579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67545397713162893003704421 12664762071218042438194579)
            ·
              refine ⟨18997143106827063657291869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12664762071218042438194579 18997143106827063657291869)
              ·
                refine ⟨7123928665060148871484451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18997143106827063657291869 7123928665060148871484451)
                ·
                  refine ⟨10685892997590223307226677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7123928665060148871484451 10685892997590223307226677)
                  ·
                    refine ⟨1001802468524083435052501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10685892997590223307226677 1001802468524083435052501)
                    ·
                      rfl

theorem cell23_5853010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_5853010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853010 prefixEnd_5853010 := by exact prefixLift 5853010
  have htrace : WordTrace (prefixWord ++ tailWord_5853010) baseStart_5853010 baseEnd_5853010 := by
    simpa [prefixWord, tailWord_5853010, baseEnd_5853010] using wordTrace_append hprefix tailTrace_5853010
  have hstable : (prefixWord ++ tailWord_5853010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853010).length < 2 ^ (prefixWord ++ tailWord_5853010).sum := by decide
  have hdescent : baseEnd_5853010 < baseStart_5853010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853033 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 3]
def baseStart_5853033 : Nat := 118140960795 + 5853033 * 2 ^ 59
def prefixEnd_5853033 : Nat := 4983230072969 + 3 ^ 40 * 5853033 * 2
def baseEnd_5853033 : Nat := 3005419215627303715169897

theorem tailTrace_5853033 : CollatzResearch.WordTrace tailWord_5853033 prefixEnd_5853033 3005419215627303715169897 := by
  unfold tailWord_5853033
  simp only [CollatzResearch.WordTrace]
  refine ⟨213477651404468534297819753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142318434269645689531879835 213477651404468534297819753)
  ·
    refine ⟨160108238553351400723364815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213477651404468534297819753 160108238553351400723364815)
    ·
      refine ⟨240162357830027101085047223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160108238553351400723364815 240162357830027101085047223)
      ·
        refine ⟨360243536745040651627570835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240162357830027101085047223 360243536745040651627570835)
        ·
          refine ⟨540365305117560977441356253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360243536745040651627570835 540365305117560977441356253)
          ·
            refine ⟨202636989419085366540508595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540365305117560977441356253 202636989419085366540508595)
            ·
              refine ⟨303955484128628049810762893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202636989419085366540508595 303955484128628049810762893)
              ·
                refine ⟨113983306548235518679036085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303955484128628049810762893 113983306548235518679036085)
                ·
                  refine ⟨10685934988897079876159633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113983306548235518679036085 10685934988897079876159633)
                  ·
                    refine ⟨8014451241672809907119725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10685934988897079876159633 8014451241672809907119725)
                    ·
                      refine ⟨3005419215627303715169897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014451241672809907119725 3005419215627303715169897)
                      ·
                        rfl

theorem cell23_5853033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_5853033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853033 prefixEnd_5853033 := by exact prefixLift 5853033
  have htrace : WordTrace (prefixWord ++ tailWord_5853033) baseStart_5853033 baseEnd_5853033 := by
    simpa [prefixWord, tailWord_5853033, baseEnd_5853033] using wordTrace_append hprefix tailTrace_5853033
  have hstable : (prefixWord ++ tailWord_5853033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853033).length < 2 ^ (prefixWord ++ tailWord_5853033).sum := by decide
  have hdescent : baseEnd_5853033 < baseStart_5853033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853050 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_5853050 : Nat := 118140960795 + 5853050 * 2 ^ 59
def prefixEnd_5853050 : Nat := 4983230072969 + 3 ^ 40 * 5853050 * 2
def baseEnd_5853050 : Nat := 3005427944798430148657319

theorem tailTrace_5853050 : CollatzResearch.WordTrace tailWord_5853050 prefixEnd_5853050 3005427944798430148657319 := by
  unfold tailWord_5853050
  simp only [CollatzResearch.WordTrace]
  refine ⟨53369567861351736550297151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142318847630271297467459069 53369567861351736550297151)
  ·
    refine ⟨80054351792027604825445727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53369567861351736550297151 80054351792027604825445727)
    ·
      refine ⟨120081527688041407238168591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80054351792027604825445727 120081527688041407238168591)
      ·
        refine ⟨180122291532062110857252887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120081527688041407238168591 180122291532062110857252887)
        ·
          refine ⟨270183437298093166285879331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180122291532062110857252887 270183437298093166285879331)
          ·
            refine ⟨405275155947139749428818997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270183437298093166285879331 405275155947139749428818997)
            ·
              refine ⟨37994545870044351508951781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 405275155947139749428818997 37994545870044351508951781)
              ·
                refine ⟨7123977350633315907928459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37994545870044351508951781 7123977350633315907928459)
                ·
                  refine ⟨10685966025949973861892689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7123977350633315907928459 10685966025949973861892689)
                  ·
                    refine ⟨8014474519462480396419517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10685966025949973861892689 8014474519462480396419517)
                    ·
                      refine ⟨3005427944798430148657319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014474519462480396419517 3005427944798430148657319)
                      ·
                        rfl

theorem cell23_5853050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_5853050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853050 prefixEnd_5853050 := by exact prefixLift 5853050
  have htrace : WordTrace (prefixWord ++ tailWord_5853050) baseStart_5853050 baseEnd_5853050 := by
    simpa [prefixWord, tailWord_5853050, baseEnd_5853050] using wordTrace_append hprefix tailTrace_5853050
  have hstable : (prefixWord ++ tailWord_5853050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853050).length < 2 ^ (prefixWord ++ tailWord_5853050).sum := by decide
  have hdescent : baseEnd_5853050 < baseStart_5853050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853123 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 3]
def baseStart_5853123 : Nat := 118140960795 + 5853123 * 2 ^ 59
def prefixEnd_5853123 : Nat := 4983230072969 + 3 ^ 40 * 5853123 * 2
def baseEnd_5853123 : Nat := 3005465428886208363044483

theorem tailTrace_5853123 : CollatzResearch.WordTrace tailWord_5853123 prefixEnd_5853123 3005465428886208363044483 := by
  unfold tailWord_5853123
  simp only [CollatzResearch.WordTrace]
  refine ⟨213480933974142479668596023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142320622649428319779064015 213480933974142479668596023)
  ·
    refine ⟨320221400961213719502894035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213480933974142479668596023 320221400961213719502894035)
    ·
      refine ⟨480332101441820579254341053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320221400961213719502894035 480332101441820579254341053)
      ·
        refine ⟨180124538040682717220377895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480332101441820579254341053 180124538040682717220377895)
        ·
          refine ⟨270186807061024075830566843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180124538040682717220377895 270186807061024075830566843)
          ·
            refine ⟨405280210591536113745850265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270186807061024075830566843 405280210591536113745850265)
            ·
              refine ⟨303960157943652085309387699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405280210591536113745850265 303960157943652085309387699)
              ·
                refine ⟨455940236915478127964081549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303960157943652085309387699 455940236915478127964081549)
                ·
                  refine ⟨170977588843304297986530581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455940236915478127964081549 170977588843304297986530581)
                  ·
                    refine ⟨8014574477029888968118621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170977588843304297986530581 8014574477029888968118621)
                    ·
                      refine ⟨3005465428886208363044483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014574477029888968118621 3005465428886208363044483)
                      ·
                        rfl

theorem cell23_5853123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_5853123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853123 prefixEnd_5853123 := by exact prefixLift 5853123
  have htrace : WordTrace (prefixWord ++ tailWord_5853123) baseStart_5853123 baseEnd_5853123 := by
    simpa [prefixWord, tailWord_5853123, baseEnd_5853123] using wordTrace_append hprefix tailTrace_5853123
  have hstable : (prefixWord ++ tailWord_5853123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853123).length < 2 ^ (prefixWord ++ tailWord_5853123).sum := by decide
  have hdescent : baseEnd_5853123 < baseStart_5853123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853140 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_5853140 : Nat := 118140960795 + 5853140 * 2 ^ 59
def prefixEnd_5853140 : Nat := 4983230072969 + 3 ^ 40 * 5853140 * 2
def baseEnd_5853140 : Nat := 3005474158057334796531905

theorem tailTrace_5853140 : CollatzResearch.WordTrace tailWord_5853140 prefixEnd_5853140 3005474158057334796531905 := by
  unfold tailWord_5853140
  simp only [CollatzResearch.WordTrace]
  refine ⟨106740777007540445785982437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142321036010053927714643249 106740777007540445785982437)
  ·
    refine ⟨20013895688913833584871707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106740777007540445785982437 20013895688913833584871707)
    ·
      refine ⟨30020843533370750377307561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20013895688913833584871707 30020843533370750377307561)
      ·
        refine ⟨22515632650028062782980671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30020843533370750377307561 22515632650028062782980671)
        ·
          refine ⟨33773448975042094174471007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22515632650028062782980671 33773448975042094174471007)
          ·
            refine ⟨50660173462563141261706511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33773448975042094174471007 50660173462563141261706511)
            ·
              refine ⟨75990260193844711892559767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50660173462563141261706511 75990260193844711892559767)
              ·
                refine ⟨113985390290767067838839651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75990260193844711892559767 113985390290767067838839651)
                ·
                  refine ⟨170978085436150601758259477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113985390290767067838839651 170978085436150601758259477)
                  ·
                    refine ⟨8014597754819559457418413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170978085436150601758259477 8014597754819559457418413)
                    ·
                      refine ⟨3005474158057334796531905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014597754819559457418413 3005474158057334796531905)
                      ·
                        rfl

theorem cell23_5853140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_5853140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853140 prefixEnd_5853140 := by exact prefixLift 5853140
  have htrace : WordTrace (prefixWord ++ tailWord_5853140) baseStart_5853140 baseEnd_5853140 := by
    simpa [prefixWord, tailWord_5853140, baseEnd_5853140] using wordTrace_append hprefix tailTrace_5853140
  have hstable : (prefixWord ++ tailWord_5853140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853140).length < 2 ^ (prefixWord ++ tailWord_5853140).sum := by decide
  have hdescent : baseEnd_5853140 < baseStart_5853140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853143 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 7]
def baseStart_5853143 : Nat := 118140960795 + 5853143 * 2 ^ 59
def prefixEnd_5853143 : Nat := 4983230072969 + 3 ^ 40 * 5853143 * 2
def baseEnd_5853143 : Nat := 333941744277699809421599

theorem tailTrace_5853143 : CollatzResearch.WordTrace tailWord_5853143 prefixEnd_5853143 333941744277699809421599 := by
  unfold tailWord_5853143
  simp only [CollatzResearch.WordTrace]
  refine ⟨213481663434070023084324083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142321108956046682056216055 213481663434070023084324083)
  ·
    refine ⟨320222495151105034626486125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213481663434070023084324083 320222495151105034626486125)
    ·
      refine ⟨120083435681664387984932297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320222495151105034626486125 120083435681664387984932297)
      ·
        refine ⟨90062576761248290988699223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120083435681664387984932297 90062576761248290988699223)
        ·
          refine ⟨135093865141872436483048835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90062576761248290988699223 135093865141872436483048835)
          ·
            refine ⟨202640797712808654724573253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135093865141872436483048835 202640797712808654724573253)
            ·
              refine ⟨37995149571151622760857485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202640797712808654724573253 37995149571151622760857485)
              ·
                refine ⟨14248181089181858535321557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37995149571151622760857485 14248181089181858535321557)
                ·
                  refine ⟨333941744277699809421599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14248181089181858535321557 333941744277699809421599)
                  ·
                    rfl

theorem cell23_5853143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 7].length) (baseStart_5853143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853143 prefixEnd_5853143 := by exact prefixLift 5853143
  have htrace : WordTrace (prefixWord ++ tailWord_5853143) baseStart_5853143 baseEnd_5853143 := by
    simpa [prefixWord, tailWord_5853143, baseEnd_5853143] using wordTrace_append hprefix tailTrace_5853143
  have hstable : (prefixWord ++ tailWord_5853143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853143).length < 2 ^ (prefixWord ++ tailWord_5853143).sum := by decide
  have hdescent : baseEnd_5853143 < baseStart_5853143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853177 : List Nat := [1, 2, 1, 3, 1, 5, 2, 3, 5]
def baseStart_5853177 : Nat := 118140960795 + 5853177 * 2 ^ 59
def prefixEnd_5853177 : Nat := 4983230072969 + 3 ^ 40 * 5853177 * 2
def baseEnd_5853177 : Nat := 333943684093505683529915

theorem tailTrace_5853177 : CollatzResearch.WordTrace tailWord_5853177 prefixEnd_5853177 333943684093505683529915 := by
  unfold tailWord_5853177
  simp only [CollatzResearch.WordTrace]
  refine ⟨213482903515946846891061785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142321935677297897927374523 213482903515946846891061785)
  ·
    refine ⟨160112177636960135168296339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213482903515946846891061785 160112177636960135168296339)
    ·
      refine ⟨240168266455440202752444509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160112177636960135168296339 240168266455440202752444509)
      ·
        refine ⟨90063099920790076032166691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240168266455440202752444509 90063099920790076032166691)
        ·
          refine ⟨135094649881185114048250037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90063099920790076032166691 135094649881185114048250037)
          ·
            refine ⟨12665123426361104442023441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135094649881185114048250037 12665123426361104442023441)
            ·
              refine ⟨9498842569770828331517581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12665123426361104442023441 9498842569770828331517581)
              ·
                refine ⟨3562065963664060624319093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9498842569770828331517581 3562065963664060624319093)
                ·
                  refine ⟨333943684093505683529915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3562065963664060624319093 333943684093505683529915)
                  ·
                    rfl

theorem cell23_5853177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 5].length) (baseStart_5853177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853177 prefixEnd_5853177 := by exact prefixLift 5853177
  have htrace : WordTrace (prefixWord ++ tailWord_5853177) baseStart_5853177 baseEnd_5853177 := by
    simpa [prefixWord, tailWord_5853177, baseEnd_5853177] using wordTrace_append hprefix tailTrace_5853177
  have hstable : (prefixWord ++ tailWord_5853177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853177).length < 2 ^ (prefixWord ++ tailWord_5853177).sum := by decide
  have hdescent : baseEnd_5853177 < baseStart_5853177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853183 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_5853183 : Nat := 118140960795 + 5853183 * 2 ^ 59
def prefixEnd_5853183 : Nat := 4983230072969 + 3 ^ 40 * 5853183 * 2
def baseEnd_5853183 : Nat := 3005496237725478128294207

theorem tailTrace_5853183 : CollatzResearch.WordTrace tailWord_5853183 prefixEnd_5853183 3005496237725478128294207 := by
  unfold tailWord_5853183
  simp only [CollatzResearch.WordTrace]
  refine ⟨213483122353925109915780203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142322081569283406610520135 213483122353925109915780203)
  ·
    refine ⟨320224683530887664873670305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213483122353925109915780203 320224683530887664873670305)
    ·
      refine ⟨240168512648165748655252729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320224683530887664873670305 240168512648165748655252729)
      ·
        refine ⟨180126384486124311491439547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240168512648165748655252729 180126384486124311491439547)
        ·
          refine ⟨270189576729186467237159321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180126384486124311491439547 270189576729186467237159321)
          ·
            refine ⟨202642182546889850427869491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270189576729186467237159321 202642182546889850427869491)
            ·
              refine ⟨303963273820334775641804237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202642182546889850427869491 303963273820334775641804237)
              ·
                refine ⟨113986227682625540865676589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303963273820334775641804237 113986227682625540865676589)
                ·
                  refine ⟨42744835380984577824628721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113986227682625540865676589 42744835380984577824628721)
                  ·
                    refine ⟨32058626535738433368471541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42744835380984577824628721 32058626535738433368471541)
                    ·
                      refine ⟨3005496237725478128294207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32058626535738433368471541 3005496237725478128294207)
                      ·
                        rfl

theorem cell23_5853183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_5853183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853183 prefixEnd_5853183 := by exact prefixLift 5853183
  have htrace : WordTrace (prefixWord ++ tailWord_5853183) baseStart_5853183 baseEnd_5853183 := by
    simpa [prefixWord, tailWord_5853183, baseEnd_5853183] using wordTrace_append hprefix tailTrace_5853183
  have hstable : (prefixWord ++ tailWord_5853183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853183).length < 2 ^ (prefixWord ++ tailWord_5853183).sum := by decide
  have hdescent : baseEnd_5853183 < baseStart_5853183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853210 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_5853210 : Nat := 118140960795 + 5853210 * 2 ^ 59
def prefixEnd_5853210 : Nat := 4983230072969 + 3 ^ 40 * 5853210 * 2
def baseEnd_5853210 : Nat := 3005510101703149522656583

theorem tailTrace_5853210 : CollatzResearch.WordTrace tailWord_5853210 prefixEnd_5853210 3005510101703149522656583 := by
  unfold tailWord_5853210
  simp only [CollatzResearch.WordTrace]
  refine ⟨53371026781206823381753271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142322738083218195684675389 53371026781206823381753271)
  ·
    refine ⟨80056540171810235072629907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53371026781206823381753271 80056540171810235072629907)
    ·
      refine ⟨120084810257715352608944861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80056540171810235072629907 120084810257715352608944861)
      ·
        refine ⟨45031803846643257228354323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120084810257715352608944861 45031803846643257228354323)
        ·
          refine ⟨67547705769964885842531485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45031803846643257228354323 67547705769964885842531485)
          ·
            refine ⟨25330389663736832190949307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67547705769964885842531485 25330389663736832190949307)
            ·
              refine ⟨37995584495605248286423961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25330389663736832190949307 37995584495605248286423961)
              ·
                refine ⟨28496688371703936214817971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37995584495605248286423961 28496688371703936214817971)
                ·
                  refine ⟨42745032557555904322226957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28496688371703936214817971 42745032557555904322226957)
                  ·
                    refine ⟨16029387209083464120835109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42745032557555904322226957 16029387209083464120835109)
                    ·
                      refine ⟨3005510101703149522656583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16029387209083464120835109 3005510101703149522656583)
                      ·
                        rfl

theorem cell23_5853210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_5853210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853210 prefixEnd_5853210 := by exact prefixLift 5853210
  have htrace : WordTrace (prefixWord ++ tailWord_5853210) baseStart_5853210 baseEnd_5853210 := by
    simpa [prefixWord, tailWord_5853210, baseEnd_5853210] using wordTrace_append hprefix tailTrace_5853210
  have hstable : (prefixWord ++ tailWord_5853210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853210).length < 2 ^ (prefixWord ++ tailWord_5853210).sum := by decide
  have hdescent : baseEnd_5853210 < baseStart_5853210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853278 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_5853278 : Nat := 118140960795 + 5853278 * 2 ^ 59
def prefixEnd_5853278 : Nat := 4983230072969 + 3 ^ 40 * 5853278 * 2
def baseEnd_5853278 : Nat := 3005545018387655256606271

theorem tailTrace_5853278 : CollatzResearch.WordTrace tailWord_5853278 prefixEnd_5853278 3005545018387655256606271 := by
  unfold tailWord_5853278
  simp only [CollatzResearch.WordTrace]
  refine ⟨26685823411072617642561061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142324391525720627426992325 26685823411072617642561061)
  ·
    refine ⟨5003591889576115807980199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26685823411072617642561061 5003591889576115807980199)
    ·
      refine ⟨7505387834364173711970299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003591889576115807980199 7505387834364173711970299)
      ·
        refine ⟨11258081751546260567955449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505387834364173711970299 11258081751546260567955449)
        ·
          refine ⟨8443561313659695425966587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11258081751546260567955449 8443561313659695425966587)
          ·
            refine ⟨12665341970489543138949881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443561313659695425966587 12665341970489543138949881)
            ·
              refine ⟨9499006477867157354212411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12665341970489543138949881 9499006477867157354212411)
              ·
                refine ⟨14248509716800736031318617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9499006477867157354212411 14248509716800736031318617)
                ·
                  refine ⟨10686382287600552023488963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14248509716800736031318617 10686382287600552023488963)
                  ·
                    refine ⟨16029573431400828035233445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10686382287600552023488963 16029573431400828035233445)
                    ·
                      refine ⟨3005545018387655256606271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16029573431400828035233445 3005545018387655256606271)
                      ·
                        rfl

theorem cell23_5853278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_5853278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853278 prefixEnd_5853278 := by exact prefixLift 5853278
  have htrace : WordTrace (prefixWord ++ tailWord_5853278) baseStart_5853278 baseEnd_5853278 := by
    simpa [prefixWord, tailWord_5853278, baseEnd_5853278] using wordTrace_append hprefix tailTrace_5853278
  have hstable : (prefixWord ++ tailWord_5853278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853278).length < 2 ^ (prefixWord ++ tailWord_5853278).sum := by decide
  have hdescent : baseEnd_5853278 < baseStart_5853278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853317 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_5853317 : Nat := 118140960795 + 5853317 * 2 ^ 59
def prefixEnd_5853317 : Nat := 4983230072969 + 3 ^ 40 * 5853317 * 2
def baseEnd_5853317 : Nat := 3005565044133180604018591

theorem tailTrace_5853317 : CollatzResearch.WordTrace tailWord_5853317 prefixEnd_5853317 3005565044133180604018591 := by
  unfold tailWord_5853317
  simp only [CollatzResearch.WordTrace]
  refine ⟨213488009735439650801158205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142325339823626433867438803 213488009735439650801158205)
  ·
    refine ⟨80058003650789869050434327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213488009735439650801158205 80058003650789869050434327)
    ·
      refine ⟨120087005476184803575651491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80058003650789869050434327 120087005476184803575651491)
      ·
        refine ⟨180130508214277205363477237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120087005476184803575651491 180130508214277205363477237)
        ·
          refine ⟨16887235145088488002825991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180130508214277205363477237 16887235145088488002825991)
          ·
            refine ⟨25330852717632732004238987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16887235145088488002825991 25330852717632732004238987)
            ·
              refine ⟨37996279076449098006358481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25330852717632732004238987 37996279076449098006358481)
              ·
                refine ⟨28497209307336823504768861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37996279076449098006358481 28497209307336823504768861)
                ·
                  refine ⟨10686453490251308814288323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28497209307336823504768861 10686453490251308814288323)
                  ·
                    refine ⟨16029680235376963221432485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10686453490251308814288323 16029680235376963221432485)
                    ·
                      refine ⟨3005565044133180604018591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16029680235376963221432485 3005565044133180604018591)
                      ·
                        rfl

theorem cell23_5853317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_5853317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853317 prefixEnd_5853317 := by exact prefixLift 5853317
  have htrace : WordTrace (prefixWord ++ tailWord_5853317) baseStart_5853317 baseEnd_5853317 := by
    simpa [prefixWord, tailWord_5853317, baseEnd_5853317] using wordTrace_append hprefix tailTrace_5853317
  have hstable : (prefixWord ++ tailWord_5853317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853317).length < 2 ^ (prefixWord ++ tailWord_5853317).sum := by decide
  have hdescent : baseEnd_5853317 < baseStart_5853317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853338 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5853338 : Nat := 118140960795 + 5853338 * 2 ^ 59
def prefixEnd_5853338 : Nat := 4983230072969 + 3 ^ 40 * 5853338 * 2
def baseEnd_5853338 : Nat := 3005575827226925021855995

theorem tailTrace_5853338 : CollatzResearch.WordTrace tailWord_5853338 prefixEnd_5853338 3005575827226925021855995 := by
  unfold tailWord_5853338
  simp only [CollatzResearch.WordTrace]
  refine ⟨53372193917090892846918167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142325850445575714258448445 53372193917090892846918167)
  ·
    refine ⟨80058290875636339270377251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53372193917090892846918167 80058290875636339270377251)
    ·
      refine ⟨120087436313454508905565877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80058290875636339270377251 120087436313454508905565877)
      ·
        refine ⟨11258197154386360209896801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120087436313454508905565877 11258197154386360209896801)
        ·
          refine ⟨8443647865789770157422601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11258197154386360209896801 8443647865789770157422601)
          ·
            refine ⟨6332735899342327618066951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8443647865789770157422601 6332735899342327618066951)
            ·
              refine ⟨9499103849013491427100427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6332735899342327618066951 9499103849013491427100427)
              ·
                refine ⟨14248655773520237140650641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9499103849013491427100427 14248655773520237140650641)
                ·
                  refine ⟨10686491830140177855487981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14248655773520237140650641 10686491830140177855487981)
                  ·
                    refine ⟨4007434436302566695807993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10686491830140177855487981 4007434436302566695807993)
                    ·
                      refine ⟨3005575827226925021855995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4007434436302566695807993 3005575827226925021855995)
                      ·
                        rfl

theorem cell23_5853338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5853338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853338 prefixEnd_5853338 := by exact prefixLift 5853338
  have htrace : WordTrace (prefixWord ++ tailWord_5853338) baseStart_5853338 baseEnd_5853338 := by
    simpa [prefixWord, tailWord_5853338, baseEnd_5853338] using wordTrace_append hprefix tailTrace_5853338
  have hstable : (prefixWord ++ tailWord_5853338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853338).length < 2 ^ (prefixWord ++ tailWord_5853338).sum := by decide
  have hdescent : baseEnd_5853338 < baseStart_5853338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853348 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_5853348 : Nat := 118140960795 + 5853348 * 2 ^ 59
def prefixEnd_5853348 : Nat := 4983230072969 + 3 ^ 40 * 5853348 * 2
def baseEnd_5853348 : Nat := 1001860320677823327576983

theorem tailTrace_5853348 : CollatzResearch.WordTrace tailWord_5853348 prefixEnd_5853348 1001860320677823327576983 := by
  unfold tailWord_5853348
  simp only [CollatzResearch.WordTrace]
  refine ⟨106744570199163671547768349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142326093598884895397024465 106744570199163671547768349)
  ·
    refine ⟨40029213824686376830413131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106744570199163671547768349 40029213824686376830413131)
    ·
      refine ⟨60043820737029565245619697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40029213824686376830413131 60043820737029565245619697)
      ·
        refine ⟨45032865552772173934214773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60043820737029565245619697 45032865552772173934214773)
        ·
          refine ⟨4221831145572391306332635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45032865552772173934214773 4221831145572391306332635)
          ·
            refine ⟨6332746718358586959498953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221831145572391306332635 6332746718358586959498953)
            ·
              refine ⟨4749560038768940219624215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6332746718358586959498953 4749560038768940219624215)
              ·
                refine ⟨7124340058153410329436323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749560038768940219624215 7124340058153410329436323)
                ·
                  refine ⟨10686510087230115494154485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7124340058153410329436323 10686510087230115494154485)
                  ·
                    refine ⟨1001860320677823327576983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10686510087230115494154485 1001860320677823327576983)
                    ·
                      rfl

theorem cell23_5853348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_5853348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853348 prefixEnd_5853348 := by exact prefixLift 5853348
  have htrace : WordTrace (prefixWord ++ tailWord_5853348) baseStart_5853348 baseEnd_5853348 := by
    simpa [prefixWord, tailWord_5853348, baseEnd_5853348] using wordTrace_append hprefix tailTrace_5853348
  have hstable : (prefixWord ++ tailWord_5853348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853348).length < 2 ^ (prefixWord ++ tailWord_5853348).sum := by decide
  have hdescent : baseEnd_5853348 < baseStart_5853348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853351 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5853351 : Nat := 118140960795 + 5853351 * 2 ^ 59
def prefixEnd_5853351 : Nat := 4983230072969 + 3 ^ 40 * 5853351 * 2
def baseEnd_5853351 : Nat := 3005582502475433470993435

theorem tailTrace_5853351 : CollatzResearch.WordTrace tailWord_5853351 prefixEnd_5853351 3005582502475433470993435 := by
  unfold tailWord_5853351
  simp only [CollatzResearch.WordTrace]
  refine ⟨213489249817316474607895907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142326166544877649738597271 213489249817316474607895907)
  ·
    refine ⟨320233874725974711911843861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213489249817316474607895907 320233874725974711911843861)
    ·
      refine ⟨15010962877780064620867681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 320233874725974711911843861 15010962877780064620867681)
      ·
        refine ⟨11258222158335048465650761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15010962877780064620867681 11258222158335048465650761)
        ·
          refine ⟨8443666618751286349238071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11258222158335048465650761 8443666618751286349238071)
          ·
            refine ⟨12665499928126929523857107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443666618751286349238071 12665499928126929523857107)
            ·
              refine ⟨18998249892190394285785661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12665499928126929523857107 18998249892190394285785661)
              ·
                refine ⟨7124343709571397857169623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18998249892190394285785661 7124343709571397857169623)
                ·
                  refine ⟨10686515564357096785754435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7124343709571397857169623 10686515564357096785754435)
                  ·
                    refine ⟨16029773346535645178631653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10686515564357096785754435 16029773346535645178631653)
                    ·
                      refine ⟨3005582502475433470993435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16029773346535645178631653 3005582502475433470993435)
                      ·
                        rfl

theorem cell23_5853351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5853351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853351 prefixEnd_5853351 := by exact prefixLift 5853351
  have htrace : WordTrace (prefixWord ++ tailWord_5853351) baseStart_5853351 baseEnd_5853351 := by
    simpa [prefixWord, tailWord_5853351, baseEnd_5853351] using wordTrace_append hprefix tailTrace_5853351
  have hstable : (prefixWord ++ tailWord_5853351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853351).length < 2 ^ (prefixWord ++ tailWord_5853351).sum := by decide
  have hdescent : baseEnd_5853351 < baseStart_5853351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853357 : List Nat := [1, 5, 2, 1, 2, 2, 10]
def baseStart_5853357 : Nat := 118140960795 + 5853357 * 2 ^ 59
def prefixEnd_5853357 : Nat := 4983230072969 + 3 ^ 40 * 5853357 * 2
def baseEnd_5853357 : Nat := 37105994856288400586647

theorem tailTrace_5853357 : CollatzResearch.WordTrace tailWord_5853357 prefixEnd_5853357 37105994856288400586647 := by
  unfold tailWord_5853357
  simp only [CollatzResearch.WordTrace]
  refine ⟨213489468655294737632614325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142326312436863158421742883 213489468655294737632614325)
  ·
    refine ⟨20014637686433881653057593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213489468655294737632614325 20014637686433881653057593)
    ·
      refine ⟨15010978264825411239793195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20014637686433881653057593 15010978264825411239793195)
      ·
        refine ⟨22516467397238116859689793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15010978264825411239793195 22516467397238116859689793)
        ·
          refine ⟨16887350547928587644767345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22516467397238116859689793 16887350547928587644767345)
          ·
            refine ⟨12665512910946440733575509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16887350547928587644767345 12665512910946440733575509)
            ·
              refine ⟨37105994856288400586647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12665512910946440733575509 37105994856288400586647)
              ·
                rfl

theorem cell23_5853357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 10].length) (baseStart_5853357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853357 prefixEnd_5853357 := by exact prefixLift 5853357
  have htrace : WordTrace (prefixWord ++ tailWord_5853357) baseStart_5853357 baseEnd_5853357 := by
    simpa [prefixWord, tailWord_5853357, baseEnd_5853357] using wordTrace_append hprefix tailTrace_5853357
  have hstable : (prefixWord ++ tailWord_5853357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853357).length < 2 ^ (prefixWord ++ tailWord_5853357).sum := by decide
  have hdescent : baseEnd_5853357 < baseStart_5853357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853370 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_5853370 : Nat := 118140960795 + 5853370 * 2 ^ 59
def prefixEnd_5853370 : Nat := 4983230072969 + 3 ^ 40 * 5853370 * 2
def baseEnd_5853370 : Nat := 1001864086202622965551949

theorem tailTrace_5853370 : CollatzResearch.WordTrace tailWord_5853370 prefixEnd_5853370 1001864086202622965551949 := by
  unfold tailWord_5853370
  simp only [CollatzResearch.WordTrace]
  refine ⟨53372485701061910213209391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142326628536165093901891709 53372485701061910213209391)
  ·
    refine ⟨80058728551592865319814087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53372485701061910213209391 80058728551592865319814087)
    ·
      refine ⟨120088092827389297979721131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80058728551592865319814087 120088092827389297979721131)
      ·
        refine ⟨180132139241083946969581697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120088092827389297979721131 180132139241083946969581697)
        ·
          refine ⟨135099104430812960227186273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180132139241083946969581697 135099104430812960227186273)
          ·
            refine ⟨101324328323109720170389705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135099104430812960227186273 101324328323109720170389705)
            ·
              refine ⟨75993246242332290127792279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101324328323109720170389705 75993246242332290127792279)
              ·
                refine ⟨113989869363498435191688419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75993246242332290127792279 113989869363498435191688419)
                ·
                  refine ⟨170984804045247652787532629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113989869363498435191688419 170984804045247652787532629)
                  ·
                    refine ⟨1001864086202622965551949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170984804045247652787532629 1001864086202622965551949)
                    ·
                      rfl

theorem cell23_5853370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_5853370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853370 prefixEnd_5853370 := by exact prefixLift 5853370
  have htrace : WordTrace (prefixWord ++ tailWord_5853370) baseStart_5853370 baseEnd_5853370 := by
    simpa [prefixWord, tailWord_5853370, baseEnd_5853370] using wordTrace_append hprefix tailTrace_5853370
  have hstable : (prefixWord ++ tailWord_5853370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853370).length < 2 ^ (prefixWord ++ tailWord_5853370).sum := by decide
  have hdescent : baseEnd_5853370 < baseStart_5853370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853378 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_5853378 : Nat := 118140960795 + 5853378 * 2 ^ 59
def prefixEnd_5853378 : Nat := 4983230072969 + 3 ^ 40 * 5853378 * 2
def baseEnd_5853378 : Nat := 1001865455484368288451937

theorem tailTrace_5853378 : CollatzResearch.WordTrace tailWord_5853378 prefixEnd_5853378 1001865455484368288451937 := by
  unfold tailWord_5853378
  simp only [CollatzResearch.WordTrace]
  refine ⟨53372558647054664554782197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142326823058812438812752525 53372558647054664554782197)
  ·
    refine ⟨5003677373161374802010831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53372558647054664554782197 5003677373161374802010831)
    ·
      refine ⟨7505516059742062203016247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003677373161374802010831 7505516059742062203016247)
      ·
        refine ⟨11258274089613093304524371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505516059742062203016247 11258274089613093304524371)
        ·
          refine ⟨16887411134419639956786557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11258274089613093304524371 16887411134419639956786557)
          ·
            refine ⟨6332779175407364983794959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16887411134419639956786557 6332779175407364983794959)
            ·
              refine ⟨9499168763111047475692439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6332779175407364983794959 9499168763111047475692439)
              ·
                refine ⟨14248753144666571213538659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9499168763111047475692439 14248753144666571213538659)
                ·
                  refine ⟨21373129716999856820307989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14248753144666571213538659 21373129716999856820307989)
                  ·
                    refine ⟨1001865455484368288451937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21373129716999856820307989 1001865455484368288451937)
                    ·
                      rfl

theorem cell23_5853378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_5853378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853378 prefixEnd_5853378 := by exact prefixLift 5853378
  have htrace : WordTrace (prefixWord ++ tailWord_5853378) baseStart_5853378 baseEnd_5853378 := by
    simpa [prefixWord, tailWord_5853378, baseEnd_5853378] using wordTrace_append hprefix tailTrace_5853378
  have hstable : (prefixWord ++ tailWord_5853378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853378).length < 2 ^ (prefixWord ++ tailWord_5853378).sum := by decide
  have hdescent : baseEnd_5853378 < baseStart_5853378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853388 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5853388 : Nat := 118140960795 + 5853388 * 2 ^ 59
def prefixEnd_5853388 : Nat := 4983230072969 + 3 ^ 40 * 5853388 * 2
def baseEnd_5853388 : Nat := 3005601501259649826230765

theorem tailTrace_5853388 : CollatzResearch.WordTrace tailWord_5853388 prefixEnd_5853388 3005601501259649826230765 := by
  unfold tailWord_5853388
  simp only [CollatzResearch.WordTrace]
  refine ⟨106745299659091214963496409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142327066212121619951328545 106745299659091214963496409)
  ·
    refine ⟨80058974744318411222622307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106745299659091214963496409 80058974744318411222622307)
    ·
      refine ⟨120088462116477616833933461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80058974744318411222622307 120088462116477616833933461)
      ·
        refine ⟨5629146661709888289090631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120088462116477616833933461 5629146661709888289090631)
        ·
          refine ⟨8443719992564832433635947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629146661709888289090631 8443719992564832433635947)
          ·
            refine ⟨12665579988847248650453921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443719992564832433635947 12665579988847248650453921)
            ·
              refine ⟨9499184991635436487840441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12665579988847248650453921 9499184991635436487840441)
              ·
                refine ⟨7124388743726577365880331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9499184991635436487840441 7124388743726577365880331)
                ·
                  refine ⟨10686583115589866048820497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7124388743726577365880331 10686583115589866048820497)
                  ·
                    refine ⟨8014937336692399536615373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10686583115589866048820497 8014937336692399536615373)
                    ·
                      refine ⟨3005601501259649826230765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014937336692399536615373 3005601501259649826230765)
                      ·
                        rfl

theorem cell23_5853388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5853388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853388 prefixEnd_5853388 := by exact prefixLift 5853388
  have htrace : WordTrace (prefixWord ++ tailWord_5853388) baseStart_5853388 baseEnd_5853388 := by
    simpa [prefixWord, tailWord_5853388, baseEnd_5853388] using wordTrace_append hprefix tailTrace_5853388
  have hstable : (prefixWord ++ tailWord_5853388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853388).length < 2 ^ (prefixWord ++ tailWord_5853388).sum := by decide
  have hdescent : baseEnd_5853388 < baseStart_5853388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853427 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 3]
def baseStart_5853427 : Nat := 118140960795 + 5853427 * 2 ^ 59
def prefixEnd_5853427 : Nat := 4983230072969 + 3 ^ 40 * 5853427 * 2
def baseEnd_5853427 : Nat := 3005621527005175173643085

theorem tailTrace_5853427 : CollatzResearch.WordTrace tailWord_5853427 prefixEnd_5853427 3005621527005175173643085 := by
  unfold tailWord_5853427
  simp only [CollatzResearch.WordTrace]
  refine ⟨213492021765041139587662535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142328014510027426391775023 213492021765041139587662535)
  ·
    refine ⟨320238032647561709381493803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213492021765041139587662535 320238032647561709381493803)
    ·
      refine ⟨480357048971342564072240705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320238032647561709381493803 480357048971342564072240705)
      ·
        refine ⟨360267786728506923054180529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480357048971342564072240705 360267786728506923054180529)
        ·
          refine ⟨270200840046380192290635397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360267786728506923054180529 270200840046380192290635397)
          ·
            refine ⟨50662657508696286054494137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270200840046380192290635397 50662657508696286054494137)
            ·
              refine ⟨37996993131522214540870603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50662657508696286054494137 37996993131522214540870603)
              ·
                refine ⟨56995489697283321811305905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37996993131522214540870603 56995489697283321811305905)
                ·
                  refine ⟨42746617272962491358479429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56995489697283321811305905 42746617272962491358479429)
                  ·
                    refine ⟨8014990738680467129714893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42746617272962491358479429 8014990738680467129714893)
                    ·
                      refine ⟨3005621527005175173643085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8014990738680467129714893 3005621527005175173643085)
                      ·
                        rfl

theorem cell23_5853427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_5853427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853427 prefixEnd_5853427 := by exact prefixLift 5853427
  have htrace : WordTrace (prefixWord ++ tailWord_5853427) baseStart_5853427 baseEnd_5853427 := by
    simpa [prefixWord, tailWord_5853427, baseEnd_5853427] using wordTrace_append hprefix tailTrace_5853427
  have hstable : (prefixWord ++ tailWord_5853427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853427).length < 2 ^ (prefixWord ++ tailWord_5853427).sum := by decide
  have hdescent : baseEnd_5853427 < baseStart_5853427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853437 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_5853437 : Nat := 118140960795 + 5853437 * 2 ^ 59
def prefixEnd_5853437 : Nat := 4983230072969 + 3 ^ 40 * 5853437 * 2
def baseEnd_5853437 : Nat := 3005626661811720134518039

theorem tailTrace_5853437 : CollatzResearch.WordTrace tailWord_5853437 prefixEnd_5853437 3005626661811720134518039 := by
  unfold tailWord_5853437
  simp only [CollatzResearch.WordTrace]
  refine ⟨213492386495004911295526565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142328257663336607530351043 213492386495004911295526565)
  ·
    refine ⟨40029822467813420867911231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213492386495004911295526565 40029822467813420867911231)
    ·
      refine ⟨60044733701720131301866847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40029822467813420867911231 60044733701720131301866847)
      ·
        refine ⟨90067100552580196952800271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60044733701720131301866847 90067100552580196952800271)
        ·
          refine ⟨135100650828870295429200407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90067100552580196952800271 135100650828870295429200407)
          ·
            refine ⟨202650976243305443143800611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135100650828870295429200407 202650976243305443143800611)
            ·
              refine ⟨303976464364958164715700917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202650976243305443143800611 303976464364958164715700917)
              ·
                refine ⟨28497793534214827942096961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303976464364958164715700917 28497793534214827942096961)
                ·
                  refine ⟨21373345150661120956572721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28497793534214827942096961 21373345150661120956572721)
                  ·
                    refine ⟨16030008862995840717429541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21373345150661120956572721 16030008862995840717429541)
                    ·
                      refine ⟨3005626661811720134518039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16030008862995840717429541 3005626661811720134518039)
                      ·
                        rfl

theorem cell23_5853437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_5853437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853437 prefixEnd_5853437 := by exact prefixLift 5853437
  have htrace : WordTrace (prefixWord ++ tailWord_5853437) baseStart_5853437 baseEnd_5853437 := by
    simpa [prefixWord, tailWord_5853437, baseEnd_5853437] using wordTrace_append hprefix tailTrace_5853437
  have hstable : (prefixWord ++ tailWord_5853437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853437).length < 2 ^ (prefixWord ++ tailWord_5853437).sum := by decide
  have hdescent : baseEnd_5853437 < baseStart_5853437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853464 : List Nat := [2, 1, 2, 3, 1, 2, 2, 5, 5]
def baseStart_5853464 : Nat := 118140960795 + 5853464 * 2 ^ 59
def prefixEnd_5853464 : Nat := 4983230072969 + 3 ^ 40 * 5853464 * 2
def baseEnd_5853464 : Nat := 333960058421043503208935

theorem tailTrace_5853464 : CollatzResearch.WordTrace tailWord_5853464 prefixEnd_5853464 333960058421043503208935 := by
  unfold tailWord_5853464
  simp only [CollatzResearch.WordTrace]
  refine ⟨106746685632953547453379723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142328914177271396604506297 106746685632953547453379723)
  ·
    refine ⟨160120028449430321180069585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106746685632953547453379723 160120028449430321180069585)
    ·
      refine ⟨120090021337072740885052189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160120028449430321180069585 120090021337072740885052189)
      ·
        refine ⟨45033758001402277831894571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120090021337072740885052189 45033758001402277831894571)
        ·
          refine ⟨67550637002103416747841857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45033758001402277831894571 67550637002103416747841857)
          ·
            refine ⟨50662977751577562560881393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67550637002103416747841857 50662977751577562560881393)
            ·
              refine ⟨37997233313683171920661045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50662977751577562560881393 37997233313683171920661045)
              ·
                refine ⟨3562240623157797367561973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37997233313683171920661045 3562240623157797367561973)
                ·
                  refine ⟨333960058421043503208935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3562240623157797367561973 333960058421043503208935)
                  ·
                    rfl

theorem cell23_5853464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 5].length) (baseStart_5853464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853464 prefixEnd_5853464 := by exact prefixLift 5853464
  have htrace : WordTrace (prefixWord ++ tailWord_5853464) baseStart_5853464 baseEnd_5853464 := by
    simpa [prefixWord, tailWord_5853464, baseEnd_5853464] using wordTrace_append hprefix tailTrace_5853464
  have hstable : (prefixWord ++ tailWord_5853464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853464).length < 2 ^ (prefixWord ++ tailWord_5853464).sum := by decide
  have hdescent : baseEnd_5853464 < baseStart_5853464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853484 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 2, 5, 2]
def baseStart_5853484 : Nat := 118140960795 + 5853484 * 2 ^ 59
def prefixEnd_5853484 : Nat := 4983230072969 + 3 ^ 40 * 5853484 * 2
def baseEnd_5853484 : Nat := 3005650795402481450630323

theorem tailTrace_5853484 : CollatzResearch.WordTrace tailWord_5853484 prefixEnd_5853484 3005650795402481450630323 := by
  unfold tailWord_5853484
  simp only [CollatzResearch.WordTrace]
  refine ⟨106747050362917319161243753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142329400483889758881658337 106747050362917319161243753)
  ·
    refine ⟨80060287772187989370932815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106747050362917319161243753 80060287772187989370932815)
    ·
      refine ⟨120090431658281984056399223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80060287772187989370932815 120090431658281984056399223)
      ·
        refine ⟨180135647487422976084598835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120090431658281984056399223 180135647487422976084598835)
        ·
          refine ⟨270203471231134464126898253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180135647487422976084598835 270203471231134464126898253)
          ·
            refine ⟨101326301711675424047586845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270203471231134464126898253 101326301711675424047586845)
            ·
              refine ⟨37997363141878284017845067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101326301711675424047586845 37997363141878284017845067)
              ·
                refine ⟨56996044712817426026767601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37997363141878284017845067 56996044712817426026767601)
                ·
                  refine ⟨42747033534613069520075701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56996044712817426026767601 42747033534613069520075701)
                  ·
                    refine ⟨4007534393869975267507097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42747033534613069520075701 4007534393869975267507097)
                    ·
                      refine ⟨3005650795402481450630323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4007534393869975267507097 3005650795402481450630323)
                      ·
                        rfl

theorem cell23_5853484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_5853484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853484 prefixEnd_5853484 := by exact prefixLift 5853484
  have htrace : WordTrace (prefixWord ++ tailWord_5853484) baseStart_5853484 baseEnd_5853484 := by
    simpa [prefixWord, tailWord_5853484, baseEnd_5853484] using wordTrace_append hprefix tailTrace_5853484
  have hstable : (prefixWord ++ tailWord_5853484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853484).length < 2 ^ (prefixWord ++ tailWord_5853484).sum := by decide
  have hdescent : baseEnd_5853484 < baseStart_5853484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853487 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_5853487 : Nat := 118140960795 + 5853487 * 2 ^ 59
def prefixEnd_5853487 : Nat := 4983230072969 + 3 ^ 40 * 5853487 * 2
def baseEnd_5853487 : Nat := 3005652335844444938892809

theorem tailTrace_5853487 : CollatzResearch.WordTrace tailWord_5853487 prefixEnd_5853487 3005652335844444938892809 := by
  unfold tailWord_5853487
  simp only [CollatzResearch.WordTrace]
  refine ⟨213494210144823769834846715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142329473429882513223231143 213494210144823769834846715)
  ·
    refine ⟨320241315217235654752270073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213494210144823769834846715 320241315217235654752270073)
    ·
      refine ⟨240180986412926741064202555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320241315217235654752270073 240180986412926741064202555)
      ·
        refine ⟨360271479619390111596303833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240180986412926741064202555 360271479619390111596303833)
        ·
          refine ⟨270203609714542583697227875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360271479619390111596303833 270203609714542583697227875)
          ·
            refine ⟨405305414571813875545841813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270203609714542583697227875 405305414571813875545841813)
            ·
              refine ⟨18998691308053775416211335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 405305414571813875545841813 18998691308053775416211335)
              ·
                refine ⟨28498036962080663124317003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18998691308053775416211335 28498036962080663124317003)
                ·
                  refine ⟨42747055443120994686475505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28498036962080663124317003 42747055443120994686475505)
                  ·
                    refine ⟨32060291582340746014856629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42747055443120994686475505 32060291582340746014856629)
                    ·
                      refine ⟨3005652335844444938892809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32060291582340746014856629 3005652335844444938892809)
                      ·
                        rfl

theorem cell23_5853487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_5853487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853487 prefixEnd_5853487 := by exact prefixLift 5853487
  have htrace : WordTrace (prefixWord ++ tailWord_5853487) baseStart_5853487 baseEnd_5853487 := by
    simpa [prefixWord, tailWord_5853487, baseEnd_5853487] using wordTrace_append hprefix tailTrace_5853487
  have hstable : (prefixWord ++ tailWord_5853487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853487).length < 2 ^ (prefixWord ++ tailWord_5853487).sum := by decide
  have hdescent : baseEnd_5853487 < baseStart_5853487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853527 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_5853527 : Nat := 118140960795 + 5853527 * 2 ^ 59
def prefixEnd_5853527 : Nat := 4983230072969 + 3 ^ 40 * 5853527 * 2
def baseEnd_5853527 : Nat := 3005672875070624782392625

theorem tailTrace_5853527 : CollatzResearch.WordTrace tailWord_5853527 prefixEnd_5853527 3005672875070624782392625 := by
  unfold tailWord_5853527
  simp only [CollatzResearch.WordTrace]
  refine ⟨213495669064678856666302835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142330446043119237777535223 213495669064678856666302835)
  ·
    refine ⟨320243503597018284999454253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213495669064678856666302835 320243503597018284999454253)
    ·
      refine ⟨120091313848881856874795345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320243503597018284999454253 120091313848881856874795345)
      ·
        refine ⟨90068485386661392656096509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120091313848881856874795345 90068485386661392656096509)
        ·
          refine ⟨33775682019998022246036191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90068485386661392656096509 33775682019998022246036191)
          ·
            refine ⟨50663523029997033369054287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33775682019998022246036191 50663523029997033369054287)
            ·
              refine ⟨75995284544995550053581431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50663523029997033369054287 75995284544995550053581431)
              ·
                refine ⟨113992926817493325080372147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75995284544995550053581431 113992926817493325080372147)
                ·
                  refine ⟨170989390226239987620558221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113992926817493325080372147 170989390226239987620558221)
                  ·
                    refine ⟨64121021334839995357709333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170989390226239987620558221 64121021334839995357709333)
                    ·
                      refine ⟨3005672875070624782392625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64121021334839995357709333 3005672875070624782392625)
                      ·
                        rfl

theorem cell23_5853527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_5853527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853527 prefixEnd_5853527 := by exact prefixLift 5853527
  have htrace : WordTrace (prefixWord ++ tailWord_5853527) baseStart_5853527 baseEnd_5853527 := by
    simpa [prefixWord, tailWord_5853527, baseEnd_5853527] using wordTrace_append hprefix tailTrace_5853527
  have hstable : (prefixWord ++ tailWord_5853527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853527).length < 2 ^ (prefixWord ++ tailWord_5853527).sum := by decide
  have hdescent : baseEnd_5853527 < baseStart_5853527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853541 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_5853541 : Nat := 118140960795 + 5853541 * 2 ^ 59
def prefixEnd_5853541 : Nat := 4983230072969 + 3 ^ 40 * 5853541 * 2
def baseEnd_5853541 : Nat := 1001893354599929242539187

theorem tailTrace_5853541 : CollatzResearch.WordTrace tailWord_5853541 prefixEnd_5853541 1001893354599929242539187 := by
  unfold tailWord_5853541
  simp only [CollatzResearch.WordTrace]
  refine ⟨213496179686628137057312477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142330786457752091371541651 213496179686628137057312477)
  ·
    refine ⟨80061067382485551396492179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213496179686628137057312477 80061067382485551396492179)
    ·
      refine ⟨120091601073728327094738269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80061067382485551396492179 120091601073728327094738269)
      ·
        refine ⟨45034350402648122660526851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120091601073728327094738269 45034350402648122660526851)
        ·
          refine ⟨67551525603972183990790277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45034350402648122660526851 67551525603972183990790277)
          ·
            refine ⟨12665911050744784498273177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67551525603972183990790277 12665911050744784498273177)
            ·
              refine ⟨9499433288058588373704883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12665911050744784498273177 9499433288058588373704883)
              ·
                refine ⟨14249149932087882560557325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9499433288058588373704883 14249149932087882560557325)
                ·
                  refine ⟨5343431224532955960208997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14249149932087882560557325 5343431224532955960208997)
                  ·
                    refine ⟨1001893354599929242539187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5343431224532955960208997 1001893354599929242539187)
                    ·
                      rfl

theorem cell23_5853541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_5853541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853541 prefixEnd_5853541 := by exact prefixLift 5853541
  have htrace : WordTrace (prefixWord ++ tailWord_5853541) baseStart_5853541 baseEnd_5853541 := by
    simpa [prefixWord, tailWord_5853541, baseEnd_5853541] using wordTrace_append hprefix tailTrace_5853541
  have hstable : (prefixWord ++ tailWord_5853541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853541).length < 2 ^ (prefixWord ++ tailWord_5853541).sum := by decide
  have hdescent : baseEnd_5853541 < baseStart_5853541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853591 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 4, 3, 2]
def baseStart_5853591 : Nat := 118140960795 + 5853591 * 2 ^ 59
def prefixEnd_5853591 : Nat := 4983230072969 + 3 ^ 40 * 5853591 * 2
def baseEnd_5853591 : Nat := 3005705737832512531992331

theorem tailTrace_5853591 : CollatzResearch.WordTrace tailWord_5853591 prefixEnd_5853591 3005705737832512531992331 := by
  unfold tailWord_5853591
  simp only [CollatzResearch.WordTrace]
  refine ⟨213498003336446995596632627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142332002224297997064421751 213498003336446995596632627)
  ·
    refine ⟨320247005004670493394948941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213498003336446995596632627 320247005004670493394948941)
    ·
      refine ⟨120092626876751435023105853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320247005004670493394948941 120092626876751435023105853)
      ·
        refine ⟨45034735078781788133664695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120092626876751435023105853 45034735078781788133664695)
        ·
          refine ⟨67552102618172682200497043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45034735078781788133664695 67552102618172682200497043)
          ·
            refine ⟨101328153927259023300745565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67552102618172682200497043 101328153927259023300745565)
            ·
              refine ⟨37998057722722133737779587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101328153927259023300745565 37998057722722133737779587)
              ·
                refine ⟨56997086584083200606669381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37998057722722133737779587 56997086584083200606669381)
                ·
                  refine ⟨10686953734515600113750509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56997086584083200606669381 10686953734515600113750509)
                  ·
                    refine ⟨4007607650443350042656441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10686953734515600113750509 4007607650443350042656441)
                    ·
                      refine ⟨3005705737832512531992331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4007607650443350042656441 3005705737832512531992331)
                      ·
                        rfl

theorem cell23_5853591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_5853591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853591 prefixEnd_5853591 := by exact prefixLift 5853591
  have htrace : WordTrace (prefixWord ++ tailWord_5853591) baseStart_5853591 baseEnd_5853591 := by
    simpa [prefixWord, tailWord_5853591, baseEnd_5853591] using wordTrace_append hprefix tailTrace_5853591
  have hstable : (prefixWord ++ tailWord_5853591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853591).length < 2 ^ (prefixWord ++ tailWord_5853591).sum := by decide
  have hdescent : baseEnd_5853591 < baseStart_5853591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853641 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 3]
def baseStart_5853641 : Nat := 118140960795 + 5853641 * 2 ^ 59
def prefixEnd_5853641 : Nat := 4983230072969 + 3 ^ 40 * 5853641 * 2
def baseEnd_5853641 : Nat := 3005731411865237336367101

theorem tailTrace_5853641 : CollatzResearch.WordTrace tailWord_5853641 prefixEnd_5853641 3005731411865237336367101 := by
  unfold tailWord_5853641
  simp only [CollatzResearch.WordTrace]
  refine ⟨213499826986265854135952777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142333217990843902757301851 213499826986265854135952777)
  ·
    refine ⟨160124870239699390601964583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213499826986265854135952777 160124870239699390601964583)
    ·
      refine ⟨240187305359549085902946875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160124870239699390601964583 240187305359549085902946875)
      ·
        refine ⟨360280958039323628854420313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240187305359549085902946875 360280958039323628854420313)
        ·
          refine ⟨270210718529492721640815235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360280958039323628854420313 270210718529492721640815235)
          ·
            refine ⟨405316077794239082461222853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270210718529492721640815235 405316077794239082461222853)
            ·
              refine ⟨75996764586419827961479285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405316077794239082461222853 75996764586419827961479285)
              ·
                refine ⟨7124696679976858871388683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75996764586419827961479285 7124696679976858871388683)
                ·
                  refine ⟨10687045019965288307083025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7124696679976858871388683 10687045019965288307083025)
                  ·
                    refine ⟨8015283764973966230312269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10687045019965288307083025 8015283764973966230312269)
                    ·
                      refine ⟨3005731411865237336367101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8015283764973966230312269 3005731411865237336367101)
                      ·
                        rfl

theorem cell23_5853641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_5853641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853641 prefixEnd_5853641 := by exact prefixLift 5853641
  have htrace : WordTrace (prefixWord ++ tailWord_5853641) baseStart_5853641 baseEnd_5853641 := by
    simpa [prefixWord, tailWord_5853641, baseEnd_5853641] using wordTrace_append hprefix tailTrace_5853641
  have hstable : (prefixWord ++ tailWord_5853641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853641).length < 2 ^ (prefixWord ++ tailWord_5853641).sum := by decide
  have hdescent : baseEnd_5853641 < baseStart_5853641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853644 : List Nat := [2, 2, 1, 4, 3, 11]
def baseStart_5853644 : Nat := 118140960795 + 5853644 * 2 ^ 59
def prefixEnd_5853644 : Nat := 4983230072969 + 3 ^ 40 * 5853644 * 2
def baseEnd_5853644 : Nat := 12369271408671608331809

theorem tailTrace_5853644 : CollatzResearch.WordTrace tailWord_5853644 prefixEnd_5853644 12369271408671608331809 := by
  unfold tailWord_5853644
  simp only [CollatzResearch.WordTrace]
  refine ⟨106749968202627492824155993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142333290936836657098874657 106749968202627492824155993)
  ·
    refine ⟨80062476151970619618116995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106749968202627492824155993 80062476151970619618116995)
    ·
      refine ⟨120093714227955929427175493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80062476151970619618116995 120093714227955929427175493)
      ·
        refine ⟨22517571417741736767595405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120093714227955929427175493 22517571417741736767595405)
        ·
          refine ⟨8444089281653151287848277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22517571417741736767595405 8444089281653151287848277)
          ·
            refine ⟨12369271408671608331809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8444089281653151287848277 12369271408671608331809)
            ·
              rfl

theorem cell23_5853644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 11].length) (baseStart_5853644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853644 prefixEnd_5853644 := by exact prefixLift 5853644
  have htrace : WordTrace (prefixWord ++ tailWord_5853644) baseStart_5853644 baseEnd_5853644 := by
    simpa [prefixWord, tailWord_5853644, baseEnd_5853644] using wordTrace_append hprefix tailTrace_5853644
  have hstable : (prefixWord ++ tailWord_5853644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853644).length < 2 ^ (prefixWord ++ tailWord_5853644).sum := by decide
  have hdescent : baseEnd_5853644 < baseStart_5853644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853711 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 5, 4, 2]
def baseStart_5853711 : Nat := 118140960795 + 5853711 * 2 ^ 59
def prefixEnd_5853711 : Nat := 4983230072969 + 3 ^ 40 * 5853711 * 2
def baseEnd_5853711 : Nat := 3005767355511052062491779

theorem tailTrace_5853711 : CollatzResearch.WordTrace tailWord_5853711 prefixEnd_5853711 3005767355511052062491779 := by
  unfold tailWord_5853711
  simp only [CollatzResearch.WordTrace]
  refine ⟨213502380096012256091000987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142334920064008170727333991 213502380096012256091000987)
  ·
    refine ⟨320253570144018384136501481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213502380096012256091000987 320253570144018384136501481)
    ·
      refine ⟨240190177608013788102376111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320253570144018384136501481 240190177608013788102376111)
      ·
        refine ⟨360285266412020682153564167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240190177608013788102376111 360285266412020682153564167)
        ·
          refine ⟨540427899618031023230346251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360285266412020682153564167 540427899618031023230346251)
          ·
            refine ⟨810641849427046534845519377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540427899618031023230346251 810641849427046534845519377)
            ·
              refine ⟨607981387070284901134139533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810641849427046534845519377 607981387070284901134139533)
              ·
                refine ⟨227993020151356837925302325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607981387070284901134139533 227993020151356837925302325)
                ·
                  refine ⟨21374345639189703555497093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227993020151356837925302325 21374345639189703555497093)
                  ·
                    refine ⟨4007689807348069416655705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21374345639189703555497093 4007689807348069416655705)
                    ·
                      refine ⟨3005767355511052062491779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4007689807348069416655705 3005767355511052062491779)
                      ·
                        rfl

theorem cell23_5853711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4, 2].length) (baseStart_5853711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853711 prefixEnd_5853711 := by exact prefixLift 5853711
  have htrace : WordTrace (prefixWord ++ tailWord_5853711) baseStart_5853711 baseEnd_5853711 := by
    simpa [prefixWord, tailWord_5853711, baseEnd_5853711] using wordTrace_append hprefix tailTrace_5853711
  have hstable : (prefixWord ++ tailWord_5853711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853711).length < 2 ^ (prefixWord ++ tailWord_5853711).sum := by decide
  have hdescent : baseEnd_5853711 < baseStart_5853711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853811 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 7, 4]
def baseStart_5853811 : Nat := 118140960795 + 5853811 * 2 ^ 59
def prefixEnd_5853811 : Nat := 4983230072969 + 3 ^ 40 * 5853811 * 2
def baseEnd_5853811 : Nat := 1001939567858833890413773

theorem tailTrace_5853811 : CollatzResearch.WordTrace tailWord_5853811 prefixEnd_5853811 1001939567858833890413773 := by
  unfold tailWord_5853811
  simp only [CollatzResearch.WordTrace]
  refine ⟨213506027395649973169641287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142337351597099982113094191 213506027395649973169641287)
  ·
    refine ⟨320259041093474959754461931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213506027395649973169641287 320259041093474959754461931)
    ·
      refine ⟨480388561640212439631692897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320259041093474959754461931 480388561640212439631692897)
      ·
        refine ⟨360291421230159329723769673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480388561640212439631692897 360291421230159329723769673)
        ·
          refine ⟨270218565922619497292827255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360291421230159329723769673 270218565922619497292827255)
          ·
            refine ⟨405327848883929245939240883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270218565922619497292827255 405327848883929245939240883)
            ·
              refine ⟨607991773325893868908861325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405327848883929245939240883 607991773325893868908861325)
              ·
                refine ⟨227996914997210200840822997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607991773325893868908861325 227996914997210200840822997)
                ·
                  refine ⟨5343677695247114082206789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 227996914997210200840822997 5343677695247114082206789)
                  ·
                    refine ⟨1001939567858833890413773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5343677695247114082206789 1001939567858833890413773)
                    ·
                      rfl

theorem cell23_5853811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 4].length) (baseStart_5853811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853811 prefixEnd_5853811 := by exact prefixLift 5853811
  have htrace : WordTrace (prefixWord ++ tailWord_5853811) baseStart_5853811 baseEnd_5853811 := by
    simpa [prefixWord, tailWord_5853811, baseEnd_5853811] using wordTrace_append hprefix tailTrace_5853811
  have hstable : (prefixWord ++ tailWord_5853811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853811).length < 2 ^ (prefixWord ++ tailWord_5853811).sum := by decide
  have hdescent : baseEnd_5853811 < baseStart_5853811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853838 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5853838 : Nat := 118140960795 + 5853838 * 2 ^ 59
def prefixEnd_5853838 : Nat := 4983230072969 + 3 ^ 40 * 5853838 * 2
def baseEnd_5853838 : Nat := 3005832567554173065603695

theorem tailTrace_5853838 : CollatzResearch.WordTrace tailWord_5853838 prefixEnd_5853838 3005832567554173065603695 := by
  unfold tailWord_5853838
  simp only [CollatzResearch.WordTrace]
  refine ⟨26688376520819019597609271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142338008111034771187249445 26688376520819019597609271)
  ·
    refine ⟨40032564781228529396413907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26688376520819019597609271 40032564781228529396413907)
    ·
      refine ⟨60048847171842794094620861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40032564781228529396413907 60048847171842794094620861)
      ·
        refine ⟨22518317689441047785482823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60048847171842794094620861 22518317689441047785482823)
        ·
          refine ⟨33777476534161571678224235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22518317689441047785482823 33777476534161571678224235)
          ·
            refine ⟨50666214801242357517336353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33777476534161571678224235 50666214801242357517336353)
            ·
              refine ⟨37999661100931768138002265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50666214801242357517336353 37999661100931768138002265)
              ·
                refine ⟨28499745825698826103501699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37999661100931768138002265 28499745825698826103501699)
                ·
                  refine ⟨42749618738548239155252549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28499745825698826103501699 42749618738548239155252549)
                  ·
                    refine ⟨8015553513477794841609853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42749618738548239155252549 8015553513477794841609853)
                    ·
                      refine ⟨3005832567554173065603695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8015553513477794841609853 3005832567554173065603695)
                      ·
                        rfl

theorem cell23_5853838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5853838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853838 prefixEnd_5853838 := by exact prefixLift 5853838
  have htrace : WordTrace (prefixWord ++ tailWord_5853838) baseStart_5853838 baseEnd_5853838 := by
    simpa [prefixWord, tailWord_5853838, baseEnd_5853838] using wordTrace_append hprefix tailTrace_5853838
  have hstable : (prefixWord ++ tailWord_5853838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853838).length < 2 ^ (prefixWord ++ tailWord_5853838).sum := by decide
  have hdescent : baseEnd_5853838 < baseStart_5853838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853885 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_5853885 : Nat := 118140960795 + 5853885 * 2 ^ 59
def prefixEnd_5853885 : Nat := 4983230072969 + 3 ^ 40 * 5853885 * 2
def baseEnd_5853885 : Nat := 3005856701144934381715979

theorem tailTrace_5853885 : CollatzResearch.WordTrace tailWord_5853885 prefixEnd_5853885 3005856701144934381715979 := by
  unfold tailWord_5853885
  simp only [CollatzResearch.WordTrace]
  refine ⟨213508726397381883807835109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142339150931587922538556739 213508726397381883807835109)
  ·
    refine ⟨40032886199509103213969083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213508726397381883807835109 40032886199509103213969083)
    ·
      refine ⟨60049329299263654820953625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40032886199509103213969083 60049329299263654820953625)
      ·
        refine ⟨45036996974447741115715219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60049329299263654820953625 45036996974447741115715219)
        ·
          refine ⟨67555495461671611673572829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45036996974447741115715219 67555495461671611673572829)
          ·
            refine ⟨25333310798126854377589811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67555495461671611673572829 25333310798126854377589811)
            ·
              refine ⟨37999966197190281566384717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25333310798126854377589811 37999966197190281566384717)
              ·
                refine ⟨14249987323946355587394269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37999966197190281566384717 14249987323946355587394269)
                ·
                  refine ⟨5343745246479883345272851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14249987323946355587394269 5343745246479883345272851)
                  ·
                    refine ⟨8015617869719825017909277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5343745246479883345272851 8015617869719825017909277)
                    ·
                      refine ⟨3005856701144934381715979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8015617869719825017909277 3005856701144934381715979)
                      ·
                        rfl

theorem cell23_5853885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_5853885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853885 prefixEnd_5853885 := by exact prefixLift 5853885
  have htrace : WordTrace (prefixWord ++ tailWord_5853885) baseStart_5853885 baseEnd_5853885 := by
    simpa [prefixWord, tailWord_5853885, baseEnd_5853885] using wordTrace_append hprefix tailTrace_5853885
  have hstable : (prefixWord ++ tailWord_5853885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853885).length < 2 ^ (prefixWord ++ tailWord_5853885).sum := by decide
  have hdescent : baseEnd_5853885 < baseStart_5853885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853919 : List Nat := [1, 1, 2, 3, 2, 5, 1, 3, 1, 1, 3]
def baseStart_5853919 : Nat := 118140960795 + 5853919 * 2 ^ 59
def prefixEnd_5853919 : Nat := 4983230072969 + 3 ^ 40 * 5853919 * 2
def baseEnd_5853919 : Nat := 3005874159487187248690823

theorem tailTrace_5853919 : CollatzResearch.WordTrace tailWord_5853919 prefixEnd_5853919 3005874159487187248690823 := by
  unfold tailWord_5853919
  simp only [CollatzResearch.WordTrace]
  refine ⟨213509966479258707614572811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142339977652839138409715207 213509966479258707614572811)
  ·
    refine ⟨320264949718888061421859217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213509966479258707614572811 320264949718888061421859217)
    ·
      refine ⟨240198712289166046066394413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320264949718888061421859217 240198712289166046066394413)
      ·
        refine ⟨90074517108437267274897905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240198712289166046066394413 90074517108437267274897905)
        ·
          refine ⟨67555887831327950456173429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90074517108437267274897905 67555887831327950456173429)
          ·
            refine ⟨6333364484186995355266259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67555887831327950456173429 6333364484186995355266259)
            ·
              refine ⟨9500046726280493032899389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6333364484186995355266259 9500046726280493032899389)
              ·
                refine ⟨3562517522355184887337271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9500046726280493032899389 3562517522355184887337271)
                ·
                  refine ⟨5343776283532777331005907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3562517522355184887337271 5343776283532777331005907)
                  ·
                    refine ⟨8015664425299165996508861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5343776283532777331005907 8015664425299165996508861)
                    ·
                      refine ⟨3005874159487187248690823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8015664425299165996508861 3005874159487187248690823)
                      ·
                        rfl

theorem cell23_5853919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_5853919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853919 prefixEnd_5853919 := by exact prefixLift 5853919
  have htrace : WordTrace (prefixWord ++ tailWord_5853919) baseStart_5853919 baseEnd_5853919 := by
    simpa [prefixWord, tailWord_5853919, baseEnd_5853919] using wordTrace_append hprefix tailTrace_5853919
  have hstable : (prefixWord ++ tailWord_5853919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853919).length < 2 ^ (prefixWord ++ tailWord_5853919).sum := by decide
  have hdescent : baseEnd_5853919 < baseStart_5853919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853925 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_5853925 : Nat := 118140960795 + 5853925 * 2 ^ 59
def prefixEnd_5853925 : Nat := 4983230072969 + 3 ^ 40 * 5853925 * 2
def baseEnd_5853925 : Nat := 3005877240371114225215795

theorem tailTrace_5853925 : CollatzResearch.WordTrace tailWord_5853925 prefixEnd_5853925 3005877240371114225215795 := by
  unfold tailWord_5853925
  simp only [CollatzResearch.WordTrace]
  refine ⟨213510185317236970639291229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142340123544824647092860819 213510185317236970639291229)
  ·
    refine ⟨80066319493963863989734211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213510185317236970639291229 80066319493963863989734211)
    ·
      refine ⟨120099479240945795984601317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80066319493963863989734211 120099479240945795984601317)
      ·
        refine ⟨22518652357677336747112747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120099479240945795984601317 22518652357677336747112747)
        ·
          refine ⟨33777978536516005120669121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22518652357677336747112747 33777978536516005120669121)
          ·
            refine ⟨25333483902387003840501841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33777978536516005120669121 25333483902387003840501841)
            ·
              refine ⟨19000112926790252880376381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25333483902387003840501841 19000112926790252880376381)
              ·
                refine ⟨7125042347546344830141143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19000112926790252880376381 7125042347546344830141143)
                ·
                  refine ⟨10687563521319517245211715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7125042347546344830141143 10687563521319517245211715)
                  ·
                    refine ⟨16031345281979275867817573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10687563521319517245211715 16031345281979275867817573)
                    ·
                      refine ⟨3005877240371114225215795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16031345281979275867817573 3005877240371114225215795)
                      ·
                        rfl

theorem cell23_5853925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_5853925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853925 prefixEnd_5853925 := by exact prefixLift 5853925
  have htrace : WordTrace (prefixWord ++ tailWord_5853925) baseStart_5853925 baseEnd_5853925 := by
    simpa [prefixWord, tailWord_5853925, baseEnd_5853925] using wordTrace_append hprefix tailTrace_5853925
  have hstable : (prefixWord ++ tailWord_5853925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853925).length < 2 ^ (prefixWord ++ tailWord_5853925).sum := by decide
  have hdescent : baseEnd_5853925 < baseStart_5853925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853938 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5853938 : Nat := 118140960795 + 5853938 * 2 ^ 59
def prefixEnd_5853938 : Nat := 4983230072969 + 3 ^ 40 * 5853938 * 2
def baseEnd_5853938 : Nat := 3005883915619622674353235

theorem tailTrace_5853938 : CollatzResearch.WordTrace tailWord_5853938 prefixEnd_5853938 3005883915619622674353235 := by
  unfold tailWord_5853938
  simp only [CollatzResearch.WordTrace]
  refine ⟨53377664866547468464878617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142340439644126582573009645 53377664866547468464878617)
  ·
    refine ⟨40033248649910601348658963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53377664866547468464878617 40033248649910601348658963)
    ·
      refine ⟨60049872974865902022988445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40033248649910601348658963 60049872974865902022988445)
      ·
        refine ⟨22518702365574713258620667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60049872974865902022988445 22518702365574713258620667)
        ·
          refine ⟨33778053548362069887931001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22518702365574713258620667 33778053548362069887931001)
          ·
            refine ⟨25333540161271552415948251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33778053548362069887931001 25333540161271552415948251)
            ·
              refine ⟨38000310241907328623922377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25333540161271552415948251 38000310241907328623922377)
              ·
                refine ⟨28500232681430496467941783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38000310241907328623922377 28500232681430496467941783)
                ·
                  refine ⟨42750349022145744701912675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28500232681430496467941783 42750349022145744701912675)
                  ·
                    refine ⟨64125523533218617052869013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42750349022145744701912675 64125523533218617052869013)
                    ·
                      refine ⟨3005883915619622674353235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64125523533218617052869013 3005883915619622674353235)
                      ·
                        rfl

theorem cell23_5853938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5853938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853938 prefixEnd_5853938 := by exact prefixLift 5853938
  have htrace : WordTrace (prefixWord ++ tailWord_5853938) baseStart_5853938 baseEnd_5853938 := by
    simpa [prefixWord, tailWord_5853938, baseEnd_5853938] using wordTrace_append hprefix tailTrace_5853938
  have hstable : (prefixWord ++ tailWord_5853938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853938).length < 2 ^ (prefixWord ++ tailWord_5853938).sum := by decide
  have hdescent : baseEnd_5853938 < baseStart_5853938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853948 : List Nat := [2, 2, 2, 1, 3, 3, 2, 8]
def baseStart_5853948 : Nat := 118140960795 + 5853948 * 2 ^ 59
def prefixEnd_5853948 : Nat := 4983230072969 + 3 ^ 40 * 5853948 * 2
def baseEnd_5853948 : Nat := 111329224089858060564007

theorem tailTrace_5853948 : CollatzResearch.WordTrace tailWord_5853948 prefixEnd_5853948 111329224089858060564007 := by
  unfold tailWord_5853948
  simp only [CollatzResearch.WordTrace]
  refine ⟨106755512098076822783689249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142340682797435763711585665 106755512098076822783689249)
  ·
    refine ⟨80066634073557617087766937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106755512098076822783689249 80066634073557617087766937)
    ·
      refine ⟨60049975555168212815825203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80066634073557617087766937 60049975555168212815825203)
      ·
        refine ⟨90074963332752319223737805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60049975555168212815825203 90074963332752319223737805)
        ·
          refine ⟨33778111249782119708901677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90074963332752319223737805 33778111249782119708901677)
          ·
            refine ⟨12666791718668294890838129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33778111249782119708901677 12666791718668294890838129)
            ·
              refine ⟨9500093789001221168128597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12666791718668294890838129 9500093789001221168128597)
              ·
                refine ⟨111329224089858060564007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9500093789001221168128597 111329224089858060564007)
                ·
                  rfl

theorem cell23_5853948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 8].length) (baseStart_5853948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853948 prefixEnd_5853948 := by exact prefixLift 5853948
  have htrace : WordTrace (prefixWord ++ tailWord_5853948) baseStart_5853948 baseEnd_5853948 := by
    simpa [prefixWord, tailWord_5853948, baseEnd_5853948] using wordTrace_append hprefix tailTrace_5853948
  have hstable : (prefixWord ++ tailWord_5853948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853948).length < 2 ^ (prefixWord ++ tailWord_5853948).sum := by decide
  have hdescent : baseEnd_5853948 < baseStart_5853948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853951 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_5853951 : Nat := 118140960795 + 5853951 * 2 ^ 59
def prefixEnd_5853951 : Nat := 4983230072969 + 3 ^ 40 * 5853951 * 2
def baseEnd_5853951 : Nat := 3005890590868131123490675

theorem tailTrace_5853951 : CollatzResearch.WordTrace tailWord_5853951 prefixEnd_5853951 3005890590868131123490675 := by
  unfold tailWord_5853951
  simp only [CollatzResearch.WordTrace]
  refine ⟨213511133615142777079737707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142340755743428518053158471 213511133615142777079737707)
  ·
    refine ⟨320266700422714165619606561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213511133615142777079737707 320266700422714165619606561)
    ·
      refine ⟨240200025317035624214704921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320266700422714165619606561 240200025317035624214704921)
      ·
        refine ⟨180150018987776718161028691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240200025317035624214704921 180150018987776718161028691)
        ·
          refine ⟨270225028481665077241543037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180150018987776718161028691 270225028481665077241543037)
          ·
            refine ⟨101334385680624403965578639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270225028481665077241543037 101334385680624403965578639)
            ·
              refine ⟨152001578520936605948367959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101334385680624403965578639 152001578520936605948367959)
              ·
                refine ⟨228002367781404908922551939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152001578520936605948367959 228002367781404908922551939)
                ·
                  refine ⟨342003551672107363383827909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228002367781404908922551939 342003551672107363383827909)
                  ·
                    refine ⟨64125665938520130634467733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342003551672107363383827909 64125665938520130634467733)
                    ·
                      refine ⟨3005890590868131123490675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64125665938520130634467733 3005890590868131123490675)
                      ·
                        rfl

theorem cell23_5853951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_5853951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5853951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5853951 prefixEnd_5853951 := by exact prefixLift 5853951
  have htrace : WordTrace (prefixWord ++ tailWord_5853951) baseStart_5853951 baseEnd_5853951 := by
    simpa [prefixWord, tailWord_5853951, baseEnd_5853951] using wordTrace_append hprefix tailTrace_5853951
  have hstable : (prefixWord ++ tailWord_5853951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853951).length < 2 ^ (prefixWord ++ tailWord_5853951).sum := by decide
  have hdescent : baseEnd_5853951 < baseStart_5853951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854008 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 2, 6]
def baseStart_5854008 : Nat := 118140960795 + 5854008 * 2 ^ 59
def prefixEnd_5854008 : Nat := 4983230072969 + 3 ^ 40 * 5854008 * 2
def baseEnd_5854008 : Nat := 1001973286421812466825971

theorem tailTrace_5854008 : CollatzResearch.WordTrace tailWord_5854008 prefixEnd_5854008 1001973286421812466825971 := by
  unfold tailWord_5854008
  simp only [CollatzResearch.WordTrace]
  refine ⟨106756606287968137907281339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142342141717290850543041785 106756606287968137907281339)
  ·
    refine ⟨160134909431952206860922009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106756606287968137907281339 160134909431952206860922009)
    ·
      refine ⟨120101182073964155145691507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160134909431952206860922009 120101182073964155145691507)
      ·
        refine ⟨180151773110946232718537261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120101182073964155145691507 180151773110946232718537261)
        ·
          refine ⟨67556914916604837269451473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180151773110946232718537261 67556914916604837269451473)
          ·
            refine ⟨50667686187453627952088605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67556914916604837269451473 50667686187453627952088605)
            ·
              refine ⟨19000382320295110482033227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50667686187453627952088605 19000382320295110482033227)
              ·
                refine ⟨28500573480442665723049841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19000382320295110482033227 28500573480442665723049841)
                ·
                  refine ⟨21375430110331999292287381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28500573480442665723049841 21375430110331999292287381)
                  ·
                    refine ⟨1001973286421812466825971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21375430110331999292287381 1001973286421812466825971)
                    ·
                      rfl

theorem cell23_5854008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_5854008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854008 prefixEnd_5854008 := by exact prefixLift 5854008
  have htrace : WordTrace (prefixWord ++ tailWord_5854008) baseStart_5854008 baseEnd_5854008 := by
    simpa [prefixWord, tailWord_5854008, baseEnd_5854008] using wordTrace_append hprefix tailTrace_5854008
  have hstable : (prefixWord ++ tailWord_5854008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854008).length < 2 ^ (prefixWord ++ tailWord_5854008).sum := by decide
  have hdescent : baseEnd_5854008 < baseStart_5854008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854055 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 7]
def baseStart_5854055 : Nat := 118140960795 + 5854055 * 2 ^ 59
def prefixEnd_5854055 : Nat := 4983230072969 + 3 ^ 40 * 5854055 * 2
def baseEnd_5854055 : Nat := 333993776984022079621133

theorem tailTrace_5854055 : CollatzResearch.WordTrace tailWord_5854055 prefixEnd_5854055 333993776984022079621133 := by
  unfold tailWord_5854055
  simp only [CollatzResearch.WordTrace]
  refine ⟨213514926806766002841523619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142343284537844001894349079 213514926806766002841523619)
  ·
    refine ⟨320272390210149004262285429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213514926806766002841523619 320272390210149004262285429)
    ·
      refine ⟨30025536582201469149589259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320272390210149004262285429 30025536582201469149589259)
      ·
        refine ⟨45038304873302203724383889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30025536582201469149589259 45038304873302203724383889)
        ·
          refine ⟨33778728654976652793287917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45038304873302203724383889 33778728654976652793287917)
          ·
            refine ⟨12667023245616244797482969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33778728654976652793287917 12667023245616244797482969)
            ·
              refine ⟨9500267434212183598112227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12667023245616244797482969 9500267434212183598112227)
              ·
                refine ⟨14250401151318275397168341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9500267434212183598112227 14250401151318275397168341)
                ·
                  refine ⟨333993776984022079621133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14250401151318275397168341 333993776984022079621133)
                  ·
                    rfl

theorem cell23_5854055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 7].length) (baseStart_5854055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854055 prefixEnd_5854055 := by exact prefixLift 5854055
  have htrace : WordTrace (prefixWord ++ tailWord_5854055) baseStart_5854055 baseEnd_5854055 := by
    simpa [prefixWord, tailWord_5854055, baseEnd_5854055] using wordTrace_append hprefix tailTrace_5854055
  have hstable : (prefixWord ++ tailWord_5854055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854055).length < 2 ^ (prefixWord ++ tailWord_5854055).sum := by decide
  have hdescent : baseEnd_5854055 < baseStart_5854055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854065 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_5854065 : Nat := 118140960795 + 5854065 * 2 ^ 59
def prefixEnd_5854065 : Nat := 4983230072969 + 3 ^ 40 * 5854065 * 2
def baseEnd_5854065 : Nat := 3005949127662743677465151

theorem tailTrace_5854065 : CollatzResearch.WordTrace tailWord_5854065 prefixEnd_5854065 3005949127662743677465151 := by
  unfold tailWord_5854065
  simp only [CollatzResearch.WordTrace]
  refine ⟨213515291536729774549387649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142343527691153183032925099 213515291536729774549387649)
  ·
    refine ⟨160136468652547330912040737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213515291536729774549387649 160136468652547330912040737)
    ·
      refine ⟨120102351489410498184030553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160136468652547330912040737 120102351489410498184030553)
      ·
        refine ⟨90076763617057873638022915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120102351489410498184030553 90076763617057873638022915)
        ·
          refine ⟨135115145425586810457034373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90076763617057873638022915 135115145425586810457034373)
          ·
            refine ⟨25334089767297526960693945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135115145425586810457034373 25334089767297526960693945)
            ·
              refine ⟨19000567325473145220520459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25334089767297526960693945 19000567325473145220520459)
              ·
                refine ⟨28500850988209717830780689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19000567325473145220520459 28500850988209717830780689)
                ·
                  refine ⟨21375638241157288373085517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28500850988209717830780689 21375638241157288373085517)
                  ·
                    refine ⟨8015864340433983139907069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21375638241157288373085517 8015864340433983139907069)
                    ·
                      refine ⟨3005949127662743677465151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8015864340433983139907069 3005949127662743677465151)
                      ·
                        rfl

theorem cell23_5854065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_5854065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854065 prefixEnd_5854065 := by exact prefixLift 5854065
  have htrace : WordTrace (prefixWord ++ tailWord_5854065) baseStart_5854065 baseEnd_5854065 := by
    simpa [prefixWord, tailWord_5854065, baseEnd_5854065] using wordTrace_append hprefix tailTrace_5854065
  have hstable : (prefixWord ++ tailWord_5854065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854065).length < 2 ^ (prefixWord ++ tailWord_5854065).sum := by decide
  have hdescent : baseEnd_5854065 < baseStart_5854065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854075 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 2, 5, 2]
def baseStart_5854075 : Nat := 118140960795 + 5854075 * 2 ^ 59
def prefixEnd_5854075 : Nat := 4983230072969 + 3 ^ 40 * 5854075 * 2
def baseEnd_5854075 : Nat := 3005954262469288638340105

theorem tailTrace_5854075 : CollatzResearch.WordTrace tailWord_5854075 prefixEnd_5854075 3005954262469288638340105 := by
  unfold tailWord_5854075
  simp only [CollatzResearch.WordTrace]
  refine ⟨213515656266693546257251679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142343770844462364171501119 213515656266693546257251679)
  ·
    refine ⟨320273484400040319385877519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213515656266693546257251679 320273484400040319385877519)
    ·
      refine ⟨480410226600060479078816279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320273484400040319385877519 480410226600060479078816279)
      ·
        refine ⟨720615339900090718618224419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480410226600060479078816279 720615339900090718618224419)
        ·
          refine ⟨1080923009850136077927336629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720615339900090718618224419 1080923009850136077927336629)
          ·
            refine ⟨101336532173450257305687809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1080923009850136077927336629 101336532173450257305687809)
            ·
              refine ⟨76002399130087692979265857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101336532173450257305687809 76002399130087692979265857)
              ·
                refine ⟨57001799347565769734449393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76002399130087692979265857 57001799347565769734449393)
                ·
                  refine ⟨42751349510674327300837045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57001799347565769734449393 42751349510674327300837045)
                  ·
                    refine ⟨4007939016625718184453473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42751349510674327300837045 4007939016625718184453473)
                    ·
                      refine ⟨3005954262469288638340105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4007939016625718184453473 3005954262469288638340105)
                      ·
                        rfl

theorem cell23_5854075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5, 2].length) (baseStart_5854075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854075 prefixEnd_5854075 := by exact prefixLift 5854075
  have htrace : WordTrace (prefixWord ++ tailWord_5854075) baseStart_5854075 baseEnd_5854075 := by
    simpa [prefixWord, tailWord_5854075, baseEnd_5854075] using wordTrace_append hprefix tailTrace_5854075
  have hstable : (prefixWord ++ tailWord_5854075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854075).length < 2 ^ (prefixWord ++ tailWord_5854075).sum := by decide
  have hdescent : baseEnd_5854075 < baseStart_5854075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854157 : List Nat := [1, 6, 3, 1, 2, 1, 2, 2, 5]
def baseStart_5854157 : Nat := 118140960795 + 5854157 * 2 ^ 59
def prefixEnd_5854157 : Nat := 4983230072969 + 3 ^ 40 * 5854157 * 2
def baseEnd_5854157 : Nat := 333999596431439701946081

theorem tailTrace_5854157 : CollatzResearch.WordTrace tailWord_5854157 prefixEnd_5854157 333999596431439701946081 := by
  unfold tailWord_5854157
  simp only [CollatzResearch.WordTrace]
  refine ⟨213518647052396474261736725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142345764701597649507824483 213518647052396474261736725)
  ·
    refine ⟨10008686580581084731018909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 213518647052396474261736725 10008686580581084731018909)
    ·
      refine ⟨3753257467717906774132091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10008686580581084731018909 3753257467717906774132091)
      ·
        refine ⟨5629886201576860161198137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3753257467717906774132091 5629886201576860161198137)
        ·
          refine ⟨4222414651182645120898603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5629886201576860161198137 4222414651182645120898603)
          ·
            refine ⟨6333621976773967681347905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222414651182645120898603 6333621976773967681347905)
            ·
              refine ⟨4750216482580475761010929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6333621976773967681347905 4750216482580475761010929)
              ·
                refine ⟨3562662361935356820758197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4750216482580475761010929 3562662361935356820758197)
                ·
                  refine ⟨333999596431439701946081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3562662361935356820758197 333999596431439701946081)
                  ·
                    rfl

theorem cell23_5854157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_5854157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854157 prefixEnd_5854157 := by exact prefixLift 5854157
  have htrace : WordTrace (prefixWord ++ tailWord_5854157) baseStart_5854157 baseEnd_5854157 := by
    simpa [prefixWord, tailWord_5854157, baseEnd_5854157] using wordTrace_append hprefix tailTrace_5854157
  have hstable : (prefixWord ++ tailWord_5854157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854157).length < 2 ^ (prefixWord ++ tailWord_5854157).sum := by decide
  have hdescent : baseEnd_5854157 < baseStart_5854157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854162 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 6]
def baseStart_5854162 : Nat := 118140960795 + 5854162 * 2 ^ 59
def prefixEnd_5854162 : Nat := 4983230072969 + 3 ^ 40 * 5854162 * 2
def baseEnd_5854162 : Nat := 333999881698469977550245

theorem tailTrace_5854162 : CollatzResearch.WordTrace tailWord_5854162 prefixEnd_5854162 333999881698469977550245 := by
  unfold tailWord_5854162
  simp only [CollatzResearch.WordTrace]
  refine ⟨53379707354344590028917185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142345886278252240077112493 53379707354344590028917185)
  ·
    refine ⟨40034780515758442521687889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53379707354344590028917185 40034780515758442521687889)
    ·
      refine ⟨30026085386818831891265917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40034780515758442521687889 30026085386818831891265917)
      ·
        refine ⟨11259782020057061959224719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30026085386818831891265917 11259782020057061959224719)
        ·
          refine ⟨16889673030085592938837079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11259782020057061959224719 16889673030085592938837079)
          ·
            refine ⟨25334509545128389408255619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16889673030085592938837079 25334509545128389408255619)
            ·
              refine ⟨38001764317692584112383429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25334509545128389408255619 38001764317692584112383429)
              ·
                refine ⟨7125330809567359521071893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38001764317692584112383429 7125330809567359521071893)
                ·
                  refine ⟨333999881698469977550245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7125330809567359521071893 333999881698469977550245)
                  ·
                    rfl

theorem cell23_5854162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_5854162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854162 prefixEnd_5854162 := by exact prefixLift 5854162
  have htrace : WordTrace (prefixWord ++ tailWord_5854162) baseStart_5854162 baseEnd_5854162 := by
    simpa [prefixWord, tailWord_5854162, baseEnd_5854162] using wordTrace_append hprefix tailTrace_5854162
  have hstable : (prefixWord ++ tailWord_5854162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854162).length < 2 ^ (prefixWord ++ tailWord_5854162).sum := by decide
  have hdescent : baseEnd_5854162 < baseStart_5854162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854209 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 1, 5]
def baseStart_5854209 : Nat := 118140960795 + 5854209 * 2 ^ 59
def prefixEnd_5854209 : Nat := 4983230072969 + 3 ^ 40 * 5854209 * 2
def baseEnd_5854209 : Nat := 1002007689625663704688163

theorem tailTrace_5854209 : CollatzResearch.WordTrace tailWord_5854209 prefixEnd_5854209 1002007689625663704688163 := by
  unfold tailWord_5854209
  simp only [CollatzResearch.WordTrace]
  refine ⟨213520543648208087142629681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142347029098805391428419787 213520543648208087142629681)
  ·
    refine ⟨160140407736156065356972261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213520543648208087142629681 160140407736156065356972261)
    ·
      refine ⟨30026326450529262254432299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160140407736156065356972261 30026326450529262254432299)
      ·
        refine ⟨45039489675793893381648449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30026326450529262254432299 45039489675793893381648449)
        ·
          refine ⟨33779617256845420036236337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45039489675793893381648449 33779617256845420036236337)
          ·
            refine ⟨25334712942634065027177253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33779617256845420036236337 25334712942634065027177253)
            ·
              refine ⟨4750258676743887192595735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25334712942634065027177253 4750258676743887192595735)
              ·
                refine ⟨7125388015115830788893603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750258676743887192595735 7125388015115830788893603)
                ·
                  refine ⟨10688082022673746183340405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7125388015115830788893603 10688082022673746183340405)
                  ·
                    refine ⟨1002007689625663704688163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10688082022673746183340405 1002007689625663704688163)
                    ·
                      rfl

theorem cell23_5854209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_5854209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854209 prefixEnd_5854209 := by exact prefixLift 5854209
  have htrace : WordTrace (prefixWord ++ tailWord_5854209) baseStart_5854209 baseEnd_5854209 := by
    simpa [prefixWord, tailWord_5854209, baseEnd_5854209] using wordTrace_append hprefix tailTrace_5854209
  have hstable : (prefixWord ++ tailWord_5854209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854209).length < 2 ^ (prefixWord ++ tailWord_5854209).sum := by decide
  have hdescent : baseEnd_5854209 < baseStart_5854209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854225 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_5854225 : Nat := 118140960795 + 5854225 * 2 ^ 59
def prefixEnd_5854225 : Nat := 4983230072969 + 3 ^ 40 * 5854225 * 2
def baseEnd_5854225 : Nat := 3006031284567463051464415

theorem tailTrace_5854225 : CollatzResearch.WordTrace tailWord_5854225 prefixEnd_5854225 3006031284567463051464415 := by
  unfold tailWord_5854225
  simp only [CollatzResearch.WordTrace]
  refine ⟨213521127216150121875212129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142347418144100081250141419 213521127216150121875212129)
  ·
    refine ⟨160140845412112591406409097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213521127216150121875212129 160140845412112591406409097)
    ·
      refine ⟨120105634059084443554806823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160140845412112591406409097 120105634059084443554806823)
      ·
        refine ⟨180158451088626665332210235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120105634059084443554806823 180158451088626665332210235)
        ·
          refine ⟨270237676632939997998315353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180158451088626665332210235 270237676632939997998315353)
          ·
            refine ⟨202678257474704998498736515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270237676632939997998315353 202678257474704998498736515)
            ·
              refine ⟨304017386212057497748104773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202678257474704998498736515 304017386212057497748104773)
              ·
                refine ⟨57003259914760780827769645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304017386212057497748104773 57003259914760780827769645)
                ·
                  refine ⟨21376222468035292810413617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57003259914760780827769645 21376222468035292810413617)
                  ·
                    refine ⟨16032166851026469607810213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21376222468035292810413617 16032166851026469607810213)
                    ·
                      refine ⟨3006031284567463051464415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16032166851026469607810213 3006031284567463051464415)
                      ·
                        rfl

theorem cell23_5854225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_5854225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854225 prefixEnd_5854225 := by exact prefixLift 5854225
  have htrace : WordTrace (prefixWord ++ tailWord_5854225) baseStart_5854225 baseEnd_5854225 := by
    simpa [prefixWord, tailWord_5854225, baseEnd_5854225] using wordTrace_append hprefix tailTrace_5854225
  have hstable : (prefixWord ++ tailWord_5854225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854225).length < 2 ^ (prefixWord ++ tailWord_5854225).sum := by decide
  have hdescent : baseEnd_5854225 < baseStart_5854225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854232 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_5854232 : Nat := 118140960795 + 5854232 * 2 ^ 59
def prefixEnd_5854232 : Nat := 4983230072969 + 3 ^ 40 * 5854232 * 2
def baseEnd_5854232 : Nat := 3006034878932044524076883

theorem tailTrace_5854232 : CollatzResearch.WordTrace tailWord_5854232 prefixEnd_5854232 3006034878932044524076883 := by
  unfold tailWord_5854232
  simp only [CollatzResearch.WordTrace]
  refine ⟨106760691263562381035358475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142347588351416508047144633 106760691263562381035358475)
  ·
    refine ⟨160141036895343571553037713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106760691263562381035358475 160141036895343571553037713)
    ·
      refine ⟨120105777671507678664778285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160141036895343571553037713 120105777671507678664778285)
      ·
        refine ⟨45039666626815379499291857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120105777671507678664778285 45039666626815379499291857)
        ·
          refine ⟨33779749970111534624468893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45039666626815379499291857 33779749970111534624468893)
          ·
            refine ⟨12667406238791825484175835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33779749970111534624468893 12667406238791825484175835)
            ·
              refine ⟨19001109358187738226263753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12667406238791825484175835 19001109358187738226263753)
              ·
                refine ⟨14250832018640803669697815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19001109358187738226263753 14250832018640803669697815)
                ·
                  refine ⟨21376248027961205504546723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14250832018640803669697815 21376248027961205504546723)
                  ·
                    refine ⟨32064372041941808256820085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21376248027961205504546723 32064372041941808256820085)
                    ·
                      refine ⟨3006034878932044524076883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32064372041941808256820085 3006034878932044524076883)
                      ·
                        rfl

theorem cell23_5854232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_5854232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854232 prefixEnd_5854232 := by exact prefixLift 5854232
  have htrace : WordTrace (prefixWord ++ tailWord_5854232) baseStart_5854232 baseEnd_5854232 := by
    simpa [prefixWord, tailWord_5854232, baseEnd_5854232] using wordTrace_append hprefix tailTrace_5854232
  have hstable : (prefixWord ++ tailWord_5854232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854232).length < 2 ^ (prefixWord ++ tailWord_5854232).sum := by decide
  have hdescent : baseEnd_5854232 < baseStart_5854232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854242 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_5854242 : Nat := 118140960795 + 5854242 * 2 ^ 59
def prefixEnd_5854242 : Nat := 4983230072969 + 3 ^ 40 * 5854242 * 2
def baseEnd_5854242 : Nat := 3006040013738589484951837

theorem tailTrace_5854242 : CollatzResearch.WordTrace tailWord_5854242 prefixEnd_5854242 3006040013738589484951837 := by
  unfold tailWord_5854242
  simp only [CollatzResearch.WordTrace]
  refine ⟨53380436814272133444645245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142347831504725689185720653 53380436814272133444645245)
  ·
    refine ⟨20017663805352050041741967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53380436814272133444645245 20017663805352050041741967)
    ·
      refine ⟨30026495708028075062612951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20017663805352050041741967 30026495708028075062612951)
      ·
        refine ⟨45039743562042112593919427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30026495708028075062612951 45039743562042112593919427)
        ·
          refine ⟨67559615343063168890879141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45039743562042112593919427 67559615343063168890879141)
          ·
            refine ⟨12667427876824344167039839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67559615343063168890879141 12667427876824344167039839)
            ·
              refine ⟨19001141815236516250559759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12667427876824344167039839 19001141815236516250559759)
              ·
                refine ⟨28501712722854774375839639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19001141815236516250559759 28501712722854774375839639)
                ·
                  refine ⟨42752569084282161563759459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28501712722854774375839639 42752569084282161563759459)
                  ·
                    refine ⟨64128853626423242345639189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42752569084282161563759459 64128853626423242345639189)
                    ·
                      refine ⟨3006040013738589484951837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64128853626423242345639189 3006040013738589484951837)
                      ·
                        rfl

theorem cell23_5854242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_5854242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854242 prefixEnd_5854242 := by exact prefixLift 5854242
  have htrace : WordTrace (prefixWord ++ tailWord_5854242) baseStart_5854242 baseEnd_5854242 := by
    simpa [prefixWord, tailWord_5854242, baseEnd_5854242] using wordTrace_append hprefix tailTrace_5854242
  have hstable : (prefixWord ++ tailWord_5854242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854242).length < 2 ^ (prefixWord ++ tailWord_5854242).sum := by decide
  have hdescent : baseEnd_5854242 < baseStart_5854242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854275 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5]
def baseStart_5854275 : Nat := 118140960795 + 5854275 * 2 ^ 59
def prefixEnd_5854275 : Nat := 4983230072969 + 3 ^ 40 * 5854275 * 2
def baseEnd_5854275 : Nat := 3006056958600187855839185

theorem tailTrace_5854275 : CollatzResearch.WordTrace tailWord_5854275 prefixEnd_5854275 3006056958600187855839185 := by
  unfold tailWord_5854275
  simp only [CollatzResearch.WordTrace]
  refine ⟨213522950865968980414532279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142348633910645986943021519 213522950865968980414532279)
  ·
    refine ⟨320284426298953470621798419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213522950865968980414532279 320284426298953470621798419)
    ·
      refine ⟨480426639448430205932697629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320284426298953470621798419 480426639448430205932697629)
      ·
        refine ⟨180159989793161327224761611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480426639448430205932697629 180159989793161327224761611)
        ·
          refine ⟨270239984689741990837142417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180159989793161327224761611 270239984689741990837142417)
          ·
            refine ⟨202679988517306493127856813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270239984689741990837142417 202679988517306493127856813)
            ·
              refine ⟨76004995693989934922946305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202679988517306493127856813 76004995693989934922946305)
              ·
                refine ⟨57003746770492451192209729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76004995693989934922946305 57003746770492451192209729)
                ·
                  refine ⟨42752810077869338394157297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57003746770492451192209729 42752810077869338394157297)
                  ·
                    refine ⟨32064607558402003795617973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42752810077869338394157297 32064607558402003795617973)
                    ·
                      refine ⟨3006056958600187855839185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32064607558402003795617973 3006056958600187855839185)
                      ·
                        rfl

theorem cell23_5854275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_5854275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854275 prefixEnd_5854275 := by exact prefixLift 5854275
  have htrace : WordTrace (prefixWord ++ tailWord_5854275) baseStart_5854275 baseEnd_5854275 := by
    simpa [prefixWord, tailWord_5854275, baseEnd_5854275] using wordTrace_append hprefix tailTrace_5854275
  have hstable : (prefixWord ++ tailWord_5854275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854275).length < 2 ^ (prefixWord ++ tailWord_5854275).sum := by decide
  have hdescent : baseEnd_5854275 < baseStart_5854275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854279 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_5854279 : Nat := 118140960795 + 5854279 * 2 ^ 59
def prefixEnd_5854279 : Nat := 4983230072969 + 3 ^ 40 * 5854279 * 2
def baseEnd_5854279 : Nat := 3006059012522805840189167

theorem tailTrace_5854279 : CollatzResearch.WordTrace tailWord_5854279 prefixEnd_5854279 3006059012522805840189167 := by
  unfold tailWord_5854279
  simp only [CollatzResearch.WordTrace]
  refine ⟨213523096757954489097677891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142348731171969659398451927 213523096757954489097677891)
  ·
    refine ⟨320284645136931733646516837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213523096757954489097677891 320284645136931733646516837)
    ·
      refine ⟨60053370963174700058721907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320284645136931733646516837 60053370963174700058721907)
      ·
        refine ⟨90080056444762050088082861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60053370963174700058721907 90080056444762050088082861)
        ·
          refine ⟨33780021166785768783031073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90080056444762050088082861 33780021166785768783031073)
          ·
            refine ⟨25335015875089326587273305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33780021166785768783031073 25335015875089326587273305)
            ·
              refine ⟨19001261906316994940454979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25335015875089326587273305 19001261906316994940454979)
              ·
                refine ⟨28501892859475492410682469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19001261906316994940454979 28501892859475492410682469)
                ·
                  refine ⟨5344104911151654827002963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28501892859475492410682469 5344104911151654827002963)
                  ·
                    refine ⟨8016157366727482240504445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5344104911151654827002963 8016157366727482240504445)
                    ·
                      refine ⟨3006059012522805840189167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8016157366727482240504445 3006059012522805840189167)
                      ·
                        rfl

theorem cell23_5854279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_5854279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854279 prefixEnd_5854279 := by exact prefixLift 5854279
  have htrace : WordTrace (prefixWord ++ tailWord_5854279) baseStart_5854279 baseEnd_5854279 := by
    simpa [prefixWord, tailWord_5854279, baseEnd_5854279] using wordTrace_append hprefix tailTrace_5854279
  have hstable : (prefixWord ++ tailWord_5854279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854279).length < 2 ^ (prefixWord ++ tailWord_5854279).sum := by decide
  have hdescent : baseEnd_5854279 < baseStart_5854279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854295 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 1, 8]
def baseStart_5854295 : Nat := 118140960795 + 5854295 * 2 ^ 59
def prefixEnd_5854295 : Nat := 4983230072969 + 3 ^ 40 * 5854295 * 2
def baseEnd_5854295 : Nat := 1002022409404425925863031

theorem tailTrace_5854295 : CollatzResearch.WordTrace tailWord_5854295 prefixEnd_5854295 1002022409404425925863031 := by
  unfold tailWord_5854295
  simp only [CollatzResearch.WordTrace]
  refine ⟨213523680325896523830260339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142349120217264349220173559 213523680325896523830260339)
  ·
    refine ⟨320285520488844785745390509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213523680325896523830260339 320285520488844785745390509)
    ·
      refine ⟨120107070183316794654521441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320285520488844785745390509 120107070183316794654521441)
      ·
        refine ⟨90080302637487595990891081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120107070183316794654521441 90080302637487595990891081)
        ·
          refine ⟨67560226978115696993168311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90080302637487595990891081 67560226978115696993168311)
          ·
            refine ⟨101340340467173545489752467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67560226978115696993168311 101340340467173545489752467)
            ·
              refine ⟨152010510700760318234628701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101340340467173545489752467 152010510700760318234628701)
              ·
                refine ⟨57003941512785119337985763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152010510700760318234628701 57003941512785119337985763)
                ·
                  refine ⟨85505912269177679006978645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57003941512785119337985763 85505912269177679006978645)
                  ·
                    refine ⟨1002022409404425925863031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85505912269177679006978645 1002022409404425925863031)
                    ·
                      rfl

theorem cell23_5854295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_5854295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854295 prefixEnd_5854295 := by exact prefixLift 5854295
  have htrace : WordTrace (prefixWord ++ tailWord_5854295) baseStart_5854295 baseEnd_5854295 := by
    simpa [prefixWord, tailWord_5854295, baseEnd_5854295] using wordTrace_append hprefix tailTrace_5854295
  have hstable : (prefixWord ++ tailWord_5854295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854295).length < 2 ^ (prefixWord ++ tailWord_5854295).sum := by decide
  have hdescent : baseEnd_5854295 < baseStart_5854295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854319 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 1, 4, 2]
def baseStart_5854319 : Nat := 118140960795 + 5854319 * 2 ^ 59
def prefixEnd_5854319 : Nat := 4983230072969 + 3 ^ 40 * 5854319 * 2
def baseEnd_5854319 : Nat := 3006079551748985683688983

theorem tailTrace_5854319 : CollatzResearch.WordTrace tailWord_5854319 prefixEnd_5854319 3006079551748985683688983 := by
  unfold tailWord_5854319
  simp only [CollatzResearch.WordTrace]
  refine ⟨213524555677809575929134011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142349703785206383952756007 213524555677809575929134011)
  ·
    refine ⟨320286833516714363893701017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213524555677809575929134011 320286833516714363893701017)
    ·
      refine ⟨240215125137535772920275763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320286833516714363893701017 240215125137535772920275763)
      ·
        refine ⟨360322687706303659380413645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240215125137535772920275763 360322687706303659380413645)
        ·
          refine ⟨135121007889863872267655117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360322687706303659380413645 135121007889863872267655117)
          ·
            refine ⟨50670377958698952100370669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135121007889863872267655117 50670377958698952100370669)
            ·
              refine ⟨19001391734512107037639001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50670377958698952100370669 19001391734512107037639001)
              ·
                refine ⟨14251043800884080278229251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19001391734512107037639001 14251043800884080278229251)
                ·
                  refine ⟨21376565701326120417343877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14251043800884080278229251 21376565701326120417343877)
                  ·
                    refine ⟨4008106068998647578251977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21376565701326120417343877 4008106068998647578251977)
                    ·
                      refine ⟨3006079551748985683688983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008106068998647578251977 3006079551748985683688983)
                      ·
                        rfl

theorem cell23_5854319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4, 2].length) (baseStart_5854319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854319 prefixEnd_5854319 := by exact prefixLift 5854319
  have htrace : WordTrace (prefixWord ++ tailWord_5854319) baseStart_5854319 baseEnd_5854319 := by
    simpa [prefixWord, tailWord_5854319, baseEnd_5854319] using wordTrace_append hprefix tailTrace_5854319
  have hstable : (prefixWord ++ tailWord_5854319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854319).length < 2 ^ (prefixWord ++ tailWord_5854319).sum := by decide
  have hdescent : baseEnd_5854319 < baseStart_5854319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854322 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_5854322 : Nat := 118140960795 + 5854322 * 2 ^ 59
def prefixEnd_5854322 : Nat := 4983230072969 + 3 ^ 40 * 5854322 * 2
def baseEnd_5854322 : Nat := 3006081092190949171951469

theorem tailTrace_5854322 : CollatzResearch.WordTrace tailWord_5854322 prefixEnd_5854322 3006081092190949171951469 := by
  unfold tailWord_5854322
  simp only [CollatzResearch.WordTrace]
  refine ⟨53381166274199676860373305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142349776731199138294328813 53381166274199676860373305)
  ·
    refine ⟨40035874705649757645279979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53381166274199676860373305 40035874705649757645279979)
    ·
      refine ⟨60053812058474636467919969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40035874705649757645279979 60053812058474636467919969)
      ·
        refine ⟨45040359043855977350939977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60053812058474636467919969 45040359043855977350939977)
        ·
          refine ⟨33780269282891983013204983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45040359043855977350939977 33780269282891983013204983)
          ·
            refine ⟨50670403924337974519807475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33780269282891983013204983 50670403924337974519807475)
            ·
              refine ⟨76005605886506961779711213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50670403924337974519807475 76005605886506961779711213)
              ·
                refine ⟨28502102207440110667391705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76005605886506961779711213 28502102207440110667391705)
                ·
                  refine ⟨21376576655580083000543779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28502102207440110667391705 21376576655580083000543779)
                  ·
                    refine ⟨32064864983370124500815669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21376576655580083000543779 32064864983370124500815669)
                    ·
                      refine ⟨3006081092190949171951469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32064864983370124500815669 3006081092190949171951469)
                      ·
                        rfl

theorem cell23_5854322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_5854322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854322 prefixEnd_5854322 := by exact prefixLift 5854322
  have htrace : WordTrace (prefixWord ++ tailWord_5854322) baseStart_5854322 baseEnd_5854322 := by
    simpa [prefixWord, tailWord_5854322, baseEnd_5854322] using wordTrace_append hprefix tailTrace_5854322
  have hstable : (prefixWord ++ tailWord_5854322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854322).length < 2 ^ (prefixWord ++ tailWord_5854322).sum := by decide
  have hdescent : baseEnd_5854322 < baseStart_5854322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854332 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_5854332 : Nat := 118140960795 + 5854332 * 2 ^ 59
def prefixEnd_5854332 : Nat := 4983230072969 + 3 ^ 40 * 5854332 * 2
def baseEnd_5854332 : Nat := 3006086226997494132826423

theorem tailTrace_5854332 : CollatzResearch.WordTrace tailWord_5854332 prefixEnd_5854332 3006086226997494132826423 := by
  unfold tailWord_5854332
  simp only [CollatzResearch.WordTrace]
  refine ⟨106762514913381239574678625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142350019884508319432904833 106762514913381239574678625)
  ·
    refine ⟨80071886185035929681008969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106762514913381239574678625 80071886185035929681008969)
    ·
      refine ⟨60053914638776947260756727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80071886185035929681008969 60053914638776947260756727)
      ·
        refine ⟨90080871958165420891135091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60053914638776947260756727 90080871958165420891135091)
        ·
          refine ⟨135121307937248131336702637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90080871958165420891135091 135121307937248131336702637)
          ·
            refine ⟨50670490476468049251263489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135121307937248131336702637 50670490476468049251263489)
            ·
              refine ⟨38002867857351036938447617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50670490476468049251263489 38002867857351036938447617)
              ·
                refine ⟨28502150893013277703835713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38002867857351036938447617 28502150893013277703835713)
                ·
                  refine ⟨21376613169759958277876785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28502150893013277703835713 21376613169759958277876785)
                  ·
                    refine ⟨16032459877319968708407589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21376613169759958277876785 16032459877319968708407589)
                    ·
                      refine ⟨3006086226997494132826423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16032459877319968708407589 3006086226997494132826423)
                      ·
                        rfl

theorem cell23_5854332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_5854332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854332 prefixEnd_5854332 := by exact prefixLift 5854332
  have htrace : WordTrace (prefixWord ++ tailWord_5854332) baseStart_5854332 baseEnd_5854332 := by
    simpa [prefixWord, tailWord_5854332, baseEnd_5854332] using wordTrace_append hprefix tailTrace_5854332
  have hstable : (prefixWord ++ tailWord_5854332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854332).length < 2 ^ (prefixWord ++ tailWord_5854332).sum := by decide
  have hdescent : baseEnd_5854332 < baseStart_5854332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854336 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 2, 2, 2]
def baseStart_5854336 : Nat := 118140960795 + 5854336 * 2 ^ 59
def prefixEnd_5854336 : Nat := 4983230072969 + 3 ^ 40 * 5854336 * 2
def baseEnd_5854336 : Nat := 3006088280920112117176405

theorem tailTrace_5854336 : CollatzResearch.WordTrace tailWord_5854336 prefixEnd_5854336 3006088280920112117176405 := by
  unfold tailWord_5854336
  simp only [CollatzResearch.WordTrace]
  refine ⟨106762587859373993916251431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142350117145831991888335241 106762587859373993916251431)
  ·
    refine ⟨160143881789060990874377147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106762587859373993916251431 160143881789060990874377147)
    ·
      refine ⟨240215822683591486311565721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160143881789060990874377147 240215822683591486311565721)
      ·
        refine ⟨180161867012693614733674291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240215822683591486311565721 180161867012693614733674291)
        ·
          refine ⟨270242800519040422100511437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180161867012693614733674291 270242800519040422100511437)
          ·
            refine ⟨101341050194640158287691789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270242800519040422100511437 101341050194640158287691789)
            ·
              refine ⟨38002893822990059357884421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101341050194640158287691789 38002893822990059357884421)
              ·
                refine ⟨7125542591810636129603329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38002893822990059357884421 7125542591810636129603329)
                ·
                  refine ⟨5344156943857977097202497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7125542591810636129603329 5344156943857977097202497)
                  ·
                    refine ⟨4008117707893482822901873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5344156943857977097202497 4008117707893482822901873)
                    ·
                      refine ⟨3006088280920112117176405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008117707893482822901873 3006088280920112117176405)
                      ·
                        rfl

theorem cell23_5854336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_5854336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854336 prefixEnd_5854336 := by exact prefixLift 5854336
  have htrace : WordTrace (prefixWord ++ tailWord_5854336) baseStart_5854336 baseEnd_5854336 := by
    simpa [prefixWord, tailWord_5854336, baseEnd_5854336] using wordTrace_append hprefix tailTrace_5854336
  have hstable : (prefixWord ++ tailWord_5854336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854336).length < 2 ^ (prefixWord ++ tailWord_5854336).sum := by decide
  have hdescent : baseEnd_5854336 < baseStart_5854336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854432 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 8]
def baseStart_5854432 : Nat := 118140960795 + 5854432 * 2 ^ 59
def prefixEnd_5854432 : Nat := 4983230072969 + 3 ^ 40 * 5854432 * 2
def baseEnd_5854432 : Nat := 334015286118104860175107

theorem tailTrace_5854432 : CollatzResearch.WordTrace tailWord_5854432 prefixEnd_5854432 334015286118104860175107 := by
  unfold tailWord_5854432
  simp only [CollatzResearch.WordTrace]
  refine ⟨106764338563200098113998775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142352451417600130818665033 106764338563200098113998775)
  ·
    refine ⟨160146507844800147170998163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106764338563200098113998775 160146507844800147170998163)
    ·
      refine ⟨240219761767200220756497245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160146507844800147170998163 240219761767200220756497245)
      ·
        refine ⟨90082410662700082783686467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240219761767200220756497245 90082410662700082783686467)
        ·
          refine ⟨135123615994050124175529701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90082410662700082783686467 135123615994050124175529701)
          ·
            refine ⟨25335677998884398282911819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135123615994050124175529701 25335677998884398282911819)
            ·
              refine ⟨38003516998326597424367729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25335677998884398282911819 38003516998326597424367729)
              ·
                refine ⟨28502637748744948068275797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38003516998326597424367729 28502637748744948068275797)
                ·
                  refine ⟨334015286118104860175107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28502637748744948068275797 334015286118104860175107)
                  ·
                    rfl

theorem cell23_5854432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_5854432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854432 prefixEnd_5854432 := by exact prefixLift 5854432
  have htrace : WordTrace (prefixWord ++ tailWord_5854432) baseStart_5854432 baseEnd_5854432 := by
    simpa [prefixWord, tailWord_5854432, baseEnd_5854432] using wordTrace_append hprefix tailTrace_5854432
  have hstable : (prefixWord ++ tailWord_5854432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854432).length < 2 ^ (prefixWord ++ tailWord_5854432).sum := by decide
  have hdescent : baseEnd_5854432 < baseStart_5854432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854516 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5854516 : Nat := 118140960795 + 5854516 * 2 ^ 59
def prefixEnd_5854516 : Nat := 4983230072969 + 3 ^ 40 * 5854516 * 2
def baseEnd_5854516 : Nat := 3006180707437921412925577

theorem tailTrace_5854516 : CollatzResearch.WordTrace tailWord_5854516 prefixEnd_5854516 3006180707437921412925577 := by
  unfold tailWord_5854516
  simp only [CollatzResearch.WordTrace]
  refine ⟨106765870429047939287027701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142354493905397252382703601 106765870429047939287027701)
  ·
    refine ⟨10009300352723244308158847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106765870429047939287027701 10009300352723244308158847)
    ·
      refine ⟨15013950529084866462238271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10009300352723244308158847 15013950529084866462238271)
      ·
        refine ⟨22520925793627299693357407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15013950529084866462238271 22520925793627299693357407)
        ·
          refine ⟨33781388690440949540036111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22520925793627299693357407 33781388690440949540036111)
          ·
            refine ⟨50672083035661424310054167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33781388690440949540036111 50672083035661424310054167)
            ·
              refine ⟨76008124553492136465081251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50672083035661424310054167 76008124553492136465081251)
              ·
                refine ⟨114012186830238204697621877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76008124553492136465081251 114012186830238204697621877)
                ·
                  refine ⟨10688642515334831690402051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114012186830238204697621877 10688642515334831690402051)
                  ·
                    refine ⟨16032963773002247535603077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10688642515334831690402051 16032963773002247535603077)
                    ·
                      refine ⟨3006180707437921412925577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16032963773002247535603077 3006180707437921412925577)
                      ·
                        rfl

theorem cell23_5854516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5854516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854516 prefixEnd_5854516 := by exact prefixLift 5854516
  have htrace : WordTrace (prefixWord ++ tailWord_5854516) baseStart_5854516 baseEnd_5854516 := by
    simpa [prefixWord, tailWord_5854516, baseEnd_5854516] using wordTrace_append hprefix tailTrace_5854516
  have hstable : (prefixWord ++ tailWord_5854516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854516).length < 2 ^ (prefixWord ++ tailWord_5854516).sum := by decide
  have hdescent : baseEnd_5854516 < baseStart_5854516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854526 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_5854526 : Nat := 118140960795 + 5854526 * 2 ^ 59
def prefixEnd_5854526 : Nat := 4983230072969 + 3 ^ 40 * 5854526 * 2
def baseEnd_5854526 : Nat := 1002061947414822124600177

theorem tailTrace_5854526 : CollatzResearch.WordTrace tailWord_5854526 prefixEnd_5854526 1002061947414822124600177 := by
  unfold tailWord_5854526
  simp only [CollatzResearch.WordTrace]
  refine ⟨26691513198507456285239929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142354737058706433521279621 26691513198507456285239929)
  ·
    refine ⟨20018634898880592213929947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26691513198507456285239929 20018634898880592213929947)
    ·
      refine ⟨30027952348320888320894921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20018634898880592213929947 30027952348320888320894921)
      ·
        refine ⟨22520964261240666240671191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30027952348320888320894921 22520964261240666240671191)
        ·
          refine ⟨33781446391860999361006787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22520964261240666240671191 33781446391860999361006787)
          ·
            refine ⟨50672169587791499041510181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33781446391860999361006787 50672169587791499041510181)
            ·
              refine ⟨9501031797710906070283159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50672169587791499041510181 9501031797710906070283159)
              ·
                refine ⟨14251547696566359105424739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9501031797710906070283159 14251547696566359105424739)
                ·
                  refine ⟨21377321544849538658137109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14251547696566359105424739 21377321544849538658137109)
                  ·
                    refine ⟨1002061947414822124600177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21377321544849538658137109 1002061947414822124600177)
                    ·
                      rfl

theorem cell23_5854526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_5854526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854526 prefixEnd_5854526 := by exact prefixLift 5854526
  have htrace : WordTrace (prefixWord ++ tailWord_5854526) baseStart_5854526 baseEnd_5854526 := by
    simpa [prefixWord, tailWord_5854526, baseEnd_5854526] using wordTrace_append hprefix tailTrace_5854526
  have hstable : (prefixWord ++ tailWord_5854526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854526).length < 2 ^ (prefixWord ++ tailWord_5854526).sum := by decide
  have hdescent : baseEnd_5854526 < baseStart_5854526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854536 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_5854536 : Nat := 118140960795 + 5854536 * 2 ^ 59
def prefixEnd_5854536 : Nat := 4983230072969 + 3 ^ 40 * 5854536 * 2
def baseEnd_5854536 : Nat := 3006190977051011334675485

theorem tailTrace_5854536 : CollatzResearch.WordTrace tailWord_5854536 prefixEnd_5854536 3006190977051011334675485 := by
  unfold tailWord_5854536
  simp only [CollatzResearch.WordTrace]
  refine ⟨106766235159011710994891731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142354980212015614659855641 106766235159011710994891731)
  ·
    refine ⟨160149352738517566492337597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106766235159011710994891731 160149352738517566492337597)
    ·
      refine ⟨60056007276944087434626599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160149352738517566492337597 60056007276944087434626599)
      ·
        refine ⟨90084010915416131151939899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60056007276944087434626599 90084010915416131151939899)
        ·
          refine ⟨135126016373124196727909849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90084010915416131151939899 135126016373124196727909849)
          ·
            refine ⟨101344512279843147545932387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135126016373124196727909849 101344512279843147545932387)
            ·
              refine ⟨152016768419764721318898581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101344512279843147545932387 152016768419764721318898581)
              ·
                refine ⟨7125786019676471311823371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152016768419764721318898581 7125786019676471311823371)
                ·
                  refine ⟨10688679029514706967735057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7125786019676471311823371 10688679029514706967735057)
                  ·
                    refine ⟨8016509272136030225801293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10688679029514706967735057 8016509272136030225801293)
                    ·
                      refine ⟨3006190977051011334675485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8016509272136030225801293 3006190977051011334675485)
                      ·
                        rfl

theorem cell23_5854536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_5854536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854536 prefixEnd_5854536 := by exact prefixLift 5854536
  have htrace : WordTrace (prefixWord ++ tailWord_5854536) baseStart_5854536 baseEnd_5854536 := by
    simpa [prefixWord, tailWord_5854536, baseEnd_5854536] using wordTrace_append hprefix tailTrace_5854536
  have hstable : (prefixWord ++ tailWord_5854536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854536).length < 2 ^ (prefixWord ++ tailWord_5854536).sum := by decide
  have hdescent : baseEnd_5854536 < baseStart_5854536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854553 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 1, 2, 3]
def baseStart_5854553 : Nat := 118140960795 + 5854553 * 2 ^ 59
def prefixEnd_5854553 : Nat := 4983230072969 + 3 ^ 40 * 5854553 * 2
def baseEnd_5854553 : Nat := 3006199706222137768162907

theorem tailTrace_5854553 : CollatzResearch.WordTrace tailWord_5854553 prefixEnd_5854553 3006199706222137768162907 := by
  unfold tailWord_5854553
  simp only [CollatzResearch.WordTrace]
  refine ⟨213533090358961833893152313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142355393572641222595434875 213533090358961833893152313)
  ·
    refine ⟨160149817769221375419864235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213533090358961833893152313 160149817769221375419864235)
    ·
      refine ⟨240224726653832063129796353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160149817769221375419864235 240224726653832063129796353)
      ·
        refine ⟨180168544990374047347347265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240224726653832063129796353 180168544990374047347347265)
        ·
          refine ⟨135126408742780535510510449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180168544990374047347347265 135126408742780535510510449)
          ·
            refine ⟨101344806557085401632882837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135126408742780535510510449 101344806557085401632882837)
            ·
              refine ⟨4750537807363378201541383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101344806557085401632882837 4750537807363378201541383)
              ·
                refine ⟨7125806711045067302312075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750537807363378201541383 7125806711045067302312075)
                ·
                  refine ⟨10688710066567600953468113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7125806711045067302312075 10688710066567600953468113)
                  ·
                    refine ⟨8016532549925700715101085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10688710066567600953468113 8016532549925700715101085)
                    ·
                      refine ⟨3006199706222137768162907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8016532549925700715101085 3006199706222137768162907)
                      ·
                        rfl

theorem cell23_5854553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_5854553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854553 prefixEnd_5854553 := by exact prefixLift 5854553
  have htrace : WordTrace (prefixWord ++ tailWord_5854553) baseStart_5854553 baseEnd_5854553 := by
    simpa [prefixWord, tailWord_5854553, baseEnd_5854553] using wordTrace_append hprefix tailTrace_5854553
  have hstable : (prefixWord ++ tailWord_5854553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854553).length < 2 ^ (prefixWord ++ tailWord_5854553).sum := by decide
  have hdescent : baseEnd_5854553 < baseStart_5854553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854609 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_5854609 : Nat := 118140960795 + 5854609 * 2 ^ 59
def prefixEnd_5854609 : Nat := 4983230072969 + 3 ^ 40 * 5854609 * 2
def baseEnd_5854609 : Nat := 3006228461138789549062649

theorem tailTrace_5854609 : CollatzResearch.WordTrace tailWord_5854609 prefixEnd_5854609 3006228461138789549062649 := by
  unfold tailWord_5854609
  simp only [CollatzResearch.WordTrace]
  refine ⟨213535132846758955457190881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142356755231172636971460587 213535132846758955457190881)
  ·
    refine ⟨160151349635069216592893161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213535132846758955457190881 160151349635069216592893161)
    ·
      refine ⟨120113512226301912444669871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160151349635069216592893161 120113512226301912444669871)
      ·
        refine ⟨180170268339452868667004807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120113512226301912444669871 180170268339452868667004807)
        ·
          refine ⟨270255402509179303000507211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180170268339452868667004807 270255402509179303000507211)
          ·
            refine ⟨405383103763768954500760817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270255402509179303000507211 405383103763768954500760817)
            ·
              refine ⟨304037327822826715875570613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405383103763768954500760817 304037327822826715875570613)
              ·
                refine ⟨28503499483390004613334745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304037327822826715875570613 28503499483390004613334745)
                ·
                  refine ⟨21377624612542503460001059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28503499483390004613334745 21377624612542503460001059)
                  ·
                    refine ⟨32066436918813755190001589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21377624612542503460001059 32066436918813755190001589)
                    ·
                      refine ⟨3006228461138789549062649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32066436918813755190001589 3006228461138789549062649)
                      ·
                        rfl

theorem cell23_5854609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_5854609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854609 prefixEnd_5854609 := by exact prefixLift 5854609
  have htrace : WordTrace (prefixWord ++ tailWord_5854609) baseStart_5854609 baseEnd_5854609 := by
    simpa [prefixWord, tailWord_5854609, baseEnd_5854609] using wordTrace_append hprefix tailTrace_5854609
  have hstable : (prefixWord ++ tailWord_5854609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854609).length < 2 ^ (prefixWord ++ tailWord_5854609).sum := by decide
  have hdescent : baseEnd_5854609 < baseStart_5854609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854629 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 7]
def baseStart_5854629 : Nat := 118140960795 + 5854629 * 2 ^ 59
def prefixEnd_5854629 : Nat := 4983230072969 + 3 ^ 40 * 5854629 * 2
def baseEnd_5854629 : Nat := 334026525639097718979173

theorem tailTrace_5854629 : CollatzResearch.WordTrace tailWord_5854629 prefixEnd_5854629 334026525639097718979173 := by
  unfold tailWord_5854629
  simp only [CollatzResearch.WordTrace]
  refine ⟨213535862306686498872918941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142357241537790999248612627 213535862306686498872918941)
  ·
    refine ⟨80075948365007437077344603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213535862306686498872918941 80075948365007437077344603)
    ·
      refine ⟨120113922547511155616016905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80075948365007437077344603 120113922547511155616016905)
      ·
        refine ⟨90085441910633366712012679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120113922547511155616016905 90085441910633366712012679)
        ·
          refine ⟨135128162865950050068019019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90085441910633366712012679 135128162865950050068019019)
          ·
            refine ⟨202692244298925075102028529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135128162865950050068019019 202692244298925075102028529)
            ·
              refine ⟨152019183224193806326521397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202692244298925075102028529 152019183224193806326521397)
              ·
                refine ⟨14251798427268169343111381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152019183224193806326521397 14251798427268169343111381)
                ·
                  refine ⟨334026525639097718979173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14251798427268169343111381 334026525639097718979173)
                  ·
                    rfl

theorem cell23_5854629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_5854629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854629 prefixEnd_5854629 := by exact prefixLift 5854629
  have htrace : WordTrace (prefixWord ++ tailWord_5854629) baseStart_5854629 baseEnd_5854629 := by
    simpa [prefixWord, tailWord_5854629, baseEnd_5854629] using wordTrace_append hprefix tailTrace_5854629
  have hstable : (prefixWord ++ tailWord_5854629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854629).length < 2 ^ (prefixWord ++ tailWord_5854629).sum := by decide
  have hdescent : baseEnd_5854629 < baseStart_5854629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854659 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 1, 7]
def baseStart_5854659 : Nat := 118140960795 + 5854659 * 2 ^ 59
def prefixEnd_5854659 : Nat := 4983230072969 + 3 ^ 40 * 5854659 * 2
def baseEnd_5854659 : Nat := 1002084711723838117812473

theorem tailTrace_5854659 : CollatzResearch.WordTrace tailWord_5854659 prefixEnd_5854659 1002084711723838117812473 := by
  unfold tailWord_5854659
  simp only [CollatzResearch.WordTrace]
  refine ⟨213536956496577813996511031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142357970997718542664340687 213536956496577813996511031)
  ·
    refine ⟨320305434744866720994766547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213536956496577813996511031 320305434744866720994766547)
    ·
      refine ⟨480458152117300081492149821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320305434744866720994766547 480458152117300081492149821)
      ·
        refine ⟨180171807043987530559556183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480458152117300081492149821 180171807043987530559556183)
        ·
          refine ⟨270257710565981295839334275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180171807043987530559556183 270257710565981295839334275)
          ·
            refine ⟨405386565848971943759001413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270257710565981295839334275 405386565848971943759001413)
            ·
              refine ⟨76009981096682239454812765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405386565848971943759001413 76009981096682239454812765)
              ·
                refine ⟨28503742911255839795554787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76009981096682239454812765 28503742911255839795554787)
                ·
                  refine ⟨42755614366883759693332181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28503742911255839795554787 42755614366883759693332181)
                  ·
                    refine ⟨1002084711723838117812473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42755614366883759693332181 1002084711723838117812473)
                    ·
                      rfl

theorem cell23_5854659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 7].length) (baseStart_5854659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854659 prefixEnd_5854659 := by exact prefixLift 5854659
  have htrace : WordTrace (prefixWord ++ tailWord_5854659) baseStart_5854659 baseEnd_5854659 := by
    simpa [prefixWord, tailWord_5854659, baseEnd_5854659] using wordTrace_append hprefix tailTrace_5854659
  have hstable : (prefixWord ++ tailWord_5854659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854659).length < 2 ^ (prefixWord ++ tailWord_5854659).sum := by decide
  have hdescent : baseEnd_5854659 < baseStart_5854659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854696 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5854696 : Nat := 118140960795 + 5854696 * 2 ^ 59
def prefixEnd_5854696 : Nat := 4983230072969 + 3 ^ 40 * 5854696 * 2
def baseEnd_5854696 : Nat := 3006273133955730708674749

theorem tailTrace_5854696 : CollatzResearch.WordTrace tailWord_5854696 prefixEnd_5854696 3006273133955730708674749 := by
  unfold tailWord_5854696
  simp only [CollatzResearch.WordTrace]
  refine ⟨106769152998721884657803971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142358870664962512877071961 106769152998721884657803971)
  ·
    refine ⟨160153729498082826986705957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106769152998721884657803971 160153729498082826986705957)
    ·
      refine ⟨30028824280890530060007367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160153729498082826986705957 30028824280890530060007367)
      ·
        refine ⟨45043236421335795090011051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30028824280890530060007367 45043236421335795090011051)
        ·
          refine ⟨67564854632003692635016577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45043236421335795090011051 67564854632003692635016577)
          ·
            refine ⟨50673640974002769476262433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67564854632003692635016577 50673640974002769476262433)
            ·
              refine ⟨38005230730502077107196825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50673640974002769476262433 38005230730502077107196825)
              ·
                refine ⟨28503923047876557830397619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38005230730502077107196825 28503923047876557830397619)
                ·
                  refine ⟨42755884571814836745596429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28503923047876557830397619 42755884571814836745596429)
                  ·
                    refine ⟨16033456714430563779598661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42755884571814836745596429 16033456714430563779598661)
                    ·
                      refine ⟨3006273133955730708674749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16033456714430563779598661 3006273133955730708674749)
                      ·
                        rfl

theorem cell23_5854696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5854696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854696 prefixEnd_5854696 := by exact prefixLift 5854696
  have htrace : WordTrace (prefixWord ++ tailWord_5854696) baseStart_5854696 baseEnd_5854696 := by
    simpa [prefixWord, tailWord_5854696, baseEnd_5854696] using wordTrace_append hprefix tailTrace_5854696
  have hstable : (prefixWord ++ tailWord_5854696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854696).length < 2 ^ (prefixWord ++ tailWord_5854696).sum := by decide
  have hdescent : baseEnd_5854696 < baseStart_5854696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854710 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_5854710 : Nat := 118140960795 + 5854710 * 2 ^ 59
def prefixEnd_5854710 : Nat := 4983230072969 + 3 ^ 40 * 5854710 * 2
def baseEnd_5854710 : Nat := 1002093440894964551299895

theorem tailTrace_5854710 : CollatzResearch.WordTrace tailWord_5854710 prefixEnd_5854710 1002093440894964551299895 := by
  unfold tailWord_5854710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13346176038712065606663599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142359211079595366471078389 13346176038712065606663599)
  ·
    refine ⟨20019264058068098409995399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13346176038712065606663599 20019264058068098409995399)
    ·
      refine ⟨30028896087102147614993099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20019264058068098409995399 30028896087102147614993099)
      ·
        refine ⟨45043344130653221422489649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30028896087102147614993099 45043344130653221422489649)
        ·
          refine ⟨33782508097989916066867237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45043344130653221422489649 33782508097989916066867237)
          ·
            refine ⟨6334220268373109262537607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33782508097989916066867237 6334220268373109262537607)
            ·
              refine ⟨9501330402559663893806411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6334220268373109262537607 9501330402559663893806411)
              ·
                refine ⟨14251995603839495840709617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9501330402559663893806411 14251995603839495840709617)
                ·
                  refine ⟨10688996702879621880532213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14251995603839495840709617 10688996702879621880532213)
                  ·
                    refine ⟨1002093440894964551299895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10688996702879621880532213 1002093440894964551299895)
                    ·
                      rfl

theorem cell23_5854710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_5854710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854710 prefixEnd_5854710 := by exact prefixLift 5854710
  have htrace : WordTrace (prefixWord ++ tailWord_5854710) baseStart_5854710 baseEnd_5854710 := by
    simpa [prefixWord, tailWord_5854710, baseEnd_5854710] using wordTrace_append hprefix tailTrace_5854710
  have hstable : (prefixWord ++ tailWord_5854710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854710).length < 2 ^ (prefixWord ++ tailWord_5854710).sum := by decide
  have hdescent : baseEnd_5854710 < baseStart_5854710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854783 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 1, 5]
def baseStart_5854783 : Nat := 118140960795 + 5854783 * 2 ^ 59
def prefixEnd_5854783 : Nat := 4983230072969 + 3 ^ 40 * 5854783 * 2
def baseEnd_5854783 : Nat := 1002105935590890622762283

theorem tailTrace_5854783 : CollatzResearch.WordTrace tailWord_5854783 prefixEnd_5854783 1002105935590890622762283 := by
  unfold tailWord_5854783
  simp only [CollatzResearch.WordTrace]
  refine ⟨213541479148128583174025003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142360986098752388782683335 213541479148128583174025003)
  ·
    refine ⟨320312218722192874761037505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213541479148128583174025003 320312218722192874761037505)
    ·
      refine ⟨240234164041644656070778129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320312218722192874761037505 240234164041644656070778129)
      ·
        refine ⟨180175623031233492053083597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240234164041644656070778129 180175623031233492053083597)
        ·
          refine ⟨67565858636712559519906349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180175623031233492053083597 67565858636712559519906349)
          ·
            refine ⟨25337196988767209819964881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67565858636712559519906349 25337196988767209819964881)
            ·
              refine ⟨19002897741575407364973661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25337196988767209819964881 19002897741575407364973661)
              ·
                refine ⟨7126086653090777761865123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19002897741575407364973661 7126086653090777761865123)
                ·
                  refine ⟨10689129979636166642797685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126086653090777761865123 10689129979636166642797685)
                  ·
                    refine ⟨1002105935590890622762283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10689129979636166642797685 1002105935590890622762283)
                    ·
                      rfl

theorem cell23_5854783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_5854783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854783 prefixEnd_5854783 := by exact prefixLift 5854783
  have htrace : WordTrace (prefixWord ++ tailWord_5854783) baseStart_5854783 baseEnd_5854783 := by
    simpa [prefixWord, tailWord_5854783, baseEnd_5854783] using wordTrace_append hprefix tailTrace_5854783
  have hstable : (prefixWord ++ tailWord_5854783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854783).length < 2 ^ (prefixWord ++ tailWord_5854783).sum := by decide
  have hdescent : baseEnd_5854783 < baseStart_5854783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854820 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_5854820 : Nat := 118140960795 + 5854820 * 2 ^ 59
def prefixEnd_5854820 : Nat := 4983230072969 + 3 ^ 40 * 5854820 * 2
def baseEnd_5854820 : Nat := 3006336805556888223524179

theorem tailTrace_5854820 : CollatzResearch.WordTrace tailWord_5854820 prefixEnd_5854820 3006336805556888223524179 := by
  unfold tailWord_5854820
  simp only [CollatzResearch.WordTrace]
  refine ⟨106771414324497269246560957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142361885765996358995414609 106771414324497269246560957)
  ·
    refine ⟨40039280371686475967460359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106771414324497269246560957 40039280371686475967460359)
    ·
      refine ⟨60058920557529713951190539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40039280371686475967460359 60058920557529713951190539)
      ·
        refine ⟨90088380836294570926785809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60058920557529713951190539 90088380836294570926785809)
        ·
          refine ⟨67566285627220928195089357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90088380836294570926785809 67566285627220928195089357)
          ·
            refine ⟨25337357110207848073158509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67566285627220928195089357 25337357110207848073158509)
            ·
              refine ⟨9501508916327943027434441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25337357110207848073158509 9501508916327943027434441)
              ·
                refine ⟨7126131687245957270575831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9501508916327943027434441 7126131687245957270575831)
                ·
                  refine ⟨10689197530868935905863747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126131687245957270575831 10689197530868935905863747)
                  ·
                    refine ⟨16033796296303403858795621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10689197530868935905863747 16033796296303403858795621)
                    ·
                      refine ⟨3006336805556888223524179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16033796296303403858795621 3006336805556888223524179)
                      ·
                        rfl

theorem cell23_5854820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_5854820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854820 prefixEnd_5854820 := by exact prefixLift 5854820
  have htrace : WordTrace (prefixWord ++ tailWord_5854820) baseStart_5854820 baseEnd_5854820 := by
    simpa [prefixWord, tailWord_5854820, baseEnd_5854820] using wordTrace_append hprefix tailTrace_5854820
  have hstable : (prefixWord ++ tailWord_5854820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854820).length < 2 ^ (prefixWord ++ tailWord_5854820).sum := by decide
  have hdescent : baseEnd_5854820 < baseStart_5854820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854830 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_5854830 : Nat := 118140960795 + 5854830 * 2 ^ 59
def prefixEnd_5854830 : Nat := 4983230072969 + 3 ^ 40 * 5854830 * 2
def baseEnd_5854830 : Nat := 1002113980121144394799711

theorem tailTrace_5854830 : CollatzResearch.WordTrace tailWord_5854830 prefixEnd_5854830 1002113980121144394799711 := by
  unfold tailWord_5854830
  simp only [CollatzResearch.WordTrace]
  refine ⟨26692899172369788775123243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142362128919305540133990629 26692899172369788775123243)
  ·
    refine ⟨40039348758554683162684865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26692899172369788775123243 40039348758554683162684865)
    ·
      refine ⟨30029511568916012372013649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40039348758554683162684865 30029511568916012372013649)
      ·
        refine ⟨22522133676687009279010237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30029511568916012372013649 22522133676687009279010237)
        ·
          refine ⟨8445800128757628479628839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22522133676687009279010237 8445800128757628479628839)
          ·
            refine ⟨12668700193136442719443259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8445800128757628479628839 12668700193136442719443259)
            ·
              refine ⟨19003050289704664079164889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12668700193136442719443259 19003050289704664079164889)
              ·
                refine ⟨14252287717278498059373667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19003050289704664079164889 14252287717278498059373667)
                ·
                  refine ⟨21378431575917747089060501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14252287717278498059373667 21378431575917747089060501)
                  ·
                    refine ⟨1002113980121144394799711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21378431575917747089060501 1002113980121144394799711)
                    ·
                      rfl

theorem cell23_5854830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_5854830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854830 prefixEnd_5854830 := by exact prefixLift 5854830
  have htrace : WordTrace (prefixWord ++ tailWord_5854830) baseStart_5854830 baseEnd_5854830 := by
    simpa [prefixWord, tailWord_5854830, baseEnd_5854830] using wordTrace_append hprefix tailTrace_5854830
  have hstable : (prefixWord ++ tailWord_5854830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854830).length < 2 ^ (prefixWord ++ tailWord_5854830).sum := by decide
  have hdescent : baseEnd_5854830 < baseStart_5854830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854853 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_5854853 : Nat := 118140960795 + 5854853 * 2 ^ 59
def prefixEnd_5854853 : Nat := 4983230072969 + 3 ^ 40 * 5854853 * 2
def baseEnd_5854853 : Nat := 3006353750418486594411527

theorem tailTrace_5854853 : CollatzResearch.WordTrace tailWord_5854853 prefixEnd_5854853 3006353750418486594411527 := by
  unfold tailWord_5854853
  simp only [CollatzResearch.WordTrace]
  refine ⟨213544032257874985129073213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142362688171916656752715475 213544032257874985129073213)
  ·
    refine ⟨80079012096703119423402455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213544032257874985129073213 80079012096703119423402455)
    ·
      refine ⟨120118518145054679135103683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80079012096703119423402455 120118518145054679135103683)
      ·
        refine ⟨180177777217582018702655525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120118518145054679135103683 180177777217582018702655525)
        ·
          refine ⟨33783333228296628506747911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180177777217582018702655525 33783333228296628506747911)
          ·
            refine ⟨50674999842444942760121867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33783333228296628506747911 50674999842444942760121867)
            ·
              refine ⟨76012499763667414140182801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50674999842444942760121867 76012499763667414140182801)
              ·
                refine ⟨57009374822750560605137101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76012499763667414140182801 57009374822750560605137101)
                ·
                  refine ⟨21378515558531460226926413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57009374822750560605137101 21378515558531460226926413)
                  ·
                    refine ⟨8016943334449297585097405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21378515558531460226926413 8016943334449297585097405)
                    ·
                      refine ⟨3006353750418486594411527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8016943334449297585097405 3006353750418486594411527)
                      ·
                        rfl

theorem cell23_5854853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_5854853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854853 prefixEnd_5854853 := by exact prefixLift 5854853
  have htrace : WordTrace (prefixWord ++ tailWord_5854853) baseStart_5854853 baseEnd_5854853 := by
    simpa [prefixWord, tailWord_5854853, baseEnd_5854853] using wordTrace_append hprefix tailTrace_5854853
  have hstable : (prefixWord ++ tailWord_5854853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854853).length < 2 ^ (prefixWord ++ tailWord_5854853).sum := by decide
  have hdescent : baseEnd_5854853 < baseStart_5854853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854863 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 9, 2]
def baseStart_5854863 : Nat := 118140960795 + 5854863 * 2 ^ 59
def prefixEnd_5854863 : Nat := 4983230072969 + 3 ^ 40 * 5854863 * 2
def baseEnd_5854863 : Nat := 3006358885225031555286481

theorem tailTrace_5854863 : CollatzResearch.WordTrace tailWord_5854863 prefixEnd_5854863 3006358885225031555286481 := by
  unfold tailWord_5854863
  simp only [CollatzResearch.WordTrace]
  refine ⟨213544396987838756836937243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142362931325225837891291495 213544396987838756836937243)
  ·
    refine ⟨320316595481758135255405865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213544396987838756836937243 320316595481758135255405865)
    ·
      refine ⟨240237446611318601441554399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320316595481758135255405865 240237446611318601441554399)
      ·
        refine ⟨360356169916977902162331599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240237446611318601441554399 360356169916977902162331599)
        ·
          refine ⟨540534254875466853243497399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360356169916977902162331599 540534254875466853243497399)
          ·
            refine ⟨810801382313200279865246099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540534254875466853243497399 810801382313200279865246099)
            ·
              refine ⟨1216202073469800419797869149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810801382313200279865246099 1216202073469800419797869149)
              ·
                refine ⟨456075777551175157424200931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216202073469800419797869149 456075777551175157424200931)
                ·
                  refine ⟨684113666326762736136301397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456075777551175157424200931 684113666326762736136301397)
                  ·
                    refine ⟨4008478513633375407048641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 684113666326762736136301397 4008478513633375407048641)
                    ·
                      refine ⟨3006358885225031555286481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008478513633375407048641 3006358885225031555286481)
                      ·
                        rfl

theorem cell23_5854863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9, 2].length) (baseStart_5854863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854863 prefixEnd_5854863 := by exact prefixLift 5854863
  have htrace : WordTrace (prefixWord ++ tailWord_5854863) baseStart_5854863 baseEnd_5854863 := by
    simpa [prefixWord, tailWord_5854863, baseEnd_5854863] using wordTrace_append hprefix tailTrace_5854863
  have hstable : (prefixWord ++ tailWord_5854863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854863).length < 2 ^ (prefixWord ++ tailWord_5854863).sum := by decide
  have hdescent : baseEnd_5854863 < baseStart_5854863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854888 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5854888 : Nat := 118140960795 + 5854888 * 2 ^ 59
def prefixEnd_5854888 : Nat := 4983230072969 + 3 ^ 40 * 5854888 * 2
def baseEnd_5854888 : Nat := 3006371722241393957473867

theorem tailTrace_5854888 : CollatzResearch.WordTrace tailWord_5854888 prefixEnd_5854888 3006371722241393957473867 := by
  unfold tailWord_5854888
  simp only [CollatzResearch.WordTrace]
  refine ⟨106772654406374093053298659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142363539208498790737731545 106772654406374093053298659)
  ·
    refine ⟨160158981609561139579947989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106772654406374093053298659 160158981609561139579947989)
    ·
      refine ⟨3753726131474089208905031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 160158981609561139579947989 3753726131474089208905031)
      ·
        refine ⟨5630589197211133813357547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3753726131474089208905031 5630589197211133813357547)
        ·
          refine ⟨8445883795816700720036321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5630589197211133813357547 8445883795816700720036321)
          ·
            refine ⟨6334412846862525540027241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8445883795816700720036321 6334412846862525540027241)
            ·
              refine ⟨4750809635146894155020431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6334412846862525540027241 4750809635146894155020431)
              ·
                refine ⟨7126214452720341232530647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750809635146894155020431 7126214452720341232530647)
                ·
                  refine ⟨10689321679080511848795971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126214452720341232530647 10689321679080511848795971)
                  ·
                    refine ⟨16033982518620767773193957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10689321679080511848795971 16033982518620767773193957)
                    ·
                      refine ⟨3006371722241393957473867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16033982518620767773193957 3006371722241393957473867)
                      ·
                        rfl

theorem cell23_5854888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5854888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854888 prefixEnd_5854888 := by exact prefixLift 5854888
  have htrace : WordTrace (prefixWord ++ tailWord_5854888) baseStart_5854888 baseEnd_5854888 := by
    simpa [prefixWord, tailWord_5854888, baseEnd_5854888] using wordTrace_append hprefix tailTrace_5854888
  have hstable : (prefixWord ++ tailWord_5854888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854888).length < 2 ^ (prefixWord ++ tailWord_5854888).sum := by decide
  have hdescent : baseEnd_5854888 < baseStart_5854888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854903 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 2, 6]
def baseStart_5854903 : Nat := 118140960795 + 5854903 * 2 ^ 59
def prefixEnd_5854903 : Nat := 4983230072969 + 3 ^ 40 * 5854903 * 2
def baseEnd_5854903 : Nat := 1002126474817070466262099

theorem tailTrace_5854903 : CollatzResearch.WordTrace tailWord_5854903 prefixEnd_5854903 1002126474817070466262099 := by
  unfold tailWord_5854903
  simp only [CollatzResearch.WordTrace]
  refine ⟨213545855907693843668393363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142363903938462562445595575 213545855907693843668393363)
  ·
    refine ⟨320318783861540765502590045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213545855907693843668393363 320318783861540765502590045)
    ·
      refine ⟨120119543948077787063471267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320318783861540765502590045 120119543948077787063471267)
      ·
        refine ⟨180179315922116680595206901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120119543948077787063471267 180179315922116680595206901)
        ·
          refine ⟨16891810867698438805800647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180179315922116680595206901 16891810867698438805800647)
          ·
            refine ⟨25337716301547658208700971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16891810867698438805800647 25337716301547658208700971)
            ·
              refine ⟨38006574452321487313051457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25337716301547658208700971 38006574452321487313051457)
              ·
                refine ⟨28504930839241115484788593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38006574452321487313051457 28504930839241115484788593)
                ·
                  refine ⟨21378698129430836613591445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28504930839241115484788593 21378698129430836613591445)
                  ·
                    refine ⟨1002126474817070466262099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21378698129430836613591445 1002126474817070466262099)
                    ·
                      rfl

theorem cell23_5854903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_5854903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854903 prefixEnd_5854903 := by exact prefixLift 5854903
  have htrace : WordTrace (prefixWord ++ tailWord_5854903) baseStart_5854903 baseEnd_5854903 := by
    simpa [prefixWord, tailWord_5854903, baseEnd_5854903] using wordTrace_append hprefix tailTrace_5854903
  have hstable : (prefixWord ++ tailWord_5854903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854903).length < 2 ^ (prefixWord ++ tailWord_5854903).sum := by decide
  have hdescent : baseEnd_5854903 < baseStart_5854903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854927 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 2, 2, 2]
def baseStart_5854927 : Nat := 118140960795 + 5854927 * 2 ^ 59
def prefixEnd_5854927 : Nat := 4983230072969 + 3 ^ 40 * 5854927 * 2
def baseEnd_5854927 : Nat := 3006391747986919304886187

theorem tailTrace_5854927 : CollatzResearch.WordTrace tailWord_5854927 prefixEnd_5854927 3006391747986919304886187 := by
  unfold tailWord_5854927
  simp only [CollatzResearch.WordTrace]
  refine ⟨213546731259606895767267035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142364487506404597178178023 213546731259606895767267035)
  ·
    refine ⟨320320096889410343650900553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213546731259606895767267035 320320096889410343650900553)
    ·
      refine ⟨240240072667057757738175415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320320096889410343650900553 240240072667057757738175415)
      ·
        refine ⟨360360109000586636607263123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240240072667057757738175415 360360109000586636607263123)
        ·
          refine ⟨540540163500879954910894685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360360109000586636607263123 540540163500879954910894685)
          ·
            refine ⟨202702561312829983091585507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540540163500879954910894685 202702561312829983091585507)
            ·
              refine ⟨304053841969244974637378261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202702561312829983091585507 304053841969244974637378261)
              ·
                refine ⟨7126261921154179093063553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 304053841969244974637378261 7126261921154179093063553)
                ·
                  refine ⟨5344696440865634319797665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7126261921154179093063553 5344696440865634319797665)
                  ·
                    refine ⟨4008522330649225739848249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5344696440865634319797665 4008522330649225739848249)
                    ·
                      refine ⟨3006391747986919304886187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008522330649225739848249 3006391747986919304886187)
                      ·
                        rfl

theorem cell23_5854927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 2, 2].length) (baseStart_5854927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854927 prefixEnd_5854927 := by exact prefixLift 5854927
  have htrace : WordTrace (prefixWord ++ tailWord_5854927) baseStart_5854927 baseEnd_5854927 := by
    simpa [prefixWord, tailWord_5854927, baseEnd_5854927] using wordTrace_append hprefix tailTrace_5854927
  have hstable : (prefixWord ++ tailWord_5854927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854927).length < 2 ^ (prefixWord ++ tailWord_5854927).sum := by decide
  have hdescent : baseEnd_5854927 < baseStart_5854927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854963 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 4, 5]
def baseStart_5854963 : Nat := 118140960795 + 5854963 * 2 ^ 59
def prefixEnd_5854963 : Nat := 4983230072969 + 3 ^ 40 * 5854963 * 2
def baseEnd_5854963 : Nat := 1002136744430160388012007

theorem tailTrace_5854963 : CollatzResearch.WordTrace tailWord_5854963 prefixEnd_5854963 1002136744430160388012007 := by
  unfold tailWord_5854963
  simp only [CollatzResearch.WordTrace]
  refine ⟨213548044287476473915577543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142365362858317649277051695 213548044287476473915577543)
  ·
    refine ⟨320322066431214710873366315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213548044287476473915577543 320322066431214710873366315)
    ·
      refine ⟨480483099646822066310049473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320322066431214710873366315 480483099646822066310049473)
      ·
        refine ⟨360362324735116549732537105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480483099646822066310049473 360362324735116549732537105)
        ·
          refine ⟨270271743551337412299402829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360362324735116549732537105 270271743551337412299402829)
          ·
            refine ⟨101351903831751529612276061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270271743551337412299402829 101351903831751529612276061)
            ·
              refine ⟨38006963936906823604603523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101351903831751529612276061 38006963936906823604603523)
              ·
                refine ⟨57010445905360235406905285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38006963936906823604603523 57010445905360235406905285)
                ·
                  refine ⟨10689458607255044138794741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57010445905360235406905285 10689458607255044138794741)
                  ·
                    refine ⟨1002136744430160388012007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10689458607255044138794741 1002136744430160388012007)
                    ·
                      rfl

theorem cell23_5854963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 5].length) (baseStart_5854963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854963 prefixEnd_5854963 := by exact prefixLift 5854963
  have htrace : WordTrace (prefixWord ++ tailWord_5854963) baseStart_5854963 baseEnd_5854963 := by
    simpa [prefixWord, tailWord_5854963, baseEnd_5854963] using wordTrace_append hprefix tailTrace_5854963
  have hstable : (prefixWord ++ tailWord_5854963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854963).length < 2 ^ (prefixWord ++ tailWord_5854963).sum := by decide
  have hdescent : baseEnd_5854963 < baseStart_5854963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5854970 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2]
def baseStart_5854970 : Nat := 118140960795 + 5854970 * 2 ^ 59
def prefixEnd_5854970 : Nat := 4983230072969 + 3 ^ 40 * 5854970 * 2
def baseEnd_5854970 : Nat := 3006413827655062636648489

theorem tailTrace_5854970 : CollatzResearch.WordTrace tailWord_5854970 prefixEnd_5854970 3006413827655062636648489 := by
  unfold tailWord_5854970
  simp only [CollatzResearch.WordTrace]
  refine ⟨53387074899612778527770591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142365533065634076074054909 53387074899612778527770591)
  ·
    refine ⟨80080612349419167791655887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53387074899612778527770591 80080612349419167791655887)
    ·
      refine ⟨120120918524128751687483831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80080612349419167791655887 120120918524128751687483831)
      ·
        refine ⟨180181377786193127531225747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120120918524128751687483831 180181377786193127531225747)
        ·
          refine ⟨270272066679289691296838621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180181377786193127531225747 270272066679289691296838621)
          ·
            refine ⟨101352025004733634236314483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270272066679289691296838621 101352025004733634236314483)
            ·
              refine ⟨152028037507100451354471725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101352025004733634236314483 152028037507100451354471725)
              ·
                refine ⟨57010514065162669257926897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152028037507100451354471725 57010514065162669257926897)
                ·
                  refine ⟨42757885548872001943445173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57010514065162669257926897 42757885548872001943445173)
                  ·
                    refine ⟨4008551770206750182197985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42757885548872001943445173 4008551770206750182197985)
                    ·
                      refine ⟨3006413827655062636648489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008551770206750182197985 3006413827655062636648489)
                      ·
                        rfl

theorem cell23_5854970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_5854970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5854970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5854970 prefixEnd_5854970 := by exact prefixLift 5854970
  have htrace : WordTrace (prefixWord ++ tailWord_5854970) baseStart_5854970 baseEnd_5854970 := by
    simpa [prefixWord, tailWord_5854970, baseEnd_5854970] using wordTrace_append hprefix tailTrace_5854970
  have hstable : (prefixWord ++ tailWord_5854970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5854970).length < 2 ^ (prefixWord ++ tailWord_5854970).sum := by decide
  have hdescent : baseEnd_5854970 < baseStart_5854970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5854970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855000 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_5855000 : Nat := 118140960795 + 5855000 * 2 ^ 59
def prefixEnd_5855000 : Nat := 4983230072969 + 3 ^ 40 * 5855000 * 2
def baseEnd_5855000 : Nat := 3006429232074697519273351

theorem tailTrace_5855000 : CollatzResearch.WordTrace tailWord_5855000 prefixEnd_5855000 3006429232074697519273351 := by
  unfold tailWord_5855000
  simp only [CollatzResearch.WordTrace]
  refine ⟨106774696894171214617337227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142366262525561619489782969 106774696894171214617337227)
  ·
    refine ⟨160162045341256821926005841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106774696894171214617337227 160162045341256821926005841)
    ·
      refine ⟨120121534005942616444504381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160162045341256821926005841 120121534005942616444504381)
      ·
        refine ⟨45045575252228481166689143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120121534005942616444504381 45045575252228481166689143)
        ·
          refine ⟨67568362878342721750033715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45045575252228481166689143 67568362878342721750033715)
          ·
            refine ⟨101352544317514082625050573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67568362878342721750033715 101352544317514082625050573)
            ·
              refine ⟨38007204119067780984393965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101352544317514082625050573 38007204119067780984393965)
              ·
                refine ⟨14252701544650417869147737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38007204119067780984393965 14252701544650417869147737)
                ·
                  refine ⟨10689526158487813401860803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14252701544650417869147737 10689526158487813401860803)
                  ·
                    refine ⟨16034289237731720102791205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10689526158487813401860803 16034289237731720102791205)
                    ·
                      refine ⟨3006429232074697519273351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16034289237731720102791205 3006429232074697519273351)
                      ·
                        rfl

theorem cell23_5855000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_5855000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855000 prefixEnd_5855000 := by exact prefixLift 5855000
  have htrace : WordTrace (prefixWord ++ tailWord_5855000) baseStart_5855000 baseEnd_5855000 := by
    simpa [prefixWord, tailWord_5855000, baseEnd_5855000] using wordTrace_append hprefix tailTrace_5855000
  have hstable : (prefixWord ++ tailWord_5855000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855000).length < 2 ^ (prefixWord ++ tailWord_5855000).sum := by decide
  have hdescent : baseEnd_5855000 < baseStart_5855000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855074 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 6]
def baseStart_5855074 : Nat := 118140960795 + 5855074 * 2 ^ 59
def prefixEnd_5855074 : Nat := 4983230072969 + 3 ^ 40 * 5855074 * 2
def baseEnd_5855074 : Nat := 334051914404792247749779

theorem tailTrace_5855074 : CollatzResearch.WordTrace tailWord_5855074 prefixEnd_5855074 334051914404792247749779 := by
  unfold tailWord_5855074
  simp only [CollatzResearch.WordTrace]
  refine ⟨53388023197518584968217069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142368061860049559915245517 53388023197518584968217069)
  ·
    refine ⟨20020508699069469363081401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53388023197518584968217069 20020508699069469363081401)
    ·
      refine ⟨15015381524302102022311051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20020508699069469363081401 15015381524302102022311051)
      ·
        refine ⟨22523072286453153033466577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15015381524302102022311051 22523072286453153033466577)
        ·
          refine ⟨16892304214839864775099933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22523072286453153033466577 16892304214839864775099933)
          ·
            refine ⟨6334614080564949290662475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16892304214839864775099933 6334614080564949290662475)
            ·
              refine ⟨9501921120847423935993713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6334614080564949290662475 9501921120847423935993713)
              ·
                refine ⟨7126440840635567951995285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9501921120847423935993713 7126440840635567951995285)
                ·
                  refine ⟨334051914404792247749779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7126440840635567951995285 334051914404792247749779)
                  ·
                    rfl

theorem cell23_5855074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_5855074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855074 prefixEnd_5855074 := by exact prefixLift 5855074
  have htrace : WordTrace (prefixWord ++ tailWord_5855074) baseStart_5855074 baseEnd_5855074 := by
    simpa [prefixWord, tailWord_5855074, baseEnd_5855074] using wordTrace_append hprefix tailTrace_5855074
  have hstable : (prefixWord ++ tailWord_5855074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855074).length < 2 ^ (prefixWord ++ tailWord_5855074).sum := by decide
  have hdescent : baseEnd_5855074 < baseStart_5855074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855077 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 4, 3, 2]
def baseStart_5855077 : Nat := 118140960795 + 5855077 * 2 ^ 59
def prefixEnd_5855077 : Nat := 4983230072969 + 3 ^ 40 * 5855077 * 2
def baseEnd_5855077 : Nat := 3006468770085093718010497

theorem tailTrace_5855077 : CollatzResearch.WordTrace tailWord_5855077 prefixEnd_5855077 3006468770085093718010497 := by
  unfold tailWord_5855077
  simp only [CollatzResearch.WordTrace]
  refine ⟨213552202209063471385227485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142368134806042314256818323 213552202209063471385227485)
  ·
    refine ⟨80082075828398801769460307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213552202209063471385227485 80082075828398801769460307)
    ·
      refine ⟨120123113742598202654190461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80082075828398801769460307 120123113742598202654190461)
      ·
        refine ⟨45046167653474325995321423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120123113742598202654190461 45046167653474325995321423)
        ·
          refine ⟨67569251480211488992982135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45046167653474325995321423 67569251480211488992982135)
          ·
            refine ⟨101353877220317233489473203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67569251480211488992982135 101353877220317233489473203)
            ·
              refine ⟨152030815830475850234209805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101353877220317233489473203 152030815830475850234209805)
              ·
                refine ⟨57011555936428443837828677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152030815830475850234209805 57011555936428443837828677)
                ·
                  refine ⟨10689666738080333219592877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57011555936428443837828677 10689666738080333219592877)
                  ·
                    refine ⟨4008625026780124957347329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10689666738080333219592877 4008625026780124957347329)
                    ·
                      refine ⟨3006468770085093718010497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008625026780124957347329 3006468770085093718010497)
                      ·
                        rfl

theorem cell23_5855077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_5855077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855077 prefixEnd_5855077 := by exact prefixLift 5855077
  have htrace : WordTrace (prefixWord ++ tailWord_5855077) baseStart_5855077 baseEnd_5855077 := by
    simpa [prefixWord, tailWord_5855077, baseEnd_5855077] using wordTrace_append hprefix tailTrace_5855077
  have hstable : (prefixWord ++ tailWord_5855077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855077).length < 2 ^ (prefixWord ++ tailWord_5855077).sum := by decide
  have hdescent : baseEnd_5855077 < baseStart_5855077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855084 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_5855084 : Nat := 118140960795 + 5855084 * 2 ^ 59
def prefixEnd_5855084 : Nat := 4983230072969 + 3 ^ 40 * 5855084 * 2
def baseEnd_5855084 : Nat := 3006472364449675190622965

theorem tailTrace_5855084 : CollatzResearch.WordTrace tailWord_5855084 prefixEnd_5855084 3006472364449675190622965 := by
  unfold tailWord_5855084
  simp only [CollatzResearch.WordTrace]
  refine ⟨106776228760019055790366153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142368305013358741053821537 106776228760019055790366153)
  ·
    refine ⟨80082171570014291842774615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106776228760019055790366153 80082171570014291842774615)
    ·
      refine ⟨120123257355021437764161923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80082171570014291842774615 120123257355021437764161923)
      ·
        refine ⟨180184886032532156646242885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120123257355021437764161923 180184886032532156646242885)
        ·
          refine ⟨33784666131099779371170541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180184886032532156646242885 33784666131099779371170541)
          ·
            refine ⟨12669249799162417264188953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33784666131099779371170541 12669249799162417264188953)
            ·
              refine ⟨9501937349371812948141715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12669249799162417264188953 9501937349371812948141715)
              ·
                refine ⟨14252906024057719422212573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9501937349371812948141715 14252906024057719422212573)
                ·
                  refine ⟨5344839759021644783329715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14252906024057719422212573 5344839759021644783329715)
                  ·
                    refine ⟨8017259638532467174994573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5344839759021644783329715 8017259638532467174994573)
                    ·
                      refine ⟨3006472364449675190622965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8017259638532467174994573 3006472364449675190622965)
                      ·
                        rfl

theorem cell23_5855084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_5855084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855084 prefixEnd_5855084 := by exact prefixLift 5855084
  have htrace : WordTrace (prefixWord ++ tailWord_5855084) baseStart_5855084 baseEnd_5855084 := by
    simpa [prefixWord, tailWord_5855084, baseEnd_5855084] using wordTrace_append hprefix tailTrace_5855084
  have hstable : (prefixWord ++ tailWord_5855084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855084).length < 2 ^ (prefixWord ++ tailWord_5855084).sum := by decide
  have hdescent : baseEnd_5855084 < baseStart_5855084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
