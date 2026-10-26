import V185TrunkScan19Chunk031

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_320903 : List Nat := [1, 1, 4, 2, 2, 3, 6]
def baseStart_320903 : Nat := 118140960795 + 320903 * 2 ^ 59
def prefixEnd_320903 : Nat := 4983230072969 + 3 ^ 40 * 320903 * 2
def baseEnd_320903 : Nat := 32548638512565570219595

theorem tailTrace_320903 : CollatzResearch.WordTrace tailWord_320903 prefixEnd_320903 32548638512565570219595 := by
  unfold tailWord_320903
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704293956430711714191363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7802862637620474476127575 11704293956430711714191363)
  ·
    refine ⟨17556440934646067571287045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11704293956430711714191363 17556440934646067571287045)
    ·
      refine ⟨3291832675246137669616321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17556440934646067571287045 3291832675246137669616321)
      ·
        refine ⟨2468874506434603252212241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3291832675246137669616321 2468874506434603252212241)
        ·
          refine ⟨1851655879825952439159181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2468874506434603252212241 1851655879825952439159181)
          ·
            refine ⟨694370954934732164684693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1851655879825952439159181 694370954934732164684693)
            ·
              refine ⟨32548638512565570219595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 694370954934732164684693 32548638512565570219595)
              ·
                rfl

theorem cell19_320903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_320903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320903 prefixEnd_320903 := by exact prefixLift 320903
  have htrace : WordTrace (prefixWord ++ tailWord_320903) baseStart_320903 baseEnd_320903 := by
    simpa [prefixWord, tailWord_320903, baseEnd_320903] using wordTrace_append hprefix tailTrace_320903
  have hstable : (prefixWord ++ tailWord_320903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320903).length < 2 ^ (prefixWord ++ tailWord_320903).sum := by decide
  have hdescent : baseEnd_320903 < baseStart_320903 := by decide
  rcases family_descends (prefixWord ++ tailWord_320903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320922 : List Nat := [3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_320922 : Nat := 118140960795 + 320922 * 2 ^ 59
def prefixEnd_320922 : Nat := 4983230072969 + 3 ^ 40 * 320922 * 2
def baseEnd_320922 : Nat := 97651696949510296236511

theorem tailTrace_320922 : CollatzResearch.WordTrace tailWord_320922 prefixEnd_320922 97651696949510296236511 := by
  unfold tailWord_320922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2926246735840469489783255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7803324628907918639422013 2926246735840469489783255)
  ·
    refine ⟨4389370103760704234674883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2926246735840469489783255 4389370103760704234674883)
    ·
      refine ⟨6584055155641056352012325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4389370103760704234674883 6584055155641056352012325)
      ·
        refine ⟨1234510341682698066002311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6584055155641056352012325 1234510341682698066002311)
        ·
          refine ⟨1851765512524047099003467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234510341682698066002311 1851765512524047099003467)
          ·
            refine ⟨2777648268786070648505201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851765512524047099003467 2777648268786070648505201)
            ·
              refine ⟨2083236201589552986378901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2777648268786070648505201 2083236201589552986378901)
              ·
                refine ⟨97651696949510296236511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2083236201589552986378901 97651696949510296236511)
                ·
                  rfl

theorem cell19_320922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_320922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320922 prefixEnd_320922 := by exact prefixLift 320922
  have htrace : WordTrace (prefixWord ++ tailWord_320922) baseStart_320922 baseEnd_320922 := by
    simpa [prefixWord, tailWord_320922, baseEnd_320922] using wordTrace_append hprefix tailTrace_320922
  have hstable : (prefixWord ++ tailWord_320922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320922).length < 2 ^ (prefixWord ++ tailWord_320922).sum := by decide
  have hdescent : baseEnd_320922 < baseStart_320922 := by decide
  rcases family_descends (prefixWord ++ tailWord_320922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320956 : List Nat := [2, 2, 2, 4, 3, 1, 5]
def baseStart_320956 : Nat := 118140960795 + 320956 * 2 ^ 59
def prefixEnd_320956 : Nat := 4983230072969 + 3 ^ 40 * 320956 * 2
def baseEnd_320956 : Nat := 32554014211269430493621

theorem tailTrace_320956 : CollatzResearch.WordTrace tailWord_320956 prefixEnd_320956 32554014211269430493621 := by
  unfold tailWord_320956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853113512619350882935361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7804151350159134510580481 5853113512619350882935361)
  ·
    refine ⟨4389835134464513162201521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5853113512619350882935361 4389835134464513162201521)
    ·
      refine ⟨3292376350848384871651141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4389835134464513162201521 3292376350848384871651141)
      ·
        refine ⟨617320565784072163434589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3292376350848384871651141 617320565784072163434589)
        ·
          refine ⟨231495212169027061287971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617320565784072163434589 231495212169027061287971)
          ·
            refine ⟨347242818253540591931957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231495212169027061287971 347242818253540591931957)
            ·
              refine ⟨32554014211269430493621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 347242818253540591931957 32554014211269430493621)
              ·
                rfl

theorem cell19_320956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_320956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320956 prefixEnd_320956 := by exact prefixLift 320956
  have htrace : WordTrace (prefixWord ++ tailWord_320956) baseStart_320956 baseEnd_320956 := by
    simpa [prefixWord, tailWord_320956, baseEnd_320956] using wordTrace_append hprefix tailTrace_320956
  have hstable : (prefixWord ++ tailWord_320956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320956).length < 2 ^ (prefixWord ++ tailWord_320956).sum := by decide
  have hdescent : baseEnd_320956 < baseStart_320956 := by decide
  rcases family_descends (prefixWord ++ tailWord_320956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321034 : List Nat := [3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_321034 : Nat := 118140960795 + 321034 * 2 ^ 59
def prefixEnd_321034 : Nat := 4983230072969 + 3 ^ 40 * 321034 * 2
def baseEnd_321034 : Nat := 97685776850727221747317

theorem tailTrace_321034 : CollatzResearch.WordTrace tailWord_321034 prefixEnd_321034 97685776850727221747317 := by
  unfold tailWord_321034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927267979739030271802539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7806047945970747391473437 2927267979739030271802539)
  ·
    refine ⟨4390901969608545407703809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2927267979739030271802539 4390901969608545407703809)
    ·
      refine ⟨3293176477206409055777857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4390901969608545407703809 3293176477206409055777857)
      ·
        refine ⟨2469882357904806791833393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3293176477206409055777857 2469882357904806791833393)
        ·
          refine ⟨1852411768428605093875045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2469882357904806791833393 1852411768428605093875045)
          ·
            refine ⟨347327206580363455101571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1852411768428605093875045 347327206580363455101571)
            ·
              refine ⟨520990809870545182652357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347327206580363455101571 520990809870545182652357)
              ·
                refine ⟨97685776850727221747317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 520990809870545182652357 97685776850727221747317)
                ·
                  rfl

theorem cell19_321034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_321034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321034 prefixEnd_321034 := by exact prefixLift 321034
  have htrace : WordTrace (prefixWord ++ tailWord_321034) baseStart_321034 baseEnd_321034 := by
    simpa [prefixWord, tailWord_321034, baseEnd_321034] using wordTrace_append hprefix tailTrace_321034
  have hstable : (prefixWord ++ tailWord_321034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321034).length < 2 ^ (prefixWord ++ tailWord_321034).sum := by decide
  have hdescent : baseEnd_321034 < baseStart_321034 := by decide
  rcases family_descends (prefixWord ++ tailWord_321034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321053 : List Nat := [1, 4, 2, 2, 1, 1, 5, 3]
def baseStart_321053 : Nat := 118140960795 + 321053 * 2 ^ 59
def prefixEnd_321053 : Nat := 4983230072969 + 3 ^ 40 * 321053 * 2
def baseEnd_321053 : Nat := 97691558262540807325043

theorem tailTrace_321053 : CollatzResearch.WordTrace tailWord_321053 prefixEnd_321053 97691558262540807325043 := by
  unfold tailWord_321053
  simp only [CollatzResearch.WordTrace]
  refine ⟨11709764905887287332151813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7806509937258191554767875 11709764905887287332151813)
  ·
    refine ⟨2195580919853866374778465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11709764905887287332151813 2195580919853866374778465)
    ·
      refine ⟨1646685689890399781083849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2195580919853866374778465 1646685689890399781083849)
      ·
        refine ⟨1235014267417799835812887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1646685689890399781083849 1235014267417799835812887)
        ·
          refine ⟨1852521401126699753719331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235014267417799835812887 1852521401126699753719331)
          ·
            refine ⟨2778782101690049630578997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852521401126699753719331 2778782101690049630578997)
            ·
              refine ⟨260510822033442152866781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2778782101690049630578997 260510822033442152866781)
              ·
                refine ⟨97691558262540807325043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260510822033442152866781 97691558262540807325043)
                ·
                  rfl

theorem cell19_321053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_321053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321053 prefixEnd_321053 := by exact prefixLift 321053
  have htrace : WordTrace (prefixWord ++ tailWord_321053) baseStart_321053 baseEnd_321053 := by
    simpa [prefixWord, tailWord_321053, baseEnd_321053] using wordTrace_append hprefix tailTrace_321053
  have hstable : (prefixWord ++ tailWord_321053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321053).length < 2 ^ (prefixWord ++ tailWord_321053).sum := by decide
  have hdescent : baseEnd_321053 < baseStart_321053 := by decide
  rcases family_descends (prefixWord ++ tailWord_321053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321186 : List Nat := [3, 3, 1, 4, 1, 7]
def baseStart_321186 : Nat := 118140960795 + 321186 * 2 ^ 59
def prefixEnd_321186 : Nat := 4983230072969 + 3 ^ 40 * 321186 * 2
def baseEnd_321186 : Nat := 10859114238359545152125

theorem tailTrace_321186 : CollatzResearch.WordTrace tailWord_321186 prefixEnd_321186 10859114238359545152125 := by
  unfold tailWord_321186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928653953601362761685853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7809743876270300697828941 2928653953601362761685853)
  ·
    refine ⟨1098245232600511035632195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2928653953601362761685853 1098245232600511035632195)
    ·
      refine ⟨1647367848900766553448293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1098245232600511035632195 1647367848900766553448293)
      ·
        refine ⟨308881471668893728771555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1647367848900766553448293 308881471668893728771555)
        ·
          refine ⟨463322207503340593157333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308881471668893728771555 463322207503340593157333)
          ·
            refine ⟨10859114238359545152125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 463322207503340593157333 10859114238359545152125)
            ·
              rfl

theorem cell19_321186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 7].length) (baseStart_321186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321186 prefixEnd_321186 := by exact prefixLift 321186
  have htrace : WordTrace (prefixWord ++ tailWord_321186) baseStart_321186 baseEnd_321186 := by
    simpa [prefixWord, tailWord_321186, baseEnd_321186] using wordTrace_append hprefix tailTrace_321186
  have hstable : (prefixWord ++ tailWord_321186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321186).length < 2 ^ (prefixWord ++ tailWord_321186).sum := by decide
  have hdescent : baseEnd_321186 < baseStart_321186 := by decide
  rcases family_descends (prefixWord ++ tailWord_321186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321207 : List Nat := [1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_321207 : Nat := 118140960795 + 321207 * 2 ^ 59
def prefixEnd_321207 : Nat := 4983230072969 + 3 ^ 40 * 321207 * 2
def baseEnd_321207 : Nat := 97738418126714079902401

theorem tailTrace_321207 : CollatzResearch.WordTrace tailWord_321207 prefixEnd_321207 97738418126714079902401 := by
  unfold tailWord_321207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11715381747329371633257875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7810254498219581088838583 11715381747329371633257875)
  ·
    refine ⟨17573072620994057449886813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11715381747329371633257875 17573072620994057449886813)
    ·
      refine ⟨6589902232872771543707555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17573072620994057449886813 6589902232872771543707555)
      ·
        refine ⟨9884853349309157315561333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6589902232872771543707555 9884853349309157315561333)
        ·
          refine ⟨926705001497733498333875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9884853349309157315561333 926705001497733498333875)
          ·
            refine ⟨1390057502246600247500813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926705001497733498333875 1390057502246600247500813)
            ·
              refine ⟨521271563342475092812805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1390057502246600247500813 521271563342475092812805)
              ·
                refine ⟨97738418126714079902401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521271563342475092812805 97738418126714079902401)
                ·
                  rfl

theorem cell19_321207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_321207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321207 prefixEnd_321207 := by exact prefixLift 321207
  have htrace : WordTrace (prefixWord ++ tailWord_321207) baseStart_321207 baseEnd_321207 := by
    simpa [prefixWord, tailWord_321207, baseEnd_321207] using wordTrace_append hprefix tailTrace_321207
  have hstable : (prefixWord ++ tailWord_321207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321207).length < 2 ^ (prefixWord ++ tailWord_321207).sum := by decide
  have hdescent : baseEnd_321207 < baseStart_321207 := by decide
  rcases family_descends (prefixWord ++ tailWord_321207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321218 : List Nat := [3, 5, 1, 2, 1, 1, 3, 3]
def baseStart_321218 : Nat := 118140960795 + 321218 * 2 ^ 59
def prefixEnd_321218 : Nat := 4983230072969 + 3 ^ 40 * 321218 * 2
def baseEnd_321218 : Nat := 97741765259869313657927

theorem tailTrace_321218 : CollatzResearch.WordTrace tailWord_321218 prefixEnd_321218 97741765259869313657927 := by
  unfold tailWord_321218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928945737572380127977077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7810521966859680341272205 2928945737572380127977077)
  ·
    refine ⟨274588662897410636997851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2928945737572380127977077 274588662897410636997851)
    ·
      refine ⟨411882994346115955496777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274588662897410636997851 411882994346115955496777)
      ·
        refine ⟨308912245759586966622583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411882994346115955496777 308912245759586966622583)
        ·
          refine ⟨463368368639380449933875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308912245759586966622583 463368368639380449933875)
          ·
            refine ⟨695052552959070674900813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463368368639380449933875 695052552959070674900813)
            ·
              refine ⟨260644707359651503087805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 695052552959070674900813 260644707359651503087805)
              ·
                refine ⟨97741765259869313657927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260644707359651503087805 97741765259869313657927)
                ·
                  rfl

theorem cell19_321218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_321218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321218 prefixEnd_321218 := by exact prefixLift 321218
  have htrace : WordTrace (prefixWord ++ tailWord_321218) baseStart_321218 baseEnd_321218 := by
    simpa [prefixWord, tailWord_321218, baseEnd_321218] using wordTrace_append hprefix tailTrace_321218
  have hstable : (prefixWord ++ tailWord_321218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321218).length < 2 ^ (prefixWord ++ tailWord_321218).sum := by decide
  have hdescent : baseEnd_321218 < baseStart_321218 := by decide
  rcases family_descends (prefixWord ++ tailWord_321218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321247 : List Nat := [1, 1, 2, 3, 2, 2, 8]
def baseStart_321247 : Nat := 118140960795 + 321247 * 2 ^ 59
def prefixEnd_321247 : Nat := 4983230072969 + 3 ^ 40 * 321247 * 2
def baseEnd_321247 : Nat := 32583529840001946337801

theorem tailTrace_321247 : CollatzResearch.WordTrace tailWord_321247 prefixEnd_321247 32583529840001946337801 := by
  unfold tailWord_321247
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716840667184458464713995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7811227111456305643142663 11716840667184458464713995)
  ·
    refine ⟨17575261000776687697070993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11716840667184458464713995 17575261000776687697070993)
    ·
      refine ⟨13181445750582515772803245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17575261000776687697070993 13181445750582515772803245)
      ·
        refine ⟨4943042156468443414801217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13181445750582515772803245 4943042156468443414801217)
        ·
          refine ⟨3707281617351332561100913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4943042156468443414801217 3707281617351332561100913)
          ·
            refine ⟨2780461213013499420825685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3707281617351332561100913 2780461213013499420825685)
            ·
              refine ⟨32583529840001946337801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2780461213013499420825685 32583529840001946337801)
              ·
                rfl

theorem cell19_321247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_321247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321247 prefixEnd_321247 := by exact prefixLift 321247
  have htrace : WordTrace (prefixWord ++ tailWord_321247) baseStart_321247 baseEnd_321247 := by
    simpa [prefixWord, tailWord_321247, baseEnd_321247] using wordTrace_append hprefix tailTrace_321247
  have hstable : (prefixWord ++ tailWord_321247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321247).length < 2 ^ (prefixWord ++ tailWord_321247).sum := by decide
  have hdescent : baseEnd_321247 < baseStart_321247 := by decide
  rcases family_descends (prefixWord ++ tailWord_321247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321283 : List Nat := [1, 1, 1, 3, 2, 2, 6, 3]
def baseStart_321283 : Nat := 118140960795 + 321283 * 2 ^ 59
def prefixEnd_321283 : Nat := 4983230072969 + 3 ^ 40 * 321283 * 2
def baseEnd_321283 : Nat := 97761543773968422213305

theorem tailTrace_321283 : CollatzResearch.WordTrace tailWord_321283 prefixEnd_321283 97761543773968422213305 := by
  unfold tailWord_321283
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718153695054036613024503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7812102463369357742016335 11718153695054036613024503)
  ·
    refine ⟨17577230542581054919536755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718153695054036613024503 17577230542581054919536755)
    ·
      refine ⟨26365845813871582379305133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17577230542581054919536755 26365845813871582379305133)
      ·
        refine ⟨9887192180201843392239425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26365845813871582379305133 9887192180201843392239425)
        ·
          refine ⟨7415394135151382544179569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9887192180201843392239425 7415394135151382544179569)
          ·
            refine ⟨5561545601363536908134677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7415394135151382544179569 5561545601363536908134677)
            ·
              refine ⟨260697450063915792568813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5561545601363536908134677 260697450063915792568813)
              ·
                refine ⟨97761543773968422213305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260697450063915792568813 97761543773968422213305)
                ·
                  rfl

theorem cell19_321283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_321283 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321283 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321283 prefixEnd_321283 := by exact prefixLift 321283
  have htrace : WordTrace (prefixWord ++ tailWord_321283) baseStart_321283 baseEnd_321283 := by
    simpa [prefixWord, tailWord_321283, baseEnd_321283] using wordTrace_append hprefix tailTrace_321283
  have hstable : (prefixWord ++ tailWord_321283).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321283).length < 2 ^ (prefixWord ++ tailWord_321283).sum := by decide
  have hdescent : baseEnd_321283 < baseStart_321283 := by decide
  rcases family_descends (prefixWord ++ tailWord_321283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321304 : List Nat := [2, 1, 2, 3, 1, 1, 9]
def baseStart_321304 : Nat := 118140960795 + 321304 * 2 ^ 59
def prefixEnd_321304 : Nat := 4983230072969 + 3 ^ 40 * 321304 * 2
def baseEnd_321304 : Nat := 32589311251815531915527

theorem tailTrace_321304 : CollatzResearch.WordTrace tailWord_321304 prefixEnd_321304 32589311251815531915527 := by
  unfold tailWord_321304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5859459813988978599769483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7812613085318638133025977 5859459813988978599769483)
  ·
    refine ⟨8789189720983467899654225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5859459813988978599769483 8789189720983467899654225)
    ·
      refine ⟨6591892290737600924740669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8789189720983467899654225 6591892290737600924740669)
      ·
        refine ⟨2471959609026600346777751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6591892290737600924740669 2471959609026600346777751)
        ·
          refine ⟨3707939413539900520166627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471959609026600346777751 3707939413539900520166627)
          ·
            refine ⟨5561909120309850780249941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707939413539900520166627 5561909120309850780249941)
            ·
              refine ⟨32589311251815531915527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5561909120309850780249941 32589311251815531915527)
              ·
                rfl

theorem cell19_321304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_321304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321304 prefixEnd_321304 := by exact prefixLift 321304
  have htrace : WordTrace (prefixWord ++ tailWord_321304) baseStart_321304 baseEnd_321304 := by
    simpa [prefixWord, tailWord_321304, baseEnd_321304] using wordTrace_append hprefix tailTrace_321304
  have hstable : (prefixWord ++ tailWord_321304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321304).length < 2 ^ (prefixWord ++ tailWord_321304).sum := by decide
  have hdescent : baseEnd_321304 < baseStart_321304 := by decide
  rcases family_descends (prefixWord ++ tailWord_321304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321361 : List Nat := [1, 2, 2, 1, 5, 8]
def baseStart_321361 : Nat := 118140960795 + 321361 * 2 ^ 59
def prefixEnd_321361 : Nat := 4983230072969 + 3 ^ 40 * 321361 * 2
def baseEnd_321361 : Nat := 10865030887876372497751

theorem tailTrace_321361 : CollatzResearch.WordTrace tailWord_321361 prefixEnd_321361 10865030887876372497751 := by
  unfold tailWord_321361
  simp only [CollatzResearch.WordTrace]
  refine ⟨11720998588771455934363937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7813999059180970622909291 11720998588771455934363937)
  ·
    refine ⟨8790748941578591950772953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11720998588771455934363937 8790748941578591950772953)
    ·
      refine ⟨6593061706183943963079715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8790748941578591950772953 6593061706183943963079715)
      ·
        refine ⟨9889592559275915944619573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6593061706183943963079715 9889592559275915944619573)
        ·
          refine ⟨927149302432117119808085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9889592559275915944619573 927149302432117119808085)
          ·
            refine ⟨10865030887876372497751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 927149302432117119808085 10865030887876372497751)
            ·
              rfl

theorem cell19_321361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_321361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321361 prefixEnd_321361 := by exact prefixLift 321361
  have htrace : WordTrace (prefixWord ++ tailWord_321361) baseStart_321361 baseEnd_321361 := by
    simpa [prefixWord, tailWord_321361, baseEnd_321361] using wordTrace_append hprefix tailTrace_321361
  have hstable : (prefixWord ++ tailWord_321361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321361).length < 2 ^ (prefixWord ++ tailWord_321361).sum := by decide
  have hdescent : baseEnd_321361 < baseStart_321361 := by decide
  rcases family_descends (prefixWord ++ tailWord_321361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321416 : List Nat := [2, 1, 3, 3, 3, 1, 6]
def baseStart_321416 : Nat := 118140960795 + 321416 * 2 ^ 59
def prefixEnd_321416 : Nat := 4983230072969 + 3 ^ 40 * 321416 * 2
def baseEnd_321416 : Nat := 32600671218887840419129

theorem tailTrace_321416 : CollatzResearch.WordTrace tailWord_321416 prefixEnd_321416 32600671218887840419129 := by
  unfold tailWord_321416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861502301786100163808051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7815336402381466885077401 5861502301786100163808051)
  ·
    refine ⟨8792253452679150245712077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5861502301786100163808051 8792253452679150245712077)
    ·
      refine ⟨3297095044754681342142029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8792253452679150245712077 3297095044754681342142029)
      ·
        refine ⟨1236410641783005503303261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3297095044754681342142029 1236410641783005503303261)
        ·
          refine ⟨463653990668627063738723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1236410641783005503303261 463653990668627063738723)
          ·
            refine ⟨695480986002940595608085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463653990668627063738723 695480986002940595608085)
            ·
              refine ⟨32600671218887840419129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 695480986002940595608085 32600671218887840419129)
              ·
                rfl

theorem cell19_321416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_321416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321416 prefixEnd_321416 := by exact prefixLift 321416
  have htrace : WordTrace (prefixWord ++ tailWord_321416) baseStart_321416 baseEnd_321416 := by
    simpa [prefixWord, tailWord_321416, baseEnd_321416] using wordTrace_append hprefix tailTrace_321416
  have hstable : (prefixWord ++ tailWord_321416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321416).length < 2 ^ (prefixWord ++ tailWord_321416).sum := by decide
  have hdescent : baseEnd_321416 < baseStart_321416 := by decide
  rcases family_descends (prefixWord ++ tailWord_321416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321448 : List Nat := [2, 1, 6, 2, 1, 2, 2, 3]
def baseStart_321448 : Nat := 118140960795 + 321448 * 2 ^ 59
def prefixEnd_321448 : Nat := 4983230072969 + 3 ^ 40 * 321448 * 2
def baseEnd_321448 : Nat := 97811750771296928546189

theorem tailTrace_321448 : CollatzResearch.WordTrace tailWord_321448 prefixEnd_321448 97811750771296928546189 := by
  unfold tailWord_321448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862085869728134896390499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7816114492970846528520665 5862085869728134896390499)
  ·
    refine ⟨8793128804592202344585749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862085869728134896390499 8793128804592202344585749)
    ·
      refine ⟨412177912715259484902457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8793128804592202344585749 412177912715259484902457)
      ·
        refine ⟨309133434536444613676843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412177912715259484902457 309133434536444613676843)
        ·
          refine ⟨463700151804666920515265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309133434536444613676843 463700151804666920515265)
          ·
            refine ⟨347775113853500190386449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463700151804666920515265 347775113853500190386449)
            ·
              refine ⟨260831335390125142789837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347775113853500190386449 260831335390125142789837)
              ·
                refine ⟨97811750771296928546189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260831335390125142789837 97811750771296928546189)
                ·
                  rfl

theorem cell19_321448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_321448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321448 prefixEnd_321448 := by exact prefixLift 321448
  have htrace : WordTrace (prefixWord ++ tailWord_321448) baseStart_321448 baseEnd_321448 := by
    simpa [prefixWord, tailWord_321448, baseEnd_321448] using wordTrace_append hprefix tailTrace_321448
  have hstable : (prefixWord ++ tailWord_321448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321448).length < 2 ^ (prefixWord ++ tailWord_321448).sum := by decide
  have hdescent : baseEnd_321448 < baseStart_321448 := by decide
  rcases family_descends (prefixWord ++ tailWord_321448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321490 : List Nat := [3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_321490 : Nat := 118140960795 + 321490 * 2 ^ 59
def prefixEnd_321490 : Nat := 4983230072969 + 3 ^ 40 * 321490 * 2
def baseEnd_321490 : Nat := 97824530734253275612741

theorem tailTrace_321490 : CollatzResearch.WordTrace tailWord_321490 prefixEnd_321490 97824530734253275612741 := by
  unfold tailWord_321490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931425901326027741452481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7817135736869407310539949 2931425901326027741452481)
  ·
    refine ⟨2198569425994520806089361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2931425901326027741452481 2198569425994520806089361)
    ·
      refine ⟨1648927069495890604567021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2198569425994520806089361 1648927069495890604567021)
      ·
        refine ⟨618347651060958976712633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1648927069495890604567021 618347651060958976712633)
        ·
          refine ⟨463760738295719232534475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618347651060958976712633 463760738295719232534475)
          ·
            refine ⟨695641107443578848801713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463760738295719232534475 695641107443578848801713)
            ·
              refine ⟨521730830582684136601285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695641107443578848801713 521730830582684136601285)
              ·
                refine ⟨97824530734253275612741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521730830582684136601285 97824530734253275612741)
                ·
                  rfl

theorem cell19_321490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_321490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321490 prefixEnd_321490 := by exact prefixLift 321490
  have htrace : WordTrace (prefixWord ++ tailWord_321490) baseStart_321490 baseEnd_321490 := by
    simpa [prefixWord, tailWord_321490, baseEnd_321490] using wordTrace_append hprefix tailTrace_321490
  have hstable : (prefixWord ++ tailWord_321490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321490).length < 2 ^ (prefixWord ++ tailWord_321490).sum := by decide
  have hdescent : baseEnd_321490 < baseStart_321490 := by decide
  rcases family_descends (prefixWord ++ tailWord_321490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321492 : List Nat := [2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_321492 : Nat := 118140960795 + 321492 * 2 ^ 59
def prefixEnd_321492 : Nat := 4983230072969 + 3 ^ 40 * 321492 * 2
def baseEnd_321492 : Nat := 97825139303917863568291

theorem tailTrace_321492 : CollatzResearch.WordTrace tailWord_321492 prefixEnd_321492 97825139303917863568291 := by
  unfold tailWord_321492
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862888275648432653691365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7817184367531243538255153 5862888275648432653691365)
  ·
    refine ⟨1099291551684081122567131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5862888275648432653691365 1099291551684081122567131)
    ·
      refine ⟨1648937327526121683850697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099291551684081122567131 1648937327526121683850697)
      ·
        refine ⟨1236702995644591262888023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1648937327526121683850697 1236702995644591262888023)
        ·
          refine ⟨1855054493466886894332035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236702995644591262888023 1855054493466886894332035)
          ·
            refine ⟨2782581740200330341498053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855054493466886894332035 2782581740200330341498053)
            ·
              refine ⟨521734076287561939030885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2782581740200330341498053 521734076287561939030885)
              ·
                refine ⟨97825139303917863568291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521734076287561939030885 97825139303917863568291)
                ·
                  rfl

theorem cell19_321492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_321492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321492 prefixEnd_321492 := by exact prefixLift 321492
  have htrace : WordTrace (prefixWord ++ tailWord_321492) baseStart_321492 baseEnd_321492 := by
    simpa [prefixWord, tailWord_321492, baseEnd_321492] using wordTrace_append hprefix tailTrace_321492
  have hstable : (prefixWord ++ tailWord_321492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321492).length < 2 ^ (prefixWord ++ tailWord_321492).sum := by decide
  have hdescent : baseEnd_321492 < baseStart_321492 := by decide
  rcases family_descends (prefixWord ++ tailWord_321492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321642 : List Nat := [3, 1, 3, 2, 4, 1, 5]
def baseStart_321642 : Nat := 118140960795 + 321642 * 2 ^ 59
def prefixEnd_321642 : Nat := 4983230072969 + 3 ^ 40 * 321642 * 2
def baseEnd_321642 : Nat := 32623594009587320078183

theorem tailTrace_321642 : CollatzResearch.WordTrace tailWord_321642 prefixEnd_321642 32623594009587320078183 := by
  unfold tailWord_321642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932811875188360231335795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7820831667168960616895453 2932811875188360231335795)
  ·
    refine ⟨4399217812782540347003693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2932811875188360231335795 4399217812782540347003693)
    ·
      refine ⟨1649706679793452630126385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4399217812782540347003693 1649706679793452630126385)
      ·
        refine ⟨1237280009845089472594789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649706679793452630126385 1237280009845089472594789)
        ·
          refine ⟨231990001845954276111523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1237280009845089472594789 231990001845954276111523)
          ·
            refine ⟨347985002768931414167285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231990001845954276111523 347985002768931414167285)
            ·
              refine ⟨32623594009587320078183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 347985002768931414167285 32623594009587320078183)
              ·
                rfl

theorem cell19_321642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_321642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321642 prefixEnd_321642 := by exact prefixLift 321642
  have htrace : WordTrace (prefixWord ++ tailWord_321642) baseStart_321642 baseEnd_321642 := by
    simpa [prefixWord, tailWord_321642, baseEnd_321642] using wordTrace_append hprefix tailTrace_321642
  have hstable : (prefixWord ++ tailWord_321642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321642).length < 2 ^ (prefixWord ++ tailWord_321642).sum := by decide
  have hdescent : baseEnd_321642 < baseStart_321642 := by decide
  rcases family_descends (prefixWord ++ tailWord_321642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321703 : List Nat := [1, 1, 6, 2, 9]
def baseStart_321703 : Nat := 118140960795 + 321703 * 2 ^ 59
def prefixEnd_321703 : Nat := 4983230072969 + 3 ^ 40 * 321703 * 2
def baseEnd_321703 : Nat := 3625531237167847884401

theorem tailTrace_321703 : CollatzResearch.WordTrace tailWord_321703 prefixEnd_321703 3625531237167847884401 := by
  unfold tailWord_321703
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733472353532448343313763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7822314902354965562209175 11733472353532448343313763)
  ·
    refine ⟨17600208530298672514970645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11733472353532448343313763 17600208530298672514970645)
    ·
      refine ⟨825009774857750274139249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17600208530298672514970645 825009774857750274139249)
      ·
        refine ⟨618757331143312705604437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 825009774857750274139249 618757331143312705604437)
        ·
          refine ⟨3625531237167847884401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 618757331143312705604437 3625531237167847884401)
          ·
            rfl

theorem cell19_321703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 9].length) (baseStart_321703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321703 prefixEnd_321703 := by exact prefixLift 321703
  have htrace : WordTrace (prefixWord ++ tailWord_321703) baseStart_321703 baseEnd_321703 := by
    simpa [prefixWord, tailWord_321703, baseEnd_321703] using wordTrace_append hprefix tailTrace_321703
  have hstable : (prefixWord ++ tailWord_321703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321703).length < 2 ^ (prefixWord ++ tailWord_321703).sum := by decide
  have hdescent : baseEnd_321703 < baseStart_321703 := by decide
  rcases family_descends (prefixWord ++ tailWord_321703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321722 : List Nat := [3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_321722 : Nat := 118140960795 + 321722 * 2 ^ 59
def prefixEnd_321722 : Nat := 4983230072969 + 3 ^ 40 * 321722 * 2
def baseEnd_321722 : Nat := 97895124815345478456553

theorem tailTrace_321722 : CollatzResearch.WordTrace tailWord_321722 prefixEnd_321722 97895124815345478456553 := by
  unfold tailWord_321722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933541335115903647063855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7822776893642409725503613 2933541335115903647063855)
  ·
    refine ⟨4400312002673855470595783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2933541335115903647063855 4400312002673855470595783)
    ·
      refine ⟨6600468004010783205893675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400312002673855470595783 6600468004010783205893675)
      ·
        refine ⟨9900702006016174808840513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6600468004010783205893675 9900702006016174808840513)
        ·
          refine ⟨7425526504512131106630385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9900702006016174808840513 7425526504512131106630385)
          ·
            refine ⟨5569144878384098329972789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7425526504512131106630385 5569144878384098329972789)
            ·
              refine ⟨522107332348509218434949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5569144878384098329972789 522107332348509218434949)
              ·
                refine ⟨97895124815345478456553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522107332348509218434949 97895124815345478456553)
                ·
                  rfl

theorem cell19_321722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_321722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321722 prefixEnd_321722 := by exact prefixLift 321722
  have htrace : WordTrace (prefixWord ++ tailWord_321722) baseStart_321722 baseEnd_321722 := by
    simpa [prefixWord, tailWord_321722, baseEnd_321722] using wordTrace_append hprefix tailTrace_321722
  have hstable : (prefixWord ++ tailWord_321722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321722).length < 2 ^ (prefixWord ++ tailWord_321722).sum := by decide
  have hdescent : baseEnd_321722 < baseStart_321722 := by decide
  rcases family_descends (prefixWord ++ tailWord_321722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321756 : List Nat := [2, 2, 5, 2, 1, 1, 6]
def baseStart_321756 : Nat := 118140960795 + 321756 * 2 ^ 59
def prefixEnd_321756 : Nat := 4983230072969 + 3 ^ 40 * 321756 * 2
def baseEnd_321756 : Nat := 32635156833214491233635

theorem tailTrace_321756 : CollatzResearch.WordTrace tailWord_321756 prefixEnd_321756 32635156833214491233635 := by
  unfold tailWord_321756
  simp only [CollatzResearch.WordTrace]
  refine ⟨5867702711170219197496561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7823603614893625596662081 5867702711170219197496561)
  ·
    refine ⟨4400777033377664398122421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5867702711170219197496561 4400777033377664398122421)
    ·
      refine ⟨412572846879156037323977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4400777033377664398122421 412572846879156037323977)
      ·
        refine ⟨309429635159367027992983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412572846879156037323977 309429635159367027992983)
        ·
          refine ⟨464144452739050541989475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309429635159367027992983 464144452739050541989475)
          ·
            refine ⟨696216679108575812984213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464144452739050541989475 696216679108575812984213)
            ·
              refine ⟨32635156833214491233635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 696216679108575812984213 32635156833214491233635)
              ·
                rfl

theorem cell19_321756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_321756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321756 prefixEnd_321756 := by exact prefixLift 321756
  have htrace : WordTrace (prefixWord ++ tailWord_321756) baseStart_321756 baseEnd_321756 := by
    simpa [prefixWord, tailWord_321756, baseEnd_321756] using wordTrace_append hprefix tailTrace_321756
  have hstable : (prefixWord ++ tailWord_321756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321756).length < 2 ^ (prefixWord ++ tailWord_321756).sum := by decide
  have hdescent : baseEnd_321756 < baseStart_321756 := by decide
  rcases family_descends (prefixWord ++ tailWord_321756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321794 : List Nat := [3, 4, 1, 1, 2, 1, 4, 3]
def baseStart_321794 : Nat := 118140960795 + 321794 * 2 ^ 59
def prefixEnd_321794 : Nat := 4983230072969 + 3 ^ 40 * 321794 * 2
def baseEnd_321794 : Nat := 97917033323270644856357

theorem tailTrace_321794 : CollatzResearch.WordTrace tailWord_321794 prefixEnd_321794 97917033323270644856357 := by
  unfold tailWord_321794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934197849050692721219109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7824527597468513923250957 2934197849050692721219109)
  ·
    refine ⟨550162096697004885228583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2934197849050692721219109 550162096697004885228583)
    ·
      refine ⟨825243145045507327842875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550162096697004885228583 825243145045507327842875)
      ·
        refine ⟨1237864717568260991764313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825243145045507327842875 1237864717568260991764313)
        ·
          refine ⟨928398538176195743823235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1237864717568260991764313 928398538176195743823235)
          ·
            refine ⟨1392597807264293615734853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928398538176195743823235 1392597807264293615734853)
            ·
              refine ⟨261112088862055052950285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1392597807264293615734853 261112088862055052950285)
              ·
                refine ⟨97917033323270644856357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261112088862055052950285 97917033323270644856357)
                ·
                  rfl

theorem cell19_321794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_321794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321794 prefixEnd_321794 := by exact prefixLift 321794
  have htrace : WordTrace (prefixWord ++ tailWord_321794) baseStart_321794 baseEnd_321794 := by
    simpa [prefixWord, tailWord_321794, baseEnd_321794] using wordTrace_append hprefix tailTrace_321794
  have hstable : (prefixWord ++ tailWord_321794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321794).length < 2 ^ (prefixWord ++ tailWord_321794).sum := by decide
  have hdescent : baseEnd_321794 < baseStart_321794 := by decide
  rcases family_descends (prefixWord ++ tailWord_321794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321796 : List Nat := [2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_321796 : Nat := 118140960795 + 321796 * 2 ^ 59
def prefixEnd_321796 : Nat := 4983230072969 + 3 ^ 40 * 321796 * 2
def baseEnd_321796 : Nat := 97917641892935232811907

theorem tailTrace_321796 : CollatzResearch.WordTrace tailWord_321796 prefixEnd_321796 97917641892935232811907 := by
  unfold tailWord_321796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868432171097762613224621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7824576228130350150966161 5868432171097762613224621)
  ·
    refine ⟨2200662064161660979959233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5868432171097762613224621 2200662064161660979959233)
    ·
      refine ⟨1650496548121245734969425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2200662064161660979959233 1650496548121245734969425)
      ·
        refine ⟨1237872411090934301227069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1650496548121245734969425 1237872411090934301227069)
        ·
          refine ⟨464202154159100362960151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1237872411090934301227069 464202154159100362960151)
          ·
            refine ⟨696303231238650544440227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464202154159100362960151 696303231238650544440227)
            ·
              refine ⟨1044454846857975816660341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696303231238650544440227 1044454846857975816660341)
              ·
                refine ⟨97917641892935232811907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1044454846857975816660341 97917641892935232811907)
                ·
                  rfl

theorem cell19_321796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_321796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321796 prefixEnd_321796 := by exact prefixLift 321796
  have htrace : WordTrace (prefixWord ++ tailWord_321796) baseStart_321796 baseEnd_321796 := by
    simpa [prefixWord, tailWord_321796, baseEnd_321796] using wordTrace_append hprefix tailTrace_321796
  have hstable : (prefixWord ++ tailWord_321796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321796).length < 2 ^ (prefixWord ++ tailWord_321796).sum := by decide
  have hdescent : baseEnd_321796 < baseStart_321796 := by decide
  rcases family_descends (prefixWord ++ tailWord_321796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321819 : List Nat := [1, 1, 1, 1, 1, 1, 13]
def baseStart_321819 : Nat := 118140960795 + 321819 * 2 ^ 59
def prefixEnd_321819 : Nat := 4983230072969 + 3 ^ 40 * 321819 * 2
def baseEnd_321819 : Nat := 32641546814692664766911

theorem tailTrace_321819 : CollatzResearch.WordTrace tailWord_321819 prefixEnd_321819 32641546814692664766911 := by
  unfold tailWord_321819
  simp only [CollatzResearch.WordTrace]
  refine ⟨11737703221112200154536511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7825135480741466769691007 11737703221112200154536511)
  ·
    refine ⟨17606554831668300231804767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11737703221112200154536511 17606554831668300231804767)
    ·
      refine ⟨26409832247502450347707151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17606554831668300231804767 26409832247502450347707151)
      ·
        refine ⟨39614748371253675521560727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26409832247502450347707151 39614748371253675521560727)
        ·
          refine ⟨59422122556880513282341091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39614748371253675521560727 59422122556880513282341091)
          ·
            refine ⟨89133183835320769923511637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59422122556880513282341091 89133183835320769923511637)
            ·
              refine ⟨32641546814692664766911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 89133183835320769923511637 32641546814692664766911)
              ·
                rfl

theorem cell19_321819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_321819 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321819 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321819 prefixEnd_321819 := by exact prefixLift 321819
  have htrace : WordTrace (prefixWord ++ tailWord_321819) baseStart_321819 baseEnd_321819 := by
    simpa [prefixWord, tailWord_321819, baseEnd_321819] using wordTrace_append hprefix tailTrace_321819
  have hstable : (prefixWord ++ tailWord_321819).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321819).length < 2 ^ (prefixWord ++ tailWord_321819).sum := by decide
  have hdescent : baseEnd_321819 < baseStart_321819 := by decide
  rcases family_descends (prefixWord ++ tailWord_321819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321893 : List Nat := [1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_321893 : Nat := 118140960795 + 321893 * 2 ^ 59
def prefixEnd_321893 : Nat := 4983230072969 + 3 ^ 40 * 321893 * 2
def baseEnd_321893 : Nat := 97947157521667748656087

theorem tailTrace_321893 : CollatzResearch.WordTrace tailWord_321893 prefixEnd_321893 97947157521667748656087 := by
  unfold tailWord_321893
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740402222844110792730333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7826934815229407195153555 11740402222844110792730333)
  ·
    refine ⟨4402650833566541547273875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11740402222844110792730333 4402650833566541547273875)
    ·
      refine ⟨6603976250349812320910813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4402650833566541547273875 6603976250349812320910813)
      ·
        refine ⟨2476491093881179620341555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6603976250349812320910813 2476491093881179620341555)
        ·
          refine ⟨3714736640821769430512333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476491093881179620341555 3714736640821769430512333)
          ·
            refine ⟨1393026240308163536442125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3714736640821769430512333 1393026240308163536442125)
            ·
              refine ⟨522384840115561326165797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1393026240308163536442125 522384840115561326165797)
              ·
                refine ⟨97947157521667748656087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522384840115561326165797 97947157521667748656087)
                ·
                  rfl

theorem cell19_321893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_321893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321893 prefixEnd_321893 := by exact prefixLift 321893
  have htrace : WordTrace (prefixWord ++ tailWord_321893) baseStart_321893 baseEnd_321893 := by
    simpa [prefixWord, tailWord_321893, baseEnd_321893] using wordTrace_append hprefix tailTrace_321893
  have hstable : (prefixWord ++ tailWord_321893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321893).length < 2 ^ (prefixWord ++ tailWord_321893).sum := by decide
  have hdescent : baseEnd_321893 < baseStart_321893 := by decide
  rcases family_descends (prefixWord ++ tailWord_321893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321969 : List Nat := [1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_321969 : Nat := 118140960795 + 321969 * 2 ^ 59
def prefixEnd_321969 : Nat := 4983230072969 + 3 ^ 40 * 321969 * 2
def baseEnd_321969 : Nat := 97970283168922090966991

theorem tailTrace_321969 : CollatzResearch.WordTrace tailWord_321969 prefixEnd_321969 97970283168922090966991 := by
  unfold tailWord_321969
  simp only [CollatzResearch.WordTrace]
  refine ⟨11743174170568775772496961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7828782780379183848331307 11743174170568775772496961)
  ·
    refine ⟨8807380627926581829372721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11743174170568775772496961 8807380627926581829372721)
    ·
      refine ⟨6605535470944936372029541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8807380627926581829372721 6605535470944936372029541)
      ·
        refine ⟨1238537900802175569755539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6605535470944936372029541 1238537900802175569755539)
        ·
          refine ⟨1857806851203263354633309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238537900802175569755539 1857806851203263354633309)
          ·
            refine ⟨696677569201223757987491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1857806851203263354633309 696677569201223757987491)
            ·
              refine ⟨1045016353801835636981237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696677569201223757987491 1045016353801835636981237)
              ·
                refine ⟨97970283168922090966991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1045016353801835636981237 97970283168922090966991)
                ·
                  rfl

theorem cell19_321969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_321969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_321969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_321969 prefixEnd_321969 := by exact prefixLift 321969
  have htrace : WordTrace (prefixWord ++ tailWord_321969) baseStart_321969 baseEnd_321969 := by
    simpa [prefixWord, tailWord_321969, baseEnd_321969] using wordTrace_append hprefix tailTrace_321969
  have hstable : (prefixWord ++ tailWord_321969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321969).length < 2 ^ (prefixWord ++ tailWord_321969).sum := by decide
  have hdescent : baseEnd_321969 < baseStart_321969 := by decide
  rcases family_descends (prefixWord ++ tailWord_321969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322026 : List Nat := [3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_322026 : Nat := 118140960795 + 322026 * 2 ^ 59
def prefixEnd_322026 : Nat := 4983230072969 + 3 ^ 40 * 322026 * 2
def baseEnd_322026 : Nat := 97987627404362847700169

theorem tailTrace_322026 : CollatzResearch.WordTrace tailWord_322026 prefixEnd_322026 97987627404362847700169 := by
  unfold tailWord_322026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936313282840568626830483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7830168754241516338214621 2936313282840568626830483)
  ·
    refine ⟨4404469924260852940245725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2936313282840568626830483 4404469924260852940245725)
    ·
      refine ⟨1651676221597819852592147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4404469924260852940245725 1651676221597819852592147)
      ·
        refine ⟨2477514332396729778888221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651676221597819852592147 2477514332396729778888221)
        ·
          refine ⟨929067874648773667083083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2477514332396729778888221 929067874648773667083083)
          ·
            refine ⟨1393601811973160500624625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929067874648773667083083 1393601811973160500624625)
            ·
              refine ⟨1045201358979870375468469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393601811973160500624625 1045201358979870375468469)
              ·
                refine ⟨97987627404362847700169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1045201358979870375468469 97987627404362847700169)
                ·
                  rfl

theorem cell19_322026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_322026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322026 prefixEnd_322026 := by exact prefixLift 322026
  have htrace : WordTrace (prefixWord ++ tailWord_322026) baseStart_322026 baseEnd_322026 := by
    simpa [prefixWord, tailWord_322026, baseEnd_322026] using wordTrace_append hprefix tailTrace_322026
  have hstable : (prefixWord ++ tailWord_322026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322026).length < 2 ^ (prefixWord ++ tailWord_322026).sum := by decide
  have hdescent : baseEnd_322026 < baseStart_322026 := by decide
  rcases family_descends (prefixWord ++ tailWord_322026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322028 : List Nat := [2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_322028 : Nat := 118140960795 + 322028 * 2 ^ 59
def prefixEnd_322028 : Nat := 4983230072969 + 3 ^ 40 * 322028 * 2
def baseEnd_322028 : Nat := 97988235974027435655719

theorem tailTrace_322028 : CollatzResearch.WordTrace tailWord_322028 prefixEnd_322028 97988235974027435655719 := by
  unfold tailWord_322028
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872663038677514424447369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7830217384903352565929825 5872663038677514424447369)
  ·
    refine ⟨4404497279008135818335527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5872663038677514424447369 4404497279008135818335527)
    ·
      refine ⟨6606745918512203727503291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4404497279008135818335527 6606745918512203727503291)
      ·
        refine ⟨9910118877768305591254937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6606745918512203727503291 9910118877768305591254937)
        ·
          refine ⟨7432589158326229193441203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9910118877768305591254937 7432589158326229193441203)
          ·
            refine ⟨11148883737489343790161805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7432589158326229193441203 11148883737489343790161805)
            ·
              refine ⟨4180831401558503921310677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11148883737489343790161805 4180831401558503921310677)
              ·
                refine ⟨97988235974027435655719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4180831401558503921310677 97988235974027435655719)
                ·
                  rfl

theorem cell19_322028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_322028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322028 prefixEnd_322028 := by exact prefixLift 322028
  have htrace : WordTrace (prefixWord ++ tailWord_322028) baseStart_322028 baseEnd_322028 := by
    simpa [prefixWord, tailWord_322028, baseEnd_322028] using wordTrace_append hprefix tailTrace_322028
  have hstable : (prefixWord ++ tailWord_322028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322028).length < 2 ^ (prefixWord ++ tailWord_322028).sum := by decide
  have hdescent : baseEnd_322028 < baseStart_322028 := by decide
  rcases family_descends (prefixWord ++ tailWord_322028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322062 : List Nat := [4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_322062 : Nat := 118140960795 + 322062 * 2 ^ 59
def prefixEnd_322062 : Nat := 4983230072969 + 3 ^ 40 * 322062 * 2
def baseEnd_322062 : Nat := 97998581658325430900071

theorem tailTrace_322062 : CollatzResearch.WordTrace tailWord_322062 prefixEnd_322062 97998581658325430900071 := by
  unfold tailWord_322062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468320769903981581954055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7831044106154568437088293 1468320769903981581954055)
  ·
    refine ⟨2202481154855972372931083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468320769903981581954055 2202481154855972372931083)
    ·
      refine ⟨3303721732283958559396625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202481154855972372931083 3303721732283958559396625)
      ·
        refine ⟨2477791299212968919547469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3303721732283958559396625 2477791299212968919547469)
        ·
          refine ⟨929171737204863344830301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2477791299212968919547469 929171737204863344830301)
          ·
            refine ⟨348439401451823754311363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 929171737204863344830301 348439401451823754311363)
            ·
              refine ⟨522659102177735631467045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348439401451823754311363 522659102177735631467045)
              ·
                refine ⟨97998581658325430900071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522659102177735631467045 97998581658325430900071)
                ·
                  rfl

theorem cell19_322062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_322062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322062 prefixEnd_322062 := by exact prefixLift 322062
  have htrace : WordTrace (prefixWord ++ tailWord_322062) baseStart_322062 baseEnd_322062 := by
    simpa [prefixWord, tailWord_322062, baseEnd_322062] using wordTrace_append hprefix tailTrace_322062
  have hstable : (prefixWord ++ tailWord_322062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322062).length < 2 ^ (prefixWord ++ tailWord_322062).sum := by decide
  have hdescent : baseEnd_322062 < baseStart_322062 := by decide
  rcases family_descends (prefixWord ++ tailWord_322062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322085 : List Nat := [1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_322085 : Nat := 118140960795 + 322085 * 2 ^ 59
def prefixEnd_322085 : Nat := 4983230072969 + 3 ^ 40 * 322085 * 2
def baseEnd_322085 : Nat := 98005580209468192388897

theorem tailTrace_322085 : CollatzResearch.WordTrace tailWord_322085 prefixEnd_322085 98005580209468192388897 := by
  unfold tailWord_322085
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747405038148527583719709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7831603358765685055813139 11747405038148527583719709)
  ·
    refine ⟨4405276889305697843894891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11747405038148527583719709 4405276889305697843894891)
    ·
      refine ⟨6607915333958546765842337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4405276889305697843894891 6607915333958546765842337)
      ·
        refine ⟨4955936500468910074381753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6607915333958546765842337 4955936500468910074381753)
        ·
          refine ⟨3716952375351682555786315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4955936500468910074381753 3716952375351682555786315)
          ·
            refine ⟨5575428563027523833679473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3716952375351682555786315 5575428563027523833679473)
            ·
              refine ⟨4181571422270642875259605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575428563027523833679473 4181571422270642875259605)
              ·
                refine ⟨98005580209468192388897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4181571422270642875259605 98005580209468192388897)
                ·
                  rfl

theorem cell19_322085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_322085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322085 prefixEnd_322085 := by exact prefixLift 322085
  have htrace : WordTrace (prefixWord ++ tailWord_322085) baseStart_322085 baseEnd_322085 := by
    simpa [prefixWord, tailWord_322085, baseEnd_322085] using wordTrace_append hprefix tailTrace_322085
  have hstable : (prefixWord ++ tailWord_322085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322085).length < 2 ^ (prefixWord ++ tailWord_322085).sum := by decide
  have hdescent : baseEnd_322085 < baseStart_322085 := by decide
  rcases family_descends (prefixWord ++ tailWord_322085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322104 : List Nat := [2, 1, 2, 1, 4, 1, 8]
def baseStart_322104 : Nat := 118140960795 + 322104 * 2 ^ 59
def prefixEnd_322104 : Nat := 4983230072969 + 3 ^ 40 * 322104 * 2
def baseEnd_322104 : Nat := 32670453873760592655541

theorem tailTrace_322104 : CollatzResearch.WordTrace tailWord_322104 prefixEnd_322104 32670453873760592655541 := by
  unfold tailWord_322104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874049012539846914330683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7832065350053129219107577 5874049012539846914330683)
  ·
    refine ⟨8811073518809770371496025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5874049012539846914330683 8811073518809770371496025)
    ·
      refine ⟨6608305139107327778622019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8811073518809770371496025 6608305139107327778622019)
      ·
        refine ⟨9912457708660991667933029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608305139107327778622019 9912457708660991667933029)
        ·
          refine ⟨1858585820373935937737443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9912457708660991667933029 1858585820373935937737443)
          ·
            refine ⟨2787878730560903906606165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858585820373935937737443 2787878730560903906606165)
            ·
              refine ⟨32670453873760592655541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2787878730560903906606165 32670453873760592655541)
              ·
                rfl

theorem cell19_322104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_322104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322104 prefixEnd_322104 := by exact prefixLift 322104
  have htrace : WordTrace (prefixWord ++ tailWord_322104) baseStart_322104 baseEnd_322104 := by
    simpa [prefixWord, tailWord_322104, baseEnd_322104] using wordTrace_append hprefix tailTrace_322104
  have hstable : (prefixWord ++ tailWord_322104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322104).length < 2 ^ (prefixWord ++ tailWord_322104).sum := by decide
  have hdescent : baseEnd_322104 < baseStart_322104 := by decide
  rcases family_descends (prefixWord ++ tailWord_322104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322199 : List Nat := [1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_322199 : Nat := 118140960795 + 322199 * 2 ^ 59
def prefixEnd_322199 : Nat := 4983230072969 + 3 ^ 40 * 322199 * 2
def baseEnd_322199 : Nat := 98040268680349705855253

theorem tailTrace_322199 : CollatzResearch.WordTrace tailWord_322199 prefixEnd_322199 98040268680349705855253 := by
  unfold tailWord_322199
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751562959735525053369651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7834375306490350035579767 11751562959735525053369651)
  ·
    refine ⟨17627344439603287580054477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11751562959735525053369651 17627344439603287580054477)
    ·
      refine ⟨6610254164851232842520429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17627344439603287580054477 6610254164851232842520429)
      ·
        refine ⟨2478845311819212315945161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6610254164851232842520429 2478845311819212315945161)
        ·
          refine ⟨1859133983864409236958871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2478845311819212315945161 1859133983864409236958871)
          ·
            refine ⟨2788700975796613855438307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859133983864409236958871 2788700975796613855438307)
            ·
              refine ⟨4183051463694920783157461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788700975796613855438307 4183051463694920783157461)
              ·
                refine ⟨98040268680349705855253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4183051463694920783157461 98040268680349705855253)
                ·
                  rfl

theorem cell19_322199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_322199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322199 prefixEnd_322199 := by exact prefixLift 322199
  have htrace : WordTrace (prefixWord ++ tailWord_322199) baseStart_322199 baseEnd_322199 := by
    simpa [prefixWord, tailWord_322199, baseEnd_322199] using wordTrace_append hprefix tailTrace_322199
  have hstable : (prefixWord ++ tailWord_322199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322199).length < 2 ^ (prefixWord ++ tailWord_322199).sum := by decide
  have hdescent : baseEnd_322199 < baseStart_322199 := by decide
  rcases family_descends (prefixWord ++ tailWord_322199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322216 : List Nat := [2, 1, 7, 9]
def baseStart_322216 : Nat := 118140960795 + 322216 * 2 ^ 59
def prefixEnd_322216 : Nat := 4983230072969 + 3 ^ 40 * 322216 * 2
def baseEnd_322216 : Nat := 1210437549660477820709

theorem tailTrace_322216 : CollatzResearch.WordTrace tailWord_322216 prefixEnd_322216 1210437549660477820709 := by
  unfold tailWord_322216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876091500336968478369251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7834788667115957971159001 5876091500336968478369251)
  ·
    refine ⟨8814137250505452717553877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5876091500336968478369251 8814137250505452717553877)
    ·
      refine ⟨206581341808721548067669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8814137250505452717553877 206581341808721548067669)
      ·
        refine ⟨1210437549660477820709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 206581341808721548067669 1210437549660477820709)
        ·
          rfl

theorem cell19_322216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 9].length) (baseStart_322216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322216 prefixEnd_322216 := by exact prefixLift 322216
  have htrace : WordTrace (prefixWord ++ tailWord_322216) baseStart_322216 baseEnd_322216 := by
    simpa [prefixWord, tailWord_322216, baseEnd_322216] using wordTrace_append hprefix tailTrace_322216
  have hstable : (prefixWord ++ tailWord_322216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322216).length < 2 ^ (prefixWord ++ tailWord_322216).sum := by decide
  have hdescent : baseEnd_322216 < baseStart_322216 := by decide
  rcases family_descends (prefixWord ++ tailWord_322216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322252 : List Nat := [2, 2, 1, 5, 1, 2, 3, 3]
def baseStart_322252 : Nat := 118140960795 + 322252 * 2 ^ 59
def prefixEnd_322252 : Nat := 4983230072969 + 3 ^ 40 * 322252 * 2
def baseEnd_322252 : Nat := 98056395776461286677331

theorem tailTrace_322252 : CollatzResearch.WordTrace tailWord_322252 prefixEnd_322252 98056395776461286677331 := by
  unfold tailWord_322252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876748014271757552524505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7835664019029010070032673 5876748014271757552524505)
  ·
    refine ⟨4407561010703818164393379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5876748014271757552524505 4407561010703818164393379)
    ·
      refine ⟨6611341516055727246590069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407561010703818164393379 6611341516055727246590069)
      ·
        refine ⟨619813267130224429367819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6611341516055727246590069 619813267130224429367819)
        ·
          refine ⟨929719900695336644051729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619813267130224429367819 929719900695336644051729)
          ·
            refine ⟨697289925521502483038797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929719900695336644051729 697289925521502483038797)
            ·
              refine ⟨261483722070563431139549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697289925521502483038797 261483722070563431139549)
              ·
                refine ⟨98056395776461286677331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261483722070563431139549 98056395776461286677331)
                ·
                  rfl

theorem cell19_322252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_322252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322252 prefixEnd_322252 := by exact prefixLift 322252
  have htrace : WordTrace (prefixWord ++ tailWord_322252) baseStart_322252 baseEnd_322252 := by
    simpa [prefixWord, tailWord_322252, baseEnd_322252] using wordTrace_append hprefix tailTrace_322252
  have hstable : (prefixWord ++ tailWord_322252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322252).length < 2 ^ (prefixWord ++ tailWord_322252).sum := by decide
  have hdescent : baseEnd_322252 < baseStart_322252 := by decide
  rcases family_descends (prefixWord ++ tailWord_322252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322311 : List Nat := [1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_322311 : Nat := 118140960795 + 322311 * 2 ^ 59
def prefixEnd_322311 : Nat := 4983230072969 + 3 ^ 40 * 322311 * 2
def baseEnd_322311 : Nat := 98074348581566631366059

theorem tailTrace_322311 : CollatzResearch.WordTrace tailWord_322311 prefixEnd_322311 98074348581566631366059 := by
  unfold tailWord_322311
  simp only [CollatzResearch.WordTrace]
  refine ⟨11755647935329768181446787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7837098623553178787631191 11755647935329768181446787)
  ·
    refine ⟨17633471902994652272170181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11755647935329768181446787 17633471902994652272170181)
    ·
      refine ⟨3306275981811497301031909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17633471902994652272170181 3306275981811497301031909)
      ·
        refine ⟨619926746589655743943483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3306275981811497301031909 619926746589655743943483)
        ·
          refine ⟨929890119884483615915225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619926746589655743943483 929890119884483615915225)
          ·
            refine ⟨697417589913362711936419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929890119884483615915225 697417589913362711936419)
            ·
              refine ⟨1046126384870044067904629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697417589913362711936419 1046126384870044067904629)
              ·
                refine ⟨98074348581566631366059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1046126384870044067904629 98074348581566631366059)
                ·
                  rfl

theorem cell19_322311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_322311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322311 prefixEnd_322311 := by exact prefixLift 322311
  have htrace : WordTrace (prefixWord ++ tailWord_322311) baseStart_322311 baseEnd_322311 := by
    simpa [prefixWord, tailWord_322311, baseEnd_322311] using wordTrace_append hprefix tailTrace_322311
  have hstable : (prefixWord ++ tailWord_322311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322311).length < 2 ^ (prefixWord ++ tailWord_322311).sum := by decide
  have hdescent : baseEnd_322311 < baseStart_322311 := by decide
  rcases family_descends (prefixWord ++ tailWord_322311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322332 : List Nat := [2, 2, 3, 1, 1, 3, 7]
def baseStart_322332 : Nat := 118140960795 + 322332 * 2 ^ 59
def prefixEnd_322332 : Nat := 4983230072969 + 3 ^ 40 * 322332 * 2
def baseEnd_322332 : Nat := 32693579521014934966445

theorem tailTrace_322332 : CollatzResearch.WordTrace tailWord_322332 prefixEnd_322332 32693579521014934966445 := by
  unfold tailWord_322332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878206934126844383980625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7837609245502459178640833 5878206934126844383980625)
  ·
    refine ⟨4408655200595133287985469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5878206934126844383980625 4408655200595133287985469)
    ·
      refine ⟨1653245700223174982994551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4408655200595133287985469 1653245700223174982994551)
      ·
        refine ⟨2479868550334762474491827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653245700223174982994551 2479868550334762474491827)
        ·
          refine ⟨3719802825502143711737741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479868550334762474491827 3719802825502143711737741)
          ·
            refine ⟨1394926059563303891901653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3719802825502143711737741 1394926059563303891901653)
            ·
              refine ⟨32693579521014934966445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1394926059563303891901653 32693579521014934966445)
              ·
                rfl

theorem cell19_322332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_322332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322332 prefixEnd_322332 := by exact prefixLift 322332
  have htrace : WordTrace (prefixWord ++ tailWord_322332) baseStart_322332 baseEnd_322332 := by
    simpa [prefixWord, tailWord_322332, baseEnd_322332] using wordTrace_append hprefix tailTrace_322332
  have hstable : (prefixWord ++ tailWord_322332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322332).length < 2 ^ (prefixWord ++ tailWord_322332).sum := by decide
  have hdescent : baseEnd_322332 < baseStart_322332 := by decide
  rcases family_descends (prefixWord ++ tailWord_322332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322402 : List Nat := [3, 3, 2, 1, 4, 1, 1, 4]
def baseStart_322402 : Nat := 118140960795 + 322402 * 2 ^ 59
def prefixEnd_322402 : Nat := 4983230072969 + 3 ^ 40 * 322402 * 2
def baseEnd_322402 : Nat := 98102038501305383343589

theorem tailTrace_322402 : CollatzResearch.WordTrace tailWord_322402 prefixEnd_322402 98102038501305383343589 := by
  unfold tailWord_322402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939741744500022680752365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7839311318666727148672973 2939741744500022680752365)
  ·
    refine ⟨1102403154187508505282137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2939741744500022680752365 1102403154187508505282137)
    ·
      refine ⟨826802365640631378961603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1102403154187508505282137 826802365640631378961603)
      ·
        refine ⟨1240203548460947068442405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826802365640631378961603 1240203548460947068442405)
        ·
          refine ⟨232538165336427575332951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1240203548460947068442405 232538165336427575332951)
          ·
            refine ⟨348807248004641362999427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232538165336427575332951 348807248004641362999427)
            ·
              refine ⟨523210872006962044499141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348807248004641362999427 523210872006962044499141)
              ·
                refine ⟨98102038501305383343589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523210872006962044499141 98102038501305383343589)
                ·
                  rfl

theorem cell19_322402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_322402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322402 prefixEnd_322402 := by exact prefixLift 322402
  have htrace : WordTrace (prefixWord ++ tailWord_322402) baseStart_322402 baseEnd_322402 := by
    simpa [prefixWord, tailWord_322402, baseEnd_322402] using wordTrace_append hprefix tailTrace_322402
  have hstable : (prefixWord ++ tailWord_322402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322402).length < 2 ^ (prefixWord ++ tailWord_322402).sum := by decide
  have hdescent : baseEnd_322402 < baseStart_322402 := by decide
  rcases family_descends (prefixWord ++ tailWord_322402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322425 : List Nat := [1, 2, 1, 3, 2, 4, 3, 3]
def baseStart_322425 : Nat := 118140960795 + 322425 * 2 ^ 59
def prefixEnd_322425 : Nat := 4983230072969 + 3 ^ 40 * 322425 * 2
def baseEnd_322425 : Nat := 98109037052448144832415

theorem tailTrace_322425 : CollatzResearch.WordTrace tailWord_322425 prefixEnd_322425 98109037052448144832415 := by
  unfold tailWord_322425
  simp only [CollatzResearch.WordTrace]
  refine ⟨11759805856916765651096729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7839870571277843767397819 11759805856916765651096729)
  ·
    refine ⟨8819854392687574238322547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11759805856916765651096729 8819854392687574238322547)
    ·
      refine ⟨13229781589031361357483821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8819854392687574238322547 13229781589031361357483821)
      ·
        refine ⟨4961168095886760509056433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13229781589031361357483821 4961168095886760509056433)
        ·
          refine ⟨3720876071915070381792325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4961168095886760509056433 3720876071915070381792325)
          ·
            refine ⟨697664263484075696586061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3720876071915070381792325 697664263484075696586061)
            ·
              refine ⟨261624098806528386219773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697664263484075696586061 261624098806528386219773)
              ·
                refine ⟨98109037052448144832415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261624098806528386219773 98109037052448144832415)
                ·
                  rfl

theorem cell19_322425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_322425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322425 prefixEnd_322425 := by exact prefixLift 322425
  have htrace : WordTrace (prefixWord ++ tailWord_322425) baseStart_322425 baseEnd_322425 := by
    simpa [prefixWord, tailWord_322425, baseEnd_322425] using wordTrace_append hprefix tailTrace_322425
  have hstable : (prefixWord ++ tailWord_322425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322425).length < 2 ^ (prefixWord ++ tailWord_322425).sum := by decide
  have hdescent : baseEnd_322425 < baseStart_322425 := by decide
  rcases family_descends (prefixWord ++ tailWord_322425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322518 : List Nat := [5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_322518 : Nat := 118140960795 + 322518 * 2 ^ 59
def prefixEnd_322518 : Nat := 4983230072969 + 3 ^ 40 * 322518 * 2
def baseEnd_322518 : Nat := 98137335541851484765495

theorem tailTrace_322518 : CollatzResearch.WordTrace tailWord_322518 prefixEnd_322518 98137335541851484765495 := by
  unfold tailWord_322518
  simp only [CollatzResearch.WordTrace]
  refine ⟨735199865348740158389513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7842131897053228356154805 735199865348740158389513)
  ·
    refine ⟨551399899011555118792135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 735199865348740158389513 551399899011555118792135)
    ·
      refine ⟨827099848517332678188203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551399899011555118792135 827099848517332678188203)
      ·
        refine ⟨1240649772775999017282305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827099848517332678188203 1240649772775999017282305)
        ·
          refine ⟨930487329581999262961729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240649772775999017282305 930487329581999262961729)
          ·
            refine ⟨697865497186499447221297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930487329581999262961729 697865497186499447221297)
            ·
              refine ⟨523399122889874585415973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697865497186499447221297 523399122889874585415973)
              ·
                refine ⟨98137335541851484765495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523399122889874585415973 98137335541851484765495)
                ·
                  rfl

theorem cell19_322518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_322518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322518 prefixEnd_322518 := by exact prefixLift 322518
  have htrace : WordTrace (prefixWord ++ tailWord_322518) baseStart_322518 baseEnd_322518 := by
    simpa [prefixWord, tailWord_322518, baseEnd_322518] using wordTrace_append hprefix tailTrace_322518
  have hstable : (prefixWord ++ tailWord_322518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322518).length < 2 ^ (prefixWord ++ tailWord_322518).sum := by decide
  have hdescent : baseEnd_322518 < baseStart_322518 := by decide
  rcases family_descends (prefixWord ++ tailWord_322518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322522 : List Nat := [3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_322522 : Nat := 118140960795 + 322522 * 2 ^ 59
def prefixEnd_322522 : Nat := 4983230072969 + 3 ^ 40 * 322522 * 2
def baseEnd_322522 : Nat := 98138552681180660676595

theorem tailTrace_322522 : CollatzResearch.WordTrace tailWord_322522 prefixEnd_322522 98138552681180660676595 := by
  unfold tailWord_322522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940835934391337804344455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7842229158376900811585213 2940835934391337804344455)
  ·
    refine ⟨4411253901587006706516683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940835934391337804344455 4411253901587006706516683)
    ·
      refine ⟨6616880852380510059775025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411253901587006706516683 6616880852380510059775025)
      ·
        refine ⟨4962660639285382544831269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6616880852380510059775025 4962660639285382544831269)
        ·
          refine ⟨930498869866009227155863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4962660639285382544831269 930498869866009227155863)
          ·
            refine ⟨1395748304799013840733795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930498869866009227155863 1395748304799013840733795)
            ·
              refine ⟨2093622457198520761100693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395748304799013840733795 2093622457198520761100693)
              ·
                refine ⟨98138552681180660676595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2093622457198520761100693 98138552681180660676595)
                ·
                  rfl

theorem cell19_322522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_322522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322522 prefixEnd_322522 := by exact prefixLift 322522
  have htrace : WordTrace (prefixWord ++ tailWord_322522) baseStart_322522 baseEnd_322522 := by
    simpa [prefixWord, tailWord_322522, baseEnd_322522] using wordTrace_append hprefix tailTrace_322522
  have hstable : (prefixWord ++ tailWord_322522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322522).length < 2 ^ (prefixWord ++ tailWord_322522).sum := by decide
  have hdescent : baseEnd_322522 < baseStart_322522 := by decide
  rcases family_descends (prefixWord ++ tailWord_322522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322558 : List Nat := [4, 2, 2, 2, 2, 7]
def baseStart_322558 : Nat := 118140960795 + 322558 * 2 ^ 59
def prefixEnd_322558 : Nat := 4983230072969 + 3 ^ 40 * 322558 * 2
def baseEnd_322558 : Nat := 10905500770571471541833

theorem tailTrace_322558 : CollatzResearch.WordTrace tailWord_322558 prefixEnd_322558 10905500770571471541833 := by
  unfold tailWord_322558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470582095679366170711041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7843104510289952910458885 1470582095679366170711041)
  ·
    refine ⟨1102936571759524628033281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1470582095679366170711041 1102936571759524628033281)
    ·
      refine ⟨827202428819643471024961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1102936571759524628033281 827202428819643471024961)
      ·
        refine ⟨620401821614732603268721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 827202428819643471024961 620401821614732603268721)
        ·
          refine ⟨465301366211049452451541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620401821614732603268721 465301366211049452451541)
          ·
            refine ⟨10905500770571471541833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 465301366211049452451541 10905500770571471541833)
            ·
              rfl

theorem cell19_322558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_322558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322558 prefixEnd_322558 := by exact prefixLift 322558
  have htrace : WordTrace (prefixWord ++ tailWord_322558) baseStart_322558 baseEnd_322558 := by
    simpa [prefixWord, tailWord_322558, baseEnd_322558] using wordTrace_append hprefix tailTrace_322558
  have hstable : (prefixWord ++ tailWord_322558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322558).length < 2 ^ (prefixWord ++ tailWord_322558).sum := by decide
  have hdescent : baseEnd_322558 < baseStart_322558 := by decide
  rcases family_descends (prefixWord ++ tailWord_322558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322617 : List Nat := [1, 2, 1, 5, 2, 2, 6]
def baseStart_322617 : Nat := 118140960795 + 322617 * 2 ^ 59
def prefixEnd_322617 : Nat := 4983230072969 + 3 ^ 40 * 322617 * 2
def baseEnd_322617 : Nat := 32722486580082862855075

theorem tailTrace_322617 : CollatzResearch.WordTrace tailWord_322617 prefixEnd_322617 32722486580082862855075 := by
  unfold tailWord_322617
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766808672221182442086105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7844539114814121628057403 11766808672221182442086105)
  ·
    refine ⟨8825106504165886831564579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11766808672221182442086105 8825106504165886831564579)
    ·
      refine ⟨13237659756248830247346869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8825106504165886831564579 13237659756248830247346869)
      ·
        refine ⟨1241030602148327835688769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13237659756248830247346869 1241030602148327835688769)
        ·
          refine ⟨930772951611245876766577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241030602148327835688769 930772951611245876766577)
          ·
            refine ⟨698079713708434407574933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930772951611245876766577 698079713708434407574933)
            ·
              refine ⟨32722486580082862855075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 698079713708434407574933 32722486580082862855075)
              ·
                rfl

theorem cell19_322617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_322617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322617 prefixEnd_322617 := by exact prefixLift 322617
  have htrace : WordTrace (prefixWord ++ tailWord_322617) baseStart_322617 baseEnd_322617 := by
    simpa [prefixWord, tailWord_322617, baseEnd_322617] using wordTrace_append hprefix tailTrace_322617
  have hstable : (prefixWord ++ tailWord_322617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322617).length < 2 ^ (prefixWord ++ tailWord_322617).sum := by decide
  have hdescent : baseEnd_322617 < baseStart_322617 := by decide
  rcases family_descends (prefixWord ++ tailWord_322617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322712 : List Nat := [2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_322712 : Nat := 118140960795 + 322712 * 2 ^ 59
def prefixEnd_322712 : Nat := 4983230072969 + 3 ^ 40 * 322712 * 2
def baseEnd_322712 : Nat := 98196366799316516453855

theorem tailTrace_322712 : CollatzResearch.WordTrace tailWord_322712 prefixEnd_322712 98196366799316516453855 := by
  unfold tailWord_322712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885136803438506833397195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7846849071251342444529593 5885136803438506833397195)
  ·
    refine ⟨8827705205157760250095793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5885136803438506833397195 8827705205157760250095793)
    ·
      refine ⟨6620778903868320187571845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8827705205157760250095793 6620778903868320187571845)
      ·
        refine ⟨1241396044475310035169721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6620778903868320187571845 1241396044475310035169721)
        ·
          refine ⟨931047033356482526377291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241396044475310035169721 931047033356482526377291)
          ·
            refine ⟨1396570550034723789565937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931047033356482526377291 1396570550034723789565937)
            ·
              refine ⟨1047427912526042842174453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396570550034723789565937 1047427912526042842174453)
              ·
                refine ⟨98196366799316516453855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1047427912526042842174453 98196366799316516453855)
                ·
                  rfl

theorem cell19_322712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_322712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322712 prefixEnd_322712 := by exact prefixLift 322712
  have htrace : WordTrace (prefixWord ++ tailWord_322712) baseStart_322712 baseEnd_322712 := by
    simpa [prefixWord, tailWord_322712, baseEnd_322712] using wordTrace_append hprefix tailTrace_322712
  have hstable : (prefixWord ++ tailWord_322712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322712).length < 2 ^ (prefixWord ++ tailWord_322712).sum := by decide
  have hdescent : baseEnd_322712 < baseStart_322712 := by decide
  rcases family_descends (prefixWord ++ tailWord_322712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322742 : List Nat := [5, 1, 3, 2, 2, 1, 1, 4]
def baseStart_322742 : Nat := 118140960795 + 322742 * 2 ^ 59
def prefixEnd_322742 : Nat := 4983230072969 + 3 ^ 40 * 322742 * 2
def baseEnd_322742 : Nat := 98205495344285335787107

theorem tailTrace_322742 : CollatzResearch.WordTrace tailWord_322742 prefixEnd_322742 98205495344285335787107 := by
  unfold tailWord_322742
  simp only [CollatzResearch.WordTrace]
  refine ⟨735710487298020549399155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7847578531178885860257653 735710487298020549399155)
  ·
    refine ⟨1103565730947030824098733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 735710487298020549399155 1103565730947030824098733)
    ·
      refine ⟨413837149105136559037025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1103565730947030824098733 413837149105136559037025)
      ·
        refine ⟨310377861828852419277769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413837149105136559037025 310377861828852419277769)
        ·
          refine ⟨232783396371639314458327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310377861828852419277769 232783396371639314458327)
          ·
            refine ⟨349175094557458971687491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232783396371639314458327 349175094557458971687491)
            ·
              refine ⟨523762641836188457531237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349175094557458971687491 523762641836188457531237)
              ·
                refine ⟨98205495344285335787107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523762641836188457531237 98205495344285335787107)
                ·
                  rfl

theorem cell19_322742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_322742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322742 prefixEnd_322742 := by exact prefixLift 322742
  have htrace : WordTrace (prefixWord ++ tailWord_322742) baseStart_322742 baseEnd_322742 := by
    simpa [prefixWord, tailWord_322742, baseEnd_322742] using wordTrace_append hprefix tailTrace_322742
  have hstable : (prefixWord ++ tailWord_322742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322742).length < 2 ^ (prefixWord ++ tailWord_322742).sum := by decide
  have hdescent : baseEnd_322742 < baseStart_322742 := by decide
  rcases family_descends (prefixWord ++ tailWord_322742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322748 : List Nat := [2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_322748 : Nat := 118140960795 + 322748 * 2 ^ 59
def prefixEnd_322748 : Nat := 4983230072969 + 3 ^ 40 * 322748 * 2
def baseEnd_322748 : Nat := 98207321053279099653757

theorem tailTrace_322748 : CollatzResearch.WordTrace tailWord_322748 prefixEnd_322748 98207321053279099653757 := by
  unfold tailWord_322748
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885793317373295907552449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7847724423164394543403265 5885793317373295907552449)
  ·
    refine ⟨4414344988029971930664337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5885793317373295907552449 4414344988029971930664337)
    ·
      refine ⟨3310758741022478947998253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4414344988029971930664337 3310758741022478947998253)
      ·
        refine ⟨1241534527883429605499345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3310758741022478947998253 1241534527883429605499345)
        ·
          refine ⟨931150895912572204124509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241534527883429605499345 931150895912572204124509)
          ·
            refine ⟨349181585967214576546691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 931150895912572204124509 349181585967214576546691)
            ·
              refine ⟨523772378950821864820037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349181585967214576546691 523772378950821864820037)
              ·
                refine ⟨98207321053279099653757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523772378950821864820037 98207321053279099653757)
                ·
                  rfl

theorem cell19_322748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_322748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322748 prefixEnd_322748 := by exact prefixLift 322748
  have htrace : WordTrace (prefixWord ++ tailWord_322748) baseStart_322748 baseEnd_322748 := by
    simpa [prefixWord, tailWord_322748, baseEnd_322748] using wordTrace_append hprefix tailTrace_322748
  have hstable : (prefixWord ++ tailWord_322748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322748).length < 2 ^ (prefixWord ++ tailWord_322748).sum := by decide
  have hdescent : baseEnd_322748 < baseStart_322748 := by decide
  rcases family_descends (prefixWord ++ tailWord_322748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322809 : List Nat := [1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_322809 : Nat := 118140960795 + 322809 * 2 ^ 59
def prefixEnd_322809 : Nat := 4983230072969 + 3 ^ 40 * 322809 * 2
def baseEnd_322809 : Nat := 98225882428049032298035

theorem tailTrace_322809 : CollatzResearch.WordTrace tailWord_322809 prefixEnd_322809 98225882428049032298035 := by
  unfold tailWord_322809
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773811487525599233075481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7849207658350399488716987 11773811487525599233075481)
  ·
    refine ⟨8830358615644199424806611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11773811487525599233075481 8830358615644199424806611)
    ·
      refine ⟨13245537923466299137209917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8830358615644199424806611 13245537923466299137209917)
      ·
        refine ⟨4967076721299862176453719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13245537923466299137209917 4967076721299862176453719)
        ·
          refine ⟨7450615081949793264680579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967076721299862176453719 7450615081949793264680579)
          ·
            refine ⟨11175922622924689897020869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450615081949793264680579 11175922622924689897020869)
            ·
              refine ⟨2095485491798379355691413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11175922622924689897020869 2095485491798379355691413)
              ·
                refine ⟨98225882428049032298035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2095485491798379355691413 98225882428049032298035)
                ·
                  rfl

theorem cell19_322809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_322809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322809 prefixEnd_322809 := by exact prefixLift 322809
  have htrace : WordTrace (prefixWord ++ tailWord_322809) baseStart_322809 baseEnd_322809 := by
    simpa [prefixWord, tailWord_322809, baseEnd_322809] using wordTrace_append hprefix tailTrace_322809
  have hstable : (prefixWord ++ tailWord_322809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322809).length < 2 ^ (prefixWord ++ tailWord_322809).sum := by decide
  have hdescent : baseEnd_322809 < baseStart_322809 := by decide
  rcases family_descends (prefixWord ++ tailWord_322809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322845 : List Nat := [1, 4, 2, 3, 1, 1, 7]
def baseStart_322845 : Nat := 118140960795 + 322845 * 2 ^ 59
def prefixEnd_322845 : Nat := 4983230072969 + 3 ^ 40 * 322845 * 2
def baseEnd_322845 : Nat := 32745612227337205165979

theorem tailTrace_322845 : CollatzResearch.WordTrace tailWord_322845 prefixEnd_322845 32745612227337205165979 := by
  unfold tailWord_322845
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775124515395177381385989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7850083010263451587590659 11775124515395177381385989)
  ·
    refine ⟨2207835846636595759009873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11775124515395177381385989 2207835846636595759009873)
    ·
      refine ⟨1655876884977446819257405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2207835846636595759009873 1655876884977446819257405)
      ·
        refine ⟨620953831866542557221527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1655876884977446819257405 620953831866542557221527)
        ·
          refine ⟨931430747799813835832291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620953831866542557221527 931430747799813835832291)
          ·
            refine ⟨1397146121699720753748437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931430747799813835832291 1397146121699720753748437)
            ·
              refine ⟨32745612227337205165979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1397146121699720753748437 32745612227337205165979)
              ·
                rfl

theorem cell19_322845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_322845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322845 prefixEnd_322845 := by exact prefixLift 322845
  have htrace : WordTrace (prefixWord ++ tailWord_322845) baseStart_322845 baseEnd_322845 := by
    simpa [prefixWord, tailWord_322845, baseEnd_322845] using wordTrace_append hprefix tailTrace_322845
  have hstable : (prefixWord ++ tailWord_322845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322845).length < 2 ^ (prefixWord ++ tailWord_322845).sum := by decide
  have hdescent : baseEnd_322845 < baseStart_322845 := by decide
  rcases family_descends (prefixWord ++ tailWord_322845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322919 : List Nat := [1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_322919 : Nat := 118140960795 + 322919 * 2 ^ 59
def prefixEnd_322919 : Nat := 4983230072969 + 3 ^ 40 * 322919 * 2
def baseEnd_322919 : Nat := 98259353759601369853291

theorem tailTrace_322919 : CollatzResearch.WordTrace tailWord_322919 prefixEnd_322919 98259353759601369853291 := by
  unfold tailWord_322919
  simp only [CollatzResearch.WordTrace]
  refine ⟨11777823517127088019579811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7851882344751392013053207 11777823517127088019579811)
  ·
    refine ⟨17666735275690632029369717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11777823517127088019579811 17666735275690632029369717)
    ·
      refine ⟨1656256432095996752753411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17666735275690632029369717 1656256432095996752753411)
      ·
        refine ⟨2484384648143995129130117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1656256432095996752753411 2484384648143995129130117)
        ·
          refine ⟨465822121526999086711897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2484384648143995129130117 465822121526999086711897)
          ·
            refine ⟨349366591145249315033923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465822121526999086711897 349366591145249315033923)
            ·
              refine ⟨524049886717873972550885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349366591145249315033923 524049886717873972550885)
              ·
                refine ⟨98259353759601369853291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524049886717873972550885 98259353759601369853291)
                ·
                  rfl

theorem cell19_322919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_322919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322919 prefixEnd_322919 := by exact prefixLift 322919
  have htrace : WordTrace (prefixWord ++ tailWord_322919) baseStart_322919 baseEnd_322919 := by
    simpa [prefixWord, tailWord_322919, baseEnd_322919] using wordTrace_append hprefix tailTrace_322919
  have hstable : (prefixWord ++ tailWord_322919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322919).length < 2 ^ (prefixWord ++ tailWord_322919).sum := by decide
  have hdescent : baseEnd_322919 < baseStart_322919 := by decide
  rcases family_descends (prefixWord ++ tailWord_322919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322940 : List Nat := [2, 2, 2, 1, 1, 1, 7, 3]
def baseStart_322940 : Nat := 118140960795 + 322940 * 2 ^ 59
def prefixEnd_322940 : Nat := 4983230072969 + 3 ^ 40 * 322940 * 2
def baseEnd_322940 : Nat := 98265743741079543386567

theorem tailTrace_322940 : CollatzResearch.WordTrace tailWord_322940 prefixEnd_322940 98265743741079543386567 := by
  unfold tailWord_322940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5889294725025504303047137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7852392966700672404062849 5889294725025504303047137)
  ·
    refine ⟨4416971043769128227285353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5889294725025504303047137 4416971043769128227285353)
    ·
      refine ⟨3312728282826846170464015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4416971043769128227285353 3312728282826846170464015)
      ·
        refine ⟨4969092424240269255696023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312728282826846170464015 4969092424240269255696023)
        ·
          refine ⟨7453638636360403883544035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969092424240269255696023 7453638636360403883544035)
          ·
            refine ⟨11180457954540605825316053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453638636360403883544035 11180457954540605825316053)
            ·
              refine ⟨262041983309545449030845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11180457954540605825316053 262041983309545449030845)
              ·
                refine ⟨98265743741079543386567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262041983309545449030845 98265743741079543386567)
                ·
                  rfl

theorem cell19_322940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_322940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322940 prefixEnd_322940 := by exact prefixLift 322940
  have htrace : WordTrace (prefixWord ++ tailWord_322940) baseStart_322940 baseEnd_322940 := by
    simpa [prefixWord, tailWord_322940, baseEnd_322940] using wordTrace_append hprefix tailTrace_322940
  have hstable : (prefixWord ++ tailWord_322940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322940).length < 2 ^ (prefixWord ++ tailWord_322940).sum := by decide
  have hdescent : baseEnd_322940 < baseStart_322940 := by decide
  rcases family_descends (prefixWord ++ tailWord_322940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322980 : List Nat := [2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_322980 : Nat := 118140960795 + 322980 * 2 ^ 59
def prefixEnd_322980 : Nat := 4983230072969 + 3 ^ 40 * 322980 * 2
def baseEnd_322980 : Nat := 98277915134371302497569

theorem tailTrace_322980 : CollatzResearch.WordTrace tailWord_322980 prefixEnd_322980 98277915134371302497569 := by
  unfold tailWord_322980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890024184953047718775197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7853365579937396958366929 5890024184953047718775197)
  ·
    refine ⟨2208759069357392894540699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5890024184953047718775197 2208759069357392894540699)
    ·
      refine ⟨3313138604036089341811049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208759069357392894540699 3313138604036089341811049)
      ·
        refine ⟨2484853953027067006358287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3313138604036089341811049 2484853953027067006358287)
        ·
          refine ⟨3727280929540600509537431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484853953027067006358287 3727280929540600509537431)
          ·
            refine ⟨5590921394310900764306147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727280929540600509537431 5590921394310900764306147)
            ·
              refine ⟨8386382091466351146459221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590921394310900764306147 8386382091466351146459221)
              ·
                refine ⟨98277915134371302497569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8386382091466351146459221 98277915134371302497569)
                ·
                  rfl

theorem cell19_322980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_322980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322980 prefixEnd_322980 := by exact prefixLift 322980
  have htrace : WordTrace (prefixWord ++ tailWord_322980) baseStart_322980 baseEnd_322980 := by
    simpa [prefixWord, tailWord_322980, baseEnd_322980] using wordTrace_append hprefix tailTrace_322980
  have hstable : (prefixWord ++ tailWord_322980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322980).length < 2 ^ (prefixWord ++ tailWord_322980).sum := by decide
  have hdescent : baseEnd_322980 < baseStart_322980 := by decide
  rcases family_descends (prefixWord ++ tailWord_322980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322997 : List Nat := [1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_322997 : Nat := 118140960795 + 322997 * 2 ^ 59
def prefixEnd_322997 : Nat := 4983230072969 + 3 ^ 40 * 322997 * 2
def baseEnd_322997 : Nat := 98283087976520300119745

theorem tailTrace_322997 : CollatzResearch.WordTrace tailWord_322997 prefixEnd_322997 98283087976520300119745 := by
  unfold tailWord_322997
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780668410844507340919245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7853778940563004893946163 11780668410844507340919245)
  ·
    refine ⟨4417750654066690252844717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11780668410844507340919245 4417750654066690252844717)
    ·
      refine ⟨1656656495275008844816769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4417750654066690252844717 1656656495275008844816769)
      ·
        refine ⟨1242492371456256633612577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1656656495275008844816769 1242492371456256633612577)
        ·
          refine ⟨931869278592192475209433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1242492371456256633612577 931869278592192475209433)
          ·
            refine ⟨698901958944144356407075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931869278592192475209433 698901958944144356407075)
            ·
              refine ⟨1048352938416216534610613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698901958944144356407075 1048352938416216534610613)
              ·
                refine ⟨98283087976520300119745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1048352938416216534610613 98283087976520300119745)
                ·
                  rfl

theorem cell19_322997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_322997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322997 prefixEnd_322997 := by exact prefixLift 322997
  have htrace : WordTrace (prefixWord ++ tailWord_322997) baseStart_322997 baseEnd_322997 := by
    simpa [prefixWord, tailWord_322997, baseEnd_322997] using wordTrace_append hprefix tailTrace_322997
  have hstable : (prefixWord ++ tailWord_322997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322997).length < 2 ^ (prefixWord ++ tailWord_322997).sum := by decide
  have hdescent : baseEnd_322997 < baseStart_322997 := by decide
  rcases family_descends (prefixWord ++ tailWord_322997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322999 : List Nat := [1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_322999 : Nat := 118140960795 + 322999 * 2 ^ 59
def prefixEnd_322999 : Nat := 4983230072969 + 3 ^ 40 * 322999 * 2
def baseEnd_322999 : Nat := 98283696546184888075295

theorem tailTrace_322999 : CollatzResearch.WordTrace tailWord_322999 prefixEnd_322999 98283696546184888075295 := by
  unfold tailWord_322999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780741356837261682492051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7853827571224841121661367 11780741356837261682492051)
  ·
    refine ⟨17671112035255892523738077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11780741356837261682492051 17671112035255892523738077)
    ·
      refine ⟨6626667013220959696401779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17671112035255892523738077 6626667013220959696401779)
      ·
        refine ⟨9940000519831439544602669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6626667013220959696401779 9940000519831439544602669)
        ·
          refine ⟨3727500194936789829226001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9940000519831439544602669 3727500194936789829226001)
          ·
            refine ⟨2795625146202592371919501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3727500194936789829226001 2795625146202592371919501)
            ·
              refine ⟨1048359429825972139469813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2795625146202592371919501 1048359429825972139469813)
              ·
                refine ⟨98283696546184888075295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1048359429825972139469813 98283696546184888075295)
                ·
                  rfl

theorem cell19_322999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_322999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_322999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_322999 prefixEnd_322999 := by exact prefixLift 322999
  have htrace : WordTrace (prefixWord ++ tailWord_322999) baseStart_322999 baseEnd_322999 := by
    simpa [prefixWord, tailWord_322999, baseEnd_322999] using wordTrace_append hprefix tailTrace_322999
  have hstable : (prefixWord ++ tailWord_322999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322999).length < 2 ^ (prefixWord ++ tailWord_322999).sum := by decide
  have hdescent : baseEnd_322999 < baseStart_322999 := by decide
  rcases family_descends (prefixWord ++ tailWord_322999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323018 : List Nat := [3, 1, 2, 1, 2, 3, 7]
def baseStart_323018 : Nat := 118140960795 + 323018 * 2 ^ 59
def prefixEnd_323018 : Nat := 4983230072969 + 3 ^ 40 * 323018 * 2
def baseEnd_323018 : Nat := 32763159319332824551007

theorem tailTrace_323018 : CollatzResearch.WordTrace tailWord_323018 prefixEnd_323018 32763159319332824551007 := by
  unfold tailWord_323018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945358585942106981858427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7854289562512285284955805 2945358585942106981858427)
  ·
    refine ⟨4418037878913160472787641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2945358585942106981858427 4418037878913160472787641)
    ·
      refine ⟨3313528409184870354590731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4418037878913160472787641 3313528409184870354590731)
      ·
        refine ⟨4970292613777305531886097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313528409184870354590731 4970292613777305531886097)
        ·
          refine ⟨3727719460332979148914573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4970292613777305531886097 3727719460332979148914573)
          ·
            refine ⟨1397894797624867180842965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3727719460332979148914573 1397894797624867180842965)
            ·
              refine ⟨32763159319332824551007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1397894797624867180842965 32763159319332824551007)
              ·
                rfl

theorem cell19_323018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_323018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323018 prefixEnd_323018 := by exact prefixLift 323018
  have htrace : WordTrace (prefixWord ++ tailWord_323018) baseStart_323018 baseEnd_323018 := by
    simpa [prefixWord, tailWord_323018, baseEnd_323018] using wordTrace_append hprefix tailTrace_323018
  have hstable : (prefixWord ++ tailWord_323018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323018).length < 2 ^ (prefixWord ++ tailWord_323018).sum := by decide
  have hdescent : baseEnd_323018 < baseStart_323018 := by decide
  rcases family_descends (prefixWord ++ tailWord_323018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323056 : List Nat := [2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_323056 : Nat := 118140960795 + 323056 * 2 ^ 59
def prefixEnd_323056 : Nat := 4983230072969 + 3 ^ 40 * 323056 * 2
def baseEnd_323056 : Nat := 98301040781625644808473

theorem tailTrace_323056 : CollatzResearch.WordTrace tailWord_323056 prefixEnd_323056 98301040781625644808473 := by
  unfold tailWord_323056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891410158815380208658511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7855213545087173611544681 5891410158815380208658511)
  ·
    refine ⟨8837115238223070312987767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5891410158815380208658511 8837115238223070312987767)
    ·
      refine ⟨13255672857334605469481651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8837115238223070312987767 13255672857334605469481651)
      ·
        refine ⟨19883509286001908204222477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13255672857334605469481651 19883509286001908204222477)
        ·
          refine ⟨7456315982250715576583429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19883509286001908204222477 7456315982250715576583429)
          ·
            refine ⟨1398059246672009170609393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7456315982250715576583429 1398059246672009170609393)
            ·
              refine ⟨1048544435004006877957045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1398059246672009170609393 1048544435004006877957045)
              ·
                refine ⟨98301040781625644808473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1048544435004006877957045 98301040781625644808473)
                ·
                  rfl

theorem cell19_323056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_323056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323056 prefixEnd_323056 := by exact prefixLift 323056
  have htrace : WordTrace (prefixWord ++ tailWord_323056) baseStart_323056 baseEnd_323056 := by
    simpa [prefixWord, tailWord_323056, baseEnd_323056] using wordTrace_append hprefix tailTrace_323056
  have hstable : (prefixWord ++ tailWord_323056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323056).length < 2 ^ (prefixWord ++ tailWord_323056).sum := by decide
  have hdescent : baseEnd_323056 < baseStart_323056 := by decide
  rcases family_descends (prefixWord ++ tailWord_323056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323073 : List Nat := [1, 2, 4, 1, 5, 6]
def baseStart_323073 : Nat := 118140960795 + 323073 * 2 ^ 59
def prefixEnd_323073 : Nat := 4983230072969 + 3 ^ 40 * 323073 * 2
def baseEnd_323073 : Nat := 10922912624863849158961

theorem tailTrace_323073 : CollatzResearch.WordTrace tailWord_323073 prefixEnd_323073 10922912624863849158961 := by
  unfold tailWord_323073
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783440358569172320685873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7855626905712781547123915 11783440358569172320685873)
  ·
    refine ⟨8837580268926879240514405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11783440358569172320685873 8837580268926879240514405)
    ·
      refine ⟨1657046300423789857596451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8837580268926879240514405 1657046300423789857596451)
      ·
        refine ⟨2485569450635684786394677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657046300423789857596451 2485569450635684786394677)
        ·
          refine ⟨233022135997095448724501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2485569450635684786394677 233022135997095448724501)
          ·
            refine ⟨10922912624863849158961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 233022135997095448724501 10922912624863849158961)
            ·
              rfl

theorem cell19_323073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 6].length) (baseStart_323073 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323073 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323073 prefixEnd_323073 := by exact prefixLift 323073
  have htrace : WordTrace (prefixWord ++ tailWord_323073) baseStart_323073 baseEnd_323073 := by
    simpa [prefixWord, tailWord_323073, baseEnd_323073] using wordTrace_append hprefix tailTrace_323073
  have hstable : (prefixWord ++ tailWord_323073).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323073).length < 2 ^ (prefixWord ++ tailWord_323073).sum := by decide
  have hdescent : baseEnd_323073 < baseStart_323073 := by decide
  rcases family_descends (prefixWord ++ tailWord_323073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323240 : List Nat := [2, 1, 7, 1, 2, 6]
def baseStart_323240 : Nat := 118140960795 + 323240 * 2 ^ 59
def prefixEnd_323240 : Nat := 4983230072969 + 3 ^ 40 * 323240 * 2
def baseEnd_323240 : Nat := 10928558798974192968787

theorem tailTrace_323240 : CollatzResearch.WordTrace tailWord_323240 prefixEnd_323240 10928558798974192968787 := by
  unfold tailWord_323240
  simp only [CollatzResearch.WordTrace]
  refine ⟨5894765674482079921007587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7859687565976106561343449 5894765674482079921007587)
  ·
    refine ⟨8842148511723119881511381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5894765674482079921007587 8842148511723119881511381)
    ·
      refine ⟨207237855743510622222923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8842148511723119881511381 207237855743510622222923)
      ·
        refine ⟨310856783615265933334385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207237855743510622222923 310856783615265933334385)
        ·
          refine ⟨233142587711449450000789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310856783615265933334385 233142587711449450000789)
          ·
            refine ⟨10928558798974192968787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 233142587711449450000789 10928558798974192968787)
            ·
              rfl

theorem cell19_323240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 6].length) (baseStart_323240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323240 prefixEnd_323240 := by exact prefixLift 323240
  have htrace : WordTrace (prefixWord ++ tailWord_323240) baseStart_323240 baseEnd_323240 := by
    simpa [prefixWord, tailWord_323240, baseEnd_323240] using wordTrace_append hprefix tailTrace_323240
  have hstable : (prefixWord ++ tailWord_323240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323240).length < 2 ^ (prefixWord ++ tailWord_323240).sum := by decide
  have hdescent : baseEnd_323240 < baseStart_323240 := by decide
  rcases family_descends (prefixWord ++ tailWord_323240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323335 : List Nat := [1, 1, 4, 4, 3, 1, 2, 3]
def baseStart_323335 : Nat := 118140960795 + 323335 * 2 ^ 59
def prefixEnd_323335 : Nat := 4983230072969 + 3 ^ 40 * 323335 * 2
def baseEnd_323335 : Nat := 98385936249835664607713

theorem tailTrace_323335 : CollatzResearch.WordTrace tailWord_323335 prefixEnd_323335 98385936249835664607713 := by
  unfold tailWord_323335
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792996283619991066723459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7861997522413327377815639 11792996283619991066723459)
  ·
    refine ⟨17689494425429986600085189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11792996283619991066723459 17689494425429986600085189)
    ·
      refine ⟨3316780204768122487515973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17689494425429986600085189 3316780204768122487515973)
      ·
        refine ⟨621896288394022966409245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3316780204768122487515973 621896288394022966409245)
        ·
          refine ⟨233211108147758612403467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 621896288394022966409245 233211108147758612403467)
          ·
            refine ⟨349816662221637918605201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233211108147758612403467 349816662221637918605201)
            ·
              refine ⟨262362496666228438953901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349816662221637918605201 262362496666228438953901)
              ·
                refine ⟨98385936249835664607713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262362496666228438953901 98385936249835664607713)
                ·
                  rfl

theorem cell19_323335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_323335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323335 prefixEnd_323335 := by exact prefixLift 323335
  have htrace : WordTrace (prefixWord ++ tailWord_323335) baseStart_323335 baseEnd_323335 := by
    simpa [prefixWord, tailWord_323335, baseEnd_323335] using wordTrace_append hprefix tailTrace_323335
  have hstable : (prefixWord ++ tailWord_323335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323335).length < 2 ^ (prefixWord ++ tailWord_323335).sum := by decide
  have hdescent : baseEnd_323335 < baseStart_323335 := by decide
  rcases family_descends (prefixWord ++ tailWord_323335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323436 : List Nat := [2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_323436 : Nat := 118140960795 + 323436 * 2 ^ 59
def prefixEnd_323436 : Nat := 4983230072969 + 3 ^ 40 * 323436 * 2
def baseEnd_323436 : Nat := 98416669017897356362993

theorem tailTrace_323436 : CollatzResearch.WordTrace tailWord_323436 prefixEnd_323436 98416669017897356362993 := by
  unfold tailWord_323436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898340028127042658075081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7864453370836056877433441 5898340028127042658075081)
  ·
    refine ⟨4423755021095281993556311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5898340028127042658075081 4423755021095281993556311)
    ·
      refine ⟨6635632531642922990334467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4423755021095281993556311 6635632531642922990334467)
      ·
        refine ⟨9953448797464384485501701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635632531642922990334467 9953448797464384485501701)
        ·
          refine ⟨1866271649524572091031569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9953448797464384485501701 1866271649524572091031569)
          ·
            refine ⟨1399703737143429068273677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1866271649524572091031569 1399703737143429068273677)
            ·
              refine ⟨524888901428785900602629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1399703737143429068273677 524888901428785900602629)
              ·
                refine ⟨98416669017897356362993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524888901428785900602629 98416669017897356362993)
                ·
                  rfl

theorem cell19_323436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_323436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323436 prefixEnd_323436 := by exact prefixLift 323436
  have htrace : WordTrace (prefixWord ++ tailWord_323436) baseStart_323436 baseEnd_323436 := by
    simpa [prefixWord, tailWord_323436, baseEnd_323436] using wordTrace_append hprefix tailTrace_323436
  have hstable : (prefixWord ++ tailWord_323436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323436).length < 2 ^ (prefixWord ++ tailWord_323436).sum := by decide
  have hdescent : baseEnd_323436 < baseStart_323436 := by decide
  rcases family_descends (prefixWord ++ tailWord_323436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323502 : List Nat := [4, 1, 5, 1, 2, 1, 2, 3]
def baseStart_323502 : Nat := 118140960795 + 323502 * 2 ^ 59
def prefixEnd_323502 : Nat := 4983230072969 + 3 ^ 40 * 323502 * 2
def baseEnd_323502 : Nat := 98436751816828758896147

theorem tailTrace_323502 : CollatzResearch.WordTrace tailWord_323502 prefixEnd_323502 98436751816828758896147 := by
  unfold tailWord_323502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474885909251872323506595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7866058182676652392035173 1474885909251872323506595)
  ·
    refine ⟨2212328863877808485259893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1474885909251872323506595 2212328863877808485259893)
    ·
      refine ⟨207405830988544545493115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2212328863877808485259893 207405830988544545493115)
      ·
        refine ⟨311108746482816818239673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207405830988544545493115 311108746482816818239673)
        ·
          refine ⟨233331559862112613679755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311108746482816818239673 233331559862112613679755)
          ·
            refine ⟨349997339793168920519633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233331559862112613679755 349997339793168920519633)
            ·
              refine ⟨262498004844876690389725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349997339793168920519633 262498004844876690389725)
              ·
                refine ⟨98436751816828758896147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262498004844876690389725 98436751816828758896147)
                ·
                  rfl

theorem cell19_323502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_323502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323502 prefixEnd_323502 := by exact prefixLift 323502
  have htrace : WordTrace (prefixWord ++ tailWord_323502) baseStart_323502 baseEnd_323502 := by
    simpa [prefixWord, tailWord_323502, baseEnd_323502] using wordTrace_append hprefix tailTrace_323502
  have hstable : (prefixWord ++ tailWord_323502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323502).length < 2 ^ (prefixWord ++ tailWord_323502).sum := by decide
  have hdescent : baseEnd_323502 < baseStart_323502 := by decide
  rcases family_descends (prefixWord ++ tailWord_323502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323508 : List Nat := [2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_323508 : Nat := 118140960795 + 323508 * 2 ^ 59
def prefixEnd_323508 : Nat := 4983230072969 + 3 ^ 40 * 323508 * 2
def baseEnd_323508 : Nat := 98438577525822522762797

theorem tailTrace_323508 : CollatzResearch.WordTrace tailWord_323508 prefixEnd_323508 98438577525822522762797 := by
  unfold tailWord_323508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899653055996620806385589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7866204074662161075180785 5899653055996620806385589)
  ·
    refine ⟨553092473999683200598649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5899653055996620806385589 553092473999683200598649)
    ·
      refine ⟨414819355499762400448987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 553092473999683200598649 414819355499762400448987)
      ·
        refine ⟨622229033249643600673481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414819355499762400448987 622229033249643600673481)
        ·
          refine ⟨466671774937232700505111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622229033249643600673481 466671774937232700505111)
          ·
            refine ⟨700007662405849050757667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466671774937232700505111 700007662405849050757667)
            ·
              refine ⟨1050011493608773576136501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700007662405849050757667 1050011493608773576136501)
              ·
                refine ⟨98438577525822522762797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1050011493608773576136501 98438577525822522762797)
                ·
                  rfl

theorem cell19_323508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_323508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323508 prefixEnd_323508 := by exact prefixLift 323508
  have htrace : WordTrace (prefixWord ++ tailWord_323508) baseStart_323508 baseEnd_323508 := by
    simpa [prefixWord, tailWord_323508, baseEnd_323508] using wordTrace_append hprefix tailTrace_323508
  have hstable : (prefixWord ++ tailWord_323508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323508).length < 2 ^ (prefixWord ++ tailWord_323508).sum := by decide
  have hdescent : baseEnd_323508 < baseStart_323508 := by decide
  rcases family_descends (prefixWord ++ tailWord_323508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323588 : List Nat := [2, 3, 2, 4, 8]
def baseStart_323588 : Nat := 118140960795 + 323588 * 2 ^ 59
def prefixEnd_323588 : Nat := 4983230072969 + 3 ^ 40 * 323588 * 2
def baseEnd_323588 : Nat := 3646774826385408925363

theorem tailTrace_323588 : CollatzResearch.WordTrace tailWord_323588 prefixEnd_323588 3646774826385408925363 := by
  unfold tailWord_323588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901111975851707637841709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7868149301135610183788945 5901111975851707637841709)
  ·
    refine ⟨2212916990944390364190641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5901111975851707637841709 2212916990944390364190641)
    ·
      refine ⟨1659687743208292773142981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2212916990944390364190641 1659687743208292773142981)
      ·
        refine ⟨311191451851554894964309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1659687743208292773142981 311191451851554894964309)
        ·
          refine ⟨3646774826385408925363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 311191451851554894964309 3646774826385408925363)
          ·
            rfl

theorem cell19_323588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 8].length) (baseStart_323588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323588 prefixEnd_323588 := by exact prefixLift 323588
  have htrace : WordTrace (prefixWord ++ tailWord_323588) baseStart_323588 baseEnd_323588 := by
    simpa [prefixWord, tailWord_323588, baseEnd_323588] using wordTrace_append hprefix tailTrace_323588
  have hstable : (prefixWord ++ tailWord_323588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323588).length < 2 ^ (prefixWord ++ tailWord_323588).sum := by decide
  have hdescent : baseEnd_323588 < baseStart_323588 := by decide
  rcases family_descends (prefixWord ++ tailWord_323588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323605 : List Nat := [1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_323605 : Nat := 118140960795 + 323605 * 2 ^ 59
def prefixEnd_323605 : Nat := 4983230072969 + 3 ^ 40 * 323605 * 2
def baseEnd_323605 : Nat := 98468093154555038606977

theorem tailTrace_323605 : CollatzResearch.WordTrace tailWord_323605 prefixEnd_323605 98468093154555038606977 := by
  unfold tailWord_323605
  simp only [CollatzResearch.WordTrace]
  refine ⟨11802843992641827179052269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7868562661761218119368179 11802843992641827179052269)
  ·
    refine ⟨4426066497240685192144601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11802843992641827179052269 4426066497240685192144601)
    ·
      refine ⟨3319549872930513894108451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4426066497240685192144601 3319549872930513894108451)
      ·
        refine ⟨4979324809395770841162677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319549872930513894108451 4979324809395770841162677)
        ·
          refine ⟨466811700880853516359001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4979324809395770841162677 466811700880853516359001)
          ·
            refine ⟨350108775660640137269251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466811700880853516359001 350108775660640137269251)
            ·
              refine ⟨525163163490960205903877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350108775660640137269251 525163163490960205903877)
              ·
                refine ⟨98468093154555038606977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 525163163490960205903877 98468093154555038606977)
                ·
                  rfl

theorem cell19_323605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_323605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323605 prefixEnd_323605 := by exact prefixLift 323605
  have htrace : WordTrace (prefixWord ++ tailWord_323605) baseStart_323605 baseEnd_323605 := by
    simpa [prefixWord, tailWord_323605, baseEnd_323605] using wordTrace_append hprefix tailTrace_323605
  have hstable : (prefixWord ++ tailWord_323605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323605).length < 2 ^ (prefixWord ++ tailWord_323605).sum := by decide
  have hdescent : baseEnd_323605 < baseStart_323605 := by decide
  rcases family_descends (prefixWord ++ tailWord_323605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323683 : List Nat := [1, 1, 1, 5, 1, 1, 6, 3]
def baseStart_323683 : Nat := 118140960795 + 323683 * 2 ^ 59
def prefixEnd_323683 : Nat := 4983230072969 + 3 ^ 40 * 323683 * 2
def baseEnd_323683 : Nat := 98491827371473968873431

theorem tailTrace_323683 : CollatzResearch.WordTrace tailWord_323683 prefixEnd_323683 98491827371473968873431 := by
  unfold tailWord_323683
  simp only [CollatzResearch.WordTrace]
  refine ⟨11805688886359246500391703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7870459257572831000261135 11805688886359246500391703)
  ·
    refine ⟨17708533329538869750587555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11805688886359246500391703 17708533329538869750587555)
    ·
      refine ⟨26562799994308304625881333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17708533329538869750587555 26562799994308304625881333)
      ·
        refine ⟨2490262499466403558676375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26562799994308304625881333 2490262499466403558676375)
        ·
          refine ⟨3735393749199605338014563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490262499466403558676375 3735393749199605338014563)
          ·
            refine ⟨5603090623799408007021845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735393749199605338014563 5603090623799408007021845)
            ·
              refine ⟨262644872990597250329149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5603090623799408007021845 262644872990597250329149)
              ·
                refine ⟨98491827371473968873431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262644872990597250329149 98491827371473968873431)
                ·
                  rfl

theorem cell19_323683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_323683 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323683 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323683 prefixEnd_323683 := by exact prefixLift 323683
  have htrace : WordTrace (prefixWord ++ tailWord_323683) baseStart_323683 baseEnd_323683 := by
    simpa [prefixWord, tailWord_323683, baseEnd_323683] using wordTrace_append hprefix tailTrace_323683
  have hstable : (prefixWord ++ tailWord_323683).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323683).length < 2 ^ (prefixWord ++ tailWord_323683).sum := by decide
  have hdescent : baseEnd_323683 < baseStart_323683 := by decide
  rcases family_descends (prefixWord ++ tailWord_323683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323702 : List Nat := [5, 1, 1, 2, 1, 2, 7]
def baseStart_323702 : Nat := 118140960795 + 323702 * 2 ^ 59
def prefixEnd_323702 : Nat := 4983230072969 + 3 ^ 40 * 323702 * 2
def baseEnd_323702 : Nat := 32832536261095851483719

theorem tailTrace_323702 : CollatzResearch.WordTrace tailWord_323702 prefixEnd_323702 32832536261095851483719 := by
  unfold tailWord_323702
  simp only [CollatzResearch.WordTrace]
  refine ⟨737898867080650796583335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7870921248860275163555573 737898867080650796583335)
  ·
    refine ⟨1106848300620976194875003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 737898867080650796583335 1106848300620976194875003)
    ·
      refine ⟨1660272450931464292312505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106848300620976194875003 1660272450931464292312505)
      ·
        refine ⟨1245204338198598219234379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1660272450931464292312505 1245204338198598219234379)
        ·
          refine ⟨1867806507297897328851569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245204338198598219234379 1867806507297897328851569)
          ·
            refine ⟨1400854880473422996638677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1867806507297897328851569 1400854880473422996638677)
            ·
              refine ⟨32832536261095851483719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1400854880473422996638677 32832536261095851483719)
              ·
                rfl

theorem cell19_323702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_323702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323702 prefixEnd_323702 := by exact prefixLift 323702
  have htrace : WordTrace (prefixWord ++ tailWord_323702) baseStart_323702 baseEnd_323702 := by
    simpa [prefixWord, tailWord_323702, baseEnd_323702] using wordTrace_append hprefix tailTrace_323702
  have hstable : (prefixWord ++ tailWord_323702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323702).length < 2 ^ (prefixWord ++ tailWord_323702).sum := by decide
  have hdescent : baseEnd_323702 < baseStart_323702 := by decide
  rcases family_descends (prefixWord ++ tailWord_323702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323761 : List Nat := [1, 2, 2, 5, 9]
def baseStart_323761 : Nat := 118140960795 + 323761 * 2 ^ 59
def prefixEnd_323761 : Nat := 4983230072969 + 3 ^ 40 * 323761 * 2
def baseEnd_323761 : Nat := 3648724503273811079255

theorem tailTrace_323761 : CollatzResearch.WordTrace tailWord_323761 prefixEnd_323761 3648724503273811079255 := by
  unfold tailWord_323761
  simp only [CollatzResearch.WordTrace]
  refine ⟨11808533780076665821731137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7872355853384443881154091 11808533780076665821731137)
  ·
    refine ⟨8856400335057499366298353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11808533780076665821731137 8856400335057499366298353)
    ·
      refine ⟨6642300251293124524723765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8856400335057499366298353 6642300251293124524723765)
      ·
        refine ⟨622715648558730424192853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6642300251293124524723765 622715648558730424192853)
        ·
          refine ⟨3648724503273811079255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 622715648558730424192853 3648724503273811079255)
          ·
            rfl

theorem cell19_323761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 9].length) (baseStart_323761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323761 prefixEnd_323761 := by exact prefixLift 323761
  have htrace : WordTrace (prefixWord ++ tailWord_323761) baseStart_323761 baseEnd_323761 := by
    simpa [prefixWord, tailWord_323761, baseEnd_323761] using wordTrace_append hprefix tailTrace_323761
  have hstable : (prefixWord ++ tailWord_323761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323761).length < 2 ^ (prefixWord ++ tailWord_323761).sum := by decide
  have hdescent : baseEnd_323761 < baseStart_323761 := by decide
  rcases family_descends (prefixWord ++ tailWord_323761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323774 : List Nat := [4, 2, 1, 1, 5, 1, 1, 4]
def baseStart_323774 : Nat := 118140960795 + 323774 * 2 ^ 59
def prefixEnd_323774 : Nat := 4983230072969 + 3 ^ 40 * 323774 * 2
def baseEnd_323774 : Nat := 98519517291212720850961

theorem tailTrace_323774 : CollatzResearch.WordTrace tailWord_323774 prefixEnd_323774 98519517291212720850961 := by
  unfold tailWord_323774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476125991128696130244297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7872671952686379361302917 1476125991128696130244297)
  ·
    refine ⟨1107094493346522097683223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1476125991128696130244297 1107094493346522097683223)
    ·
      refine ⟨1660641740019783146524835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107094493346522097683223 1660641740019783146524835)
      ·
        refine ⟨2490962610029674719787253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660641740019783146524835 2490962610029674719787253)
        ·
          refine ⟨233527744690282004980055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2490962610029674719787253 233527744690282004980055)
          ·
            refine ⟨350291617035423007470083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233527744690282004980055 350291617035423007470083)
            ·
              refine ⟨525437425553134511205125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350291617035423007470083 525437425553134511205125)
              ·
                refine ⟨98519517291212720850961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 525437425553134511205125 98519517291212720850961)
                ·
                  rfl

theorem cell19_323774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_323774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323774 prefixEnd_323774 := by exact prefixLift 323774
  have htrace : WordTrace (prefixWord ++ tailWord_323774) baseStart_323774 baseEnd_323774 := by
    simpa [prefixWord, tailWord_323774, baseEnd_323774] using wordTrace_append hprefix tailTrace_323774
  have hstable : (prefixWord ++ tailWord_323774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323774).length < 2 ^ (prefixWord ++ tailWord_323774).sum := by decide
  have hdescent : baseEnd_323774 < baseStart_323774 := by decide
  rcases family_descends (prefixWord ++ tailWord_323774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323818 : List Nat := [3, 1, 3, 1, 1, 2, 8]
def baseStart_323818 : Nat := 118140960795 + 323818 * 2 ^ 59
def prefixEnd_323818 : Nat := 4983230072969 + 3 ^ 40 * 323818 * 2
def baseEnd_323818 : Nat := 32844301941277885291021

theorem tailTrace_323818 : CollatzResearch.WordTrace tailWord_323818 prefixEnd_323818 32844301941277885291021 := by
  unfold tailWord_323818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952653185217541139139027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7873741827246776371037405 2952653185217541139139027)
  ·
    refine ⟨4428979777826311708708541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2952653185217541139139027 4428979777826311708708541)
    ·
      refine ⟨1660867416684866890765703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4428979777826311708708541 1660867416684866890765703)
      ·
        refine ⟨2491301125027300336148555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660867416684866890765703 2491301125027300336148555)
        ·
          refine ⟨3736951687540950504222833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491301125027300336148555 3736951687540950504222833)
          ·
            refine ⟨2802713765655712878167125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3736951687540950504222833 2802713765655712878167125)
            ·
              refine ⟨32844301941277885291021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2802713765655712878167125 32844301941277885291021)
              ·
                rfl

theorem cell19_323818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_323818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323818 prefixEnd_323818 := by exact prefixLift 323818
  have htrace : WordTrace (prefixWord ++ tailWord_323818) baseStart_323818 baseEnd_323818 := by
    simpa [prefixWord, tailWord_323818, baseEnd_323818] using wordTrace_append hprefix tailTrace_323818
  have hstable : (prefixWord ++ tailWord_323818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323818).length < 2 ^ (prefixWord ++ tailWord_323818).sum := by decide
  have hdescent : baseEnd_323818 < baseStart_323818 := by decide
  rcases family_descends (prefixWord ++ tailWord_323818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323892 : List Nat := [2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_323892 : Nat := 118140960795 + 323892 * 2 ^ 59
def prefixEnd_323892 : Nat := 4983230072969 + 3 ^ 40 * 323892 * 2
def baseEnd_323892 : Nat := 98555422901423410228417

theorem tailTrace_323892 : CollatzResearch.WordTrace tailWord_323892 prefixEnd_323892 98555422901423410228417 := by
  unfold tailWord_323892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906655871301037597374965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7875541161734716796499953 5906655871301037597374965)
  ·
    refine ⟨553748987934472274753903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5906655871301037597374965 553748987934472274753903)
    ·
      refine ⟨830623481901708412130855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553748987934472274753903 830623481901708412130855)
      ·
        refine ⟨1245935222852562618196283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830623481901708412130855 1245935222852562618196283)
        ·
          refine ⟨1868902834278843927294425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245935222852562618196283 1868902834278843927294425)
          ·
            refine ⟨1401677125709132945470819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1868902834278843927294425 1401677125709132945470819)
            ·
              refine ⟨2102515688563699418206229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401677125709132945470819 2102515688563699418206229)
              ·
                refine ⟨98555422901423410228417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2102515688563699418206229 98555422901423410228417)
                ·
                  rfl

theorem cell19_323892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_323892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_323892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_323892 prefixEnd_323892 := by exact prefixLift 323892
  have htrace : WordTrace (prefixWord ++ tailWord_323892) baseStart_323892 baseEnd_323892 := by
    simpa [prefixWord, tailWord_323892, baseEnd_323892] using wordTrace_append hprefix tailTrace_323892
  have hstable : (prefixWord ++ tailWord_323892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323892).length < 2 ^ (prefixWord ++ tailWord_323892).sum := by decide
  have hdescent : baseEnd_323892 < baseStart_323892 := by decide
  rcases family_descends (prefixWord ++ tailWord_323892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324021 : List Nat := [1, 3, 3, 2, 4, 1, 2, 3]
def baseStart_324021 : Nat := 118140960795 + 324021 * 2 ^ 59
def prefixEnd_324021 : Nat := 4983230072969 + 3 ^ 40 * 324021 * 2
def baseEnd_324021 : Nat := 98594675644789333361399

theorem tailTrace_324021 : CollatzResearch.WordTrace tailWord_324021 prefixEnd_324021 98594675644789333361399 := by
  unfold tailWord_324021
  simp only [CollatzResearch.WordTrace]
  refine ⟨11818016759134730226195917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7878677839423153484130611 11818016759134730226195917)
  ·
    refine ⟨4431756284675523834823469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11818016759134730226195917 4431756284675523834823469)
    ·
      refine ⟨1661908606753321438058801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4431756284675523834823469 1661908606753321438058801)
      ·
        refine ⟨1246431455064991078544101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1661908606753321438058801 1246431455064991078544101)
        ·
          refine ⟨233705897824685827227019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1246431455064991078544101 233705897824685827227019)
          ·
            refine ⟨350558846737028740840529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233705897824685827227019 350558846737028740840529)
            ·
              refine ⟨262919135052771555630397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350558846737028740840529 262919135052771555630397)
              ·
                refine ⟨98594675644789333361399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262919135052771555630397 98594675644789333361399)
                ·
                  rfl

theorem cell19_324021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_324021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324021 prefixEnd_324021 := by exact prefixLift 324021
  have htrace : WordTrace (prefixWord ++ tailWord_324021) baseStart_324021 baseEnd_324021 := by
    simpa [prefixWord, tailWord_324021, baseEnd_324021] using wordTrace_append hprefix tailTrace_324021
  have hstable : (prefixWord ++ tailWord_324021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324021).length < 2 ^ (prefixWord ++ tailWord_324021).sum := by decide
  have hdescent : baseEnd_324021 < baseStart_324021 := by decide
  rcases family_descends (prefixWord ++ tailWord_324021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324025 : List Nat := [1, 2, 1, 4, 3, 1, 4, 3]
def baseStart_324025 : Nat := 118140960795 + 324025 * 2 ^ 59
def prefixEnd_324025 : Nat := 4983230072969 + 3 ^ 40 * 324025 * 2
def baseEnd_324025 : Nat := 98595892784118509272499

theorem tailTrace_324025 : CollatzResearch.WordTrace tailWord_324025 prefixEnd_324025 98595892784118509272499 := by
  unfold tailWord_324025
  simp only [CollatzResearch.WordTrace]
  refine ⟨11818162651120238909341529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7878775100746825939561019 11818162651120238909341529)
  ·
    refine ⟨8863621988340179182006147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11818162651120238909341529 8863621988340179182006147)
    ·
      refine ⟨13295432982510268773009221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8863621988340179182006147 13295432982510268773009221)
      ·
        refine ⟨2492893684220675394939229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13295432982510268773009221 2492893684220675394939229)
        ·
          refine ⟨934835131582753273102211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2492893684220675394939229 934835131582753273102211)
          ·
            refine ⟨1402252697374129909653317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934835131582753273102211 1402252697374129909653317)
            ·
              refine ⟨262922380757649358059997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1402252697374129909653317 262922380757649358059997)
              ·
                refine ⟨98595892784118509272499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262922380757649358059997 98595892784118509272499)
                ·
                  rfl

theorem cell19_324025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_324025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324025 prefixEnd_324025 := by exact prefixLift 324025
  have htrace : WordTrace (prefixWord ++ tailWord_324025) baseStart_324025 baseEnd_324025 := by
    simpa [prefixWord, tailWord_324025, baseEnd_324025] using wordTrace_append hprefix tailTrace_324025
  have hstable : (prefixWord ++ tailWord_324025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324025).length < 2 ^ (prefixWord ++ tailWord_324025).sum := by decide
  have hdescent : baseEnd_324025 < baseStart_324025 := by decide
  rcases family_descends (prefixWord ++ tailWord_324025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324044 : List Nat := [2, 2, 1, 4, 3, 2, 5]
def baseStart_324044 : Nat := 118140960795 + 324044 * 2 ^ 59
def prefixEnd_324044 : Nat := 4983230072969 + 3 ^ 40 * 324044 * 2
def baseEnd_324044 : Nat := 32867224731977364950075

theorem tailTrace_324044 : CollatzResearch.WordTrace tailWord_324044 prefixEnd_324044 32867224731977364950075 := by
  unfold tailWord_324044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909427819025702577141593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7879237092034270102855457 5909427819025702577141593)
  ·
    refine ⟨4432070864269276932856195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5909427819025702577141593 4432070864269276932856195)
    ·
      refine ⟨6648106296403915399284293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4432070864269276932856195 6648106296403915399284293)
      ·
        refine ⟨1246519930575734137365805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6648106296403915399284293 1246519930575734137365805)
        ·
          refine ⟨467444973965900301512177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1246519930575734137365805 467444973965900301512177)
          ·
            refine ⟨350583730474425226134133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467444973965900301512177 350583730474425226134133)
            ·
              refine ⟨32867224731977364950075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350583730474425226134133 32867224731977364950075)
              ·
                rfl

theorem cell19_324044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_324044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324044 prefixEnd_324044 := by exact prefixLift 324044
  have htrace : WordTrace (prefixWord ++ tailWord_324044) baseStart_324044 baseEnd_324044 := by
    simpa [prefixWord, tailWord_324044, baseEnd_324044] using wordTrace_append hprefix tailTrace_324044
  have hstable : (prefixWord ++ tailWord_324044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324044).length < 2 ^ (prefixWord ++ tailWord_324044).sum := by decide
  have hdescent : baseEnd_324044 < baseStart_324044 := by decide
  rcases family_descends (prefixWord ++ tailWord_324044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324065 : List Nat := [1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_324065 : Nat := 118140960795 + 324065 * 2 ^ 59
def prefixEnd_324065 : Nat := 4983230072969 + 3 ^ 40 * 324065 * 2
def baseEnd_324065 : Nat := 98608064177410268383501

theorem tailTrace_324065 : CollatzResearch.WordTrace tailWord_324065 prefixEnd_324065 98608064177410268383501 := by
  unfold tailWord_324065
  simp only [CollatzResearch.WordTrace]
  refine ⟨11819621570975325740797649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7879747713983550493865099 11819621570975325740797649)
  ·
    refine ⟨8864716178231494305598237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11819621570975325740797649 8864716178231494305598237)
    ·
      refine ⟨3324268566836810364599339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8864716178231494305598237 3324268566836810364599339)
      ·
        refine ⟨4986402850255215546899009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3324268566836810364599339 4986402850255215546899009)
        ·
          refine ⟨3739802137691411660174257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4986402850255215546899009 3739802137691411660174257)
          ·
            refine ⟨2804851603268558745130693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3739802137691411660174257 2804851603268558745130693)
            ·
              refine ⟨525909675612854764712005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2804851603268558745130693 525909675612854764712005)
              ·
                refine ⟨98608064177410268383501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 525909675612854764712005 98608064177410268383501)
                ·
                  rfl

theorem cell19_324065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_324065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324065 prefixEnd_324065 := by exact prefixLift 324065
  have htrace : WordTrace (prefixWord ++ tailWord_324065) baseStart_324065 baseEnd_324065 := by
    simpa [prefixWord, tailWord_324065, baseEnd_324065] using wordTrace_append hprefix tailTrace_324065
  have hstable : (prefixWord ++ tailWord_324065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324065).length < 2 ^ (prefixWord ++ tailWord_324065).sum := by decide
  have hdescent : baseEnd_324065 < baseStart_324065 := by decide
  rcases family_descends (prefixWord ++ tailWord_324065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324103 : List Nat := [1, 1, 4, 3, 3, 7]
def baseStart_324103 : Nat := 118140960795 + 324103 * 2 ^ 59
def prefixEnd_324103 : Nat := 4983230072969 + 3 ^ 40 * 324103 * 2
def baseEnd_324103 : Nat := 10957736333448604393217

theorem tailTrace_324103 : CollatzResearch.WordTrace tailWord_324103 prefixEnd_324103 10957736333448604393217 := by
  unfold tailWord_324103
  simp only [CollatzResearch.WordTrace]
  refine ⟨11821007544837658230680963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7880671696558438820453975 11821007544837658230680963)
  ·
    refine ⟨17731511317256487346021445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11821007544837658230680963 17731511317256487346021445)
    ·
      refine ⟨3324658371985591377379021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17731511317256487346021445 3324658371985591377379021)
      ·
        refine ⟨1246746889494596766517133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3324658371985591377379021 1246746889494596766517133)
        ·
          refine ⟨467530083560473787443925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1246746889494596766517133 467530083560473787443925)
          ·
            refine ⟨10957736333448604393217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 467530083560473787443925 10957736333448604393217)
            ·
              rfl

theorem cell19_324103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_324103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324103 prefixEnd_324103 := by exact prefixLift 324103
  have htrace : WordTrace (prefixWord ++ tailWord_324103) baseStart_324103 baseEnd_324103 := by
    simpa [prefixWord, tailWord_324103, baseEnd_324103] using wordTrace_append hprefix tailTrace_324103
  have hstable : (prefixWord ++ tailWord_324103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324103).length < 2 ^ (prefixWord ++ tailWord_324103).sum := by decide
  have hdescent : baseEnd_324103 < baseStart_324103 := by decide
  rcases family_descends (prefixWord ++ tailWord_324103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324120 : List Nat := [2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_324120 : Nat := 118140960795 + 324120 * 2 ^ 59
def prefixEnd_324120 : Nat := 4983230072969 + 3 ^ 40 * 324120 * 2
def baseEnd_324120 : Nat := 98624799843186437161129

theorem tailTrace_324120 : CollatzResearch.WordTrace tailWord_324120 prefixEnd_324120 98624799843186437161129 := by
  unfold tailWord_324120
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910813792888035067024907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7881085057184046756033209 5910813792888035067024907)
  ·
    refine ⟨8866220689332052600537361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5910813792888035067024907 8866220689332052600537361)
    ·
      refine ⟨6649665516999039450403021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8866220689332052600537361 6649665516999039450403021)
      ·
        refine ⟨2493624568874639793901133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6649665516999039450403021 2493624568874639793901133)
        ·
          refine ⟨935109213327989922712925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2493624568874639793901133 935109213327989922712925)
          ·
            refine ⟨350665954997996221017347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 935109213327989922712925 350665954997996221017347)
            ·
              refine ⟨525998932496994331526021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350665954997996221017347 525998932496994331526021)
              ·
                refine ⟨98624799843186437161129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 525998932496994331526021 98624799843186437161129)
                ·
                  rfl

theorem cell19_324120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_324120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324120 prefixEnd_324120 := by exact prefixLift 324120
  have htrace : WordTrace (prefixWord ++ tailWord_324120) baseStart_324120 baseEnd_324120 := by
    simpa [prefixWord, tailWord_324120, baseEnd_324120] using wordTrace_append hprefix tailTrace_324120
  have hstable : (prefixWord ++ tailWord_324120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324120).length < 2 ^ (prefixWord ++ tailWord_324120).sum := by decide
  have hdescent : baseEnd_324120 < baseStart_324120 := by decide
  rcases family_descends (prefixWord ++ tailWord_324120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324122 : List Nat := [3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_324122 : Nat := 118140960795 + 324122 * 2 ^ 59
def prefixEnd_324122 : Nat := 4983230072969 + 3 ^ 40 * 324122 * 2
def baseEnd_324122 : Nat := 98625408412851025116679

theorem tailTrace_324122 : CollatzResearch.WordTrace tailWord_324122 prefixEnd_324122 98625408412851025116679 := by
  unfold tailWord_324122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955425132942206118905655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7881133687845882983748413 2955425132942206118905655)
  ·
    refine ⟨4433137699413309178358483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955425132942206118905655 4433137699413309178358483)
    ·
      refine ⟨6649706549119963767537725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4433137699413309178358483 6649706549119963767537725)
      ·
        refine ⟨2493639955919986412826647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6649706549119963767537725 2493639955919986412826647)
        ·
          refine ⟨3740459933879979619239971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493639955919986412826647 3740459933879979619239971)
          ·
            refine ⟨5610689900819969428859957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740459933879979619239971 5610689900819969428859957)
            ·
              refine ⟨526002178201872133955621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5610689900819969428859957 526002178201872133955621)
              ·
                refine ⟨98625408412851025116679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526002178201872133955621 98625408412851025116679)
                ·
                  rfl

theorem cell19_324122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_324122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324122 prefixEnd_324122 := by exact prefixLift 324122
  have htrace : WordTrace (prefixWord ++ tailWord_324122) baseStart_324122 baseEnd_324122 := by
    simpa [prefixWord, tailWord_324122, baseEnd_324122] using wordTrace_append hprefix tailTrace_324122
  have hstable : (prefixWord ++ tailWord_324122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324122).length < 2 ^ (prefixWord ++ tailWord_324122).sum := by decide
  have hdescent : baseEnd_324122 < baseStart_324122 := by decide
  rcases family_descends (prefixWord ++ tailWord_324122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324135 : List Nat := [1, 1, 7, 2, 1, 1, 3, 3]
def baseStart_324135 : Nat := 118140960795 + 324135 * 2 ^ 59
def prefixEnd_324135 : Nat := 4983230072969 + 3 ^ 40 * 324135 * 2
def baseEnd_324135 : Nat := 98629364115670846827755

theorem tailTrace_324135 : CollatzResearch.WordTrace tailWord_324135 prefixEnd_324135 98629364115670846827755 := by
  unfold tailWord_324135
  simp only [CollatzResearch.WordTrace]
  refine ⟨11822174680721727695845859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7881449787147818463897239 11822174680721727695845859)
  ·
    refine ⟨17733262021082591543768789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11822174680721727695845859 17733262021082591543768789)
    ·
      refine ⟨415623328619123239307081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17733262021082591543768789 415623328619123239307081)
      ·
        refine ⟨311717496464342429480311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415623328619123239307081 311717496464342429480311)
        ·
          refine ⟨467576244696513644220467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311717496464342429480311 467576244696513644220467)
          ·
            refine ⟨701364367044770466330701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467576244696513644220467 701364367044770466330701)
            ·
              refine ⟨263011637641788924874013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701364367044770466330701 263011637641788924874013)
              ·
                refine ⟨98629364115670846827755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263011637641788924874013 98629364115670846827755)
                ·
                  rfl

theorem cell19_324135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_324135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324135 prefixEnd_324135 := by exact prefixLift 324135
  have htrace : WordTrace (prefixWord ++ tailWord_324135) baseStart_324135 baseEnd_324135 := by
    simpa [prefixWord, tailWord_324135, baseEnd_324135] using wordTrace_append hprefix tailTrace_324135
  have hstable : (prefixWord ++ tailWord_324135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324135).length < 2 ^ (prefixWord ++ tailWord_324135).sum := by decide
  have hdescent : baseEnd_324135 < baseStart_324135 := by decide
  rcases family_descends (prefixWord ++ tailWord_324135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324194 : List Nat := [3, 3, 2, 3, 1, 1, 1, 5]
def baseStart_324194 : Nat := 118140960795 + 324194 * 2 ^ 59
def prefixEnd_324194 : Nat := 4983230072969 + 3 ^ 40 * 324194 * 2
def baseEnd_324194 : Nat := 98647316920776191516483

theorem tailTrace_324194 : CollatzResearch.WordTrace tailWord_324194 prefixEnd_324194 98647316920776191516483 := by
  unfold tailWord_324194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956081646876995193060909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7882884391671987181495757 2956081646876995193060909)
  ·
    refine ⟨1108530617578873197397841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2956081646876995193060909 1108530617578873197397841)
    ·
      refine ⟨831397963184154898048381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1108530617578873197397841 831397963184154898048381)
      ·
        refine ⟨311774236194058086768143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 831397963184154898048381 311774236194058086768143)
        ·
          refine ⟨467661354291087130152215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311774236194058086768143 467661354291087130152215)
          ·
            refine ⟨701492031436630695228323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467661354291087130152215 701492031436630695228323)
            ·
              refine ⟨1052238047154946042842485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701492031436630695228323 1052238047154946042842485)
              ·
                refine ⟨98647316920776191516483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1052238047154946042842485 98647316920776191516483)
                ·
                  rfl

theorem cell19_324194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_324194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324194 prefixEnd_324194 := by exact prefixLift 324194
  have htrace : WordTrace (prefixWord ++ tailWord_324194) baseStart_324194 baseEnd_324194 := by
    simpa [prefixWord, tailWord_324194, baseEnd_324194] using wordTrace_append hprefix tailTrace_324194
  have hstable : (prefixWord ++ tailWord_324194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324194).length < 2 ^ (prefixWord ++ tailWord_324194).sum := by decide
  have hdescent : baseEnd_324194 < baseStart_324194 := by decide
  rcases family_descends (prefixWord ++ tailWord_324194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324213 : List Nat := [1, 3, 4, 2, 3, 1, 5]
def baseStart_324213 : Nat := 118140960795 + 324213 * 2 ^ 59
def prefixEnd_324213 : Nat := 4983230072969 + 3 ^ 40 * 324213 * 2
def baseEnd_324213 : Nat := 32884366110863259031403

theorem tailTrace_324213 : CollatzResearch.WordTrace tailWord_324213 prefixEnd_324213 32884366110863259031403 := by
  unfold tailWord_324213
  simp only [CollatzResearch.WordTrace]
  refine ⟨11825019574439147017185293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7883346382959431344790195 11825019574439147017185293)
  ·
    refine ⟨4434382340414680131444485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11825019574439147017185293 4434382340414680131444485)
    ·
      refine ⟨831446688827752524645841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4434382340414680131444485 831446688827752524645841)
      ·
        refine ⟨623585016620814393484381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 831446688827752524645841 623585016620814393484381)
        ·
          refine ⟨233844381232805397556643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 623585016620814393484381 233844381232805397556643)
          ·
            refine ⟨350766571849208096334965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233844381232805397556643 350766571849208096334965)
            ·
              refine ⟨32884366110863259031403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350766571849208096334965 32884366110863259031403)
              ·
                rfl

theorem cell19_324213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_324213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324213 prefixEnd_324213 := by exact prefixLift 324213
  have htrace : WordTrace (prefixWord ++ tailWord_324213) baseStart_324213 baseEnd_324213 := by
    simpa [prefixWord, tailWord_324213, baseEnd_324213] using wordTrace_append hprefix tailTrace_324213
  have hstable : (prefixWord ++ tailWord_324213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324213).length < 2 ^ (prefixWord ++ tailWord_324213).sum := by decide
  have hdescent : baseEnd_324213 < baseStart_324213 := by decide
  rcases family_descends (prefixWord ++ tailWord_324213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324217 : List Nat := [1, 2, 1, 3, 3, 4, 5]
def baseStart_324217 : Nat := 118140960795 + 324217 * 2 ^ 59
def prefixEnd_324217 : Nat := 4983230072969 + 3 ^ 40 * 324217 * 2
def baseEnd_324217 : Nat := 32884771823972984335103

theorem tailTrace_324217 : CollatzResearch.WordTrace tailWord_324217 prefixEnd_324217 32884771823972984335103 := by
  unfold tailWord_324217
  simp only [CollatzResearch.WordTrace]
  refine ⟨11825165466424655700330905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7883443644283103800220603 11825165466424655700330905)
  ·
    refine ⟨8868874099818491775248179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11825165466424655700330905 8868874099818491775248179)
    ·
      refine ⟨13303311149727737662872269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8868874099818491775248179 13303311149727737662872269)
      ·
        refine ⟨4988741681147901623577101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13303311149727737662872269 4988741681147901623577101)
        ·
          refine ⟨1870778130430463108841413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4988741681147901623577101 1870778130430463108841413)
          ·
            refine ⟨350770899455711832907765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1870778130430463108841413 350770899455711832907765)
            ·
              refine ⟨32884771823972984335103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350770899455711832907765 32884771823972984335103)
              ·
                rfl

theorem cell19_324217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_324217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324217 prefixEnd_324217 := by exact prefixLift 324217
  have htrace : WordTrace (prefixWord ++ tailWord_324217) baseStart_324217 baseEnd_324217 := by
    simpa [prefixWord, tailWord_324217, baseEnd_324217] using wordTrace_append hprefix tailTrace_324217
  have hstable : (prefixWord ++ tailWord_324217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324217).length < 2 ^ (prefixWord ++ tailWord_324217).sum := by decide
  have hdescent : baseEnd_324217 < baseStart_324217 := by decide
  rcases family_descends (prefixWord ++ tailWord_324217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324234 : List Nat := [3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_324234 : Nat := 118140960795 + 324234 * 2 ^ 59
def prefixEnd_324234 : Nat := 4983230072969 + 3 ^ 40 * 324234 * 2
def baseEnd_324234 : Nat := 98659488314067950627485

theorem tailTrace_324234 : CollatzResearch.WordTrace tailWord_324234 prefixEnd_324234 98659488314067950627485 := by
  unfold tailWord_324234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956446376840766900924939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7883857004908711735799837 2956446376840766900924939)
  ·
    refine ⟨4434669565261150351387409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2956446376840766900924939 4434669565261150351387409)
    ·
      refine ⟨3326002173945862763540557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4434669565261150351387409 3326002173945862763540557)
      ·
        refine ⟨1247250815229698536327709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3326002173945862763540557 1247250815229698536327709)
        ·
          refine ⟨467719055711136951122891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1247250815229698536327709 467719055711136951122891)
          ·
            refine ⟨701578583566705426684337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467719055711136951122891 701578583566705426684337)
            ·
              refine ⟨526183937675029070013253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701578583566705426684337 526183937675029070013253)
              ·
                refine ⟨98659488314067950627485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526183937675029070013253 98659488314067950627485)
                ·
                  rfl

theorem cell19_324234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_324234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324234 prefixEnd_324234 := by exact prefixLift 324234
  have htrace : WordTrace (prefixWord ++ tailWord_324234) baseStart_324234 baseEnd_324234 := by
    simpa [prefixWord, tailWord_324234, baseEnd_324234] using wordTrace_append hprefix tailTrace_324234
  have hstable : (prefixWord ++ tailWord_324234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324234).length < 2 ^ (prefixWord ++ tailWord_324234).sum := by decide
  have hdescent : baseEnd_324234 < baseStart_324234 := by decide
  rcases family_descends (prefixWord ++ tailWord_324234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324295 : List Nat := [1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_324295 : Nat := 118140960795 + 324295 * 2 ^ 59
def prefixEnd_324295 : Nat := 4983230072969 + 3 ^ 40 * 324295 * 2
def baseEnd_324295 : Nat := 98678049688837883271763

theorem tailTrace_324295 : CollatzResearch.WordTrace tailWord_324295 prefixEnd_324295 98678049688837883271763 := by
  unfold tailWord_324295
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828010360142075021670339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7885340240094716681113559 11828010360142075021670339)
  ·
    refine ⟨17742015540213112532505509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11828010360142075021670339 17742015540213112532505509)
    ·
      refine ⟨3326627913789958599844783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17742015540213112532505509 3326627913789958599844783)
      ·
        refine ⟨4989941870684937899767175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326627913789958599844783 4989941870684937899767175)
        ·
          refine ⟨7484912806027406849650763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4989941870684937899767175 7484912806027406849650763)
          ·
            refine ⟨11227369209041110274476145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7484912806027406849650763 11227369209041110274476145)
            ·
              refine ⟨8420526906780832705857109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11227369209041110274476145 8420526906780832705857109)
              ·
                refine ⟨98678049688837883271763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8420526906780832705857109 98678049688837883271763)
                ·
                  rfl

theorem cell19_324295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_324295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324295 prefixEnd_324295 := by exact prefixLift 324295
  have htrace : WordTrace (prefixWord ++ tailWord_324295) baseStart_324295 baseEnd_324295 := by
    simpa [prefixWord, tailWord_324295, baseEnd_324295] using wordTrace_append hprefix tailTrace_324295
  have hstable : (prefixWord ++ tailWord_324295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324295).length < 2 ^ (prefixWord ++ tailWord_324295).sum := by decide
  have hdescent : baseEnd_324295 < baseStart_324295 := by decide
  rcases family_descends (prefixWord ++ tailWord_324295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324308 : List Nat := [2, 4, 1, 3, 2, 1, 3, 3]
def baseStart_324308 : Nat := 118140960795 + 324308 * 2 ^ 59
def prefixEnd_324308 : Nat := 4983230072969 + 3 ^ 40 * 324308 * 2
def baseEnd_324308 : Nat := 98682005391657704982839

theorem tailTrace_324308 : CollatzResearch.WordTrace tailWord_324308 prefixEnd_324308 98682005391657704982839 := by
  unfold tailWord_324308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5914242254547489120946789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7885656339396652161262385 5914242254547489120946789)
  ·
    refine ⟨1108920422727654210177523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5914242254547489120946789 1108920422727654210177523)
    ·
      refine ⟨1663380634091481315266285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108920422727654210177523 1663380634091481315266285)
      ·
        refine ⟨623767737784305493224857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1663380634091481315266285 623767737784305493224857)
        ·
          refine ⟨467825803338229119918643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623767737784305493224857 467825803338229119918643)
          ·
            refine ⟨701738705007343679877965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467825803338229119918643 701738705007343679877965)
            ·
              refine ⟨263152014377753879954237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701738705007343679877965 263152014377753879954237)
              ·
                refine ⟨98682005391657704982839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263152014377753879954237 98682005391657704982839)
                ·
                  rfl

theorem cell19_324308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_324308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324308 prefixEnd_324308 := by exact prefixLift 324308
  have htrace : WordTrace (prefixWord ++ tailWord_324308) baseStart_324308 baseEnd_324308 := by
    simpa [prefixWord, tailWord_324308, baseEnd_324308] using wordTrace_append hprefix tailTrace_324308
  have hstable : (prefixWord ++ tailWord_324308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324308).length < 2 ^ (prefixWord ++ tailWord_324308).sum := by decide
  have hdescent : baseEnd_324308 < baseStart_324308 := by decide
  rcases family_descends (prefixWord ++ tailWord_324308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324369 : List Nat := [1, 2, 2, 1, 1, 3, 6, 3]
def baseStart_324369 : Nat := 118140960795 + 324369 * 2 ^ 59
def prefixEnd_324369 : Nat := 4983230072969 + 3 ^ 40 * 324369 * 2
def baseEnd_324369 : Nat := 98700566766427637627117

theorem tailTrace_324369 : CollatzResearch.WordTrace tailWord_324369 prefixEnd_324369 98700566766427637627117 := by
  unfold tailWord_324369
  simp only [CollatzResearch.WordTrace]
  refine ⟨11830709361873985659864161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7887139574582657106576107 11830709361873985659864161)
  ·
    refine ⟨8873032021405489244898121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11830709361873985659864161 8873032021405489244898121)
    ·
      refine ⟨6654774016054116933673591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8873032021405489244898121 6654774016054116933673591)
      ·
        refine ⟨9982161024081175400510387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6654774016054116933673591 9982161024081175400510387)
        ·
          refine ⟨14973241536121763100765581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9982161024081175400510387 14973241536121763100765581)
          ·
            refine ⟨5614965576045661162787093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14973241536121763100765581 5614965576045661162787093)
            ·
              refine ⟨263201511377140367005645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5614965576045661162787093 263201511377140367005645)
              ·
                refine ⟨98700566766427637627117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263201511377140367005645 98700566766427637627117)
                ·
                  rfl

theorem cell19_324369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_324369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324369 prefixEnd_324369 := by exact prefixLift 324369
  have htrace : WordTrace (prefixWord ++ tailWord_324369) baseStart_324369 baseEnd_324369 := by
    simpa [prefixWord, tailWord_324369, baseEnd_324369] using wordTrace_append hprefix tailTrace_324369
  have hstable : (prefixWord ++ tailWord_324369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324369).length < 2 ^ (prefixWord ++ tailWord_324369).sum := by decide
  have hdescent : baseEnd_324369 < baseStart_324369 := by decide
  rcases family_descends (prefixWord ++ tailWord_324369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324371 : List Nat := [1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_324371 : Nat := 118140960795 + 324371 * 2 ^ 59
def prefixEnd_324371 : Nat := 4983230072969 + 3 ^ 40 * 324371 * 2
def baseEnd_324371 : Nat := 98701175336092225582667

theorem tailTrace_324371 : CollatzResearch.WordTrace tailWord_324371 prefixEnd_324371 98701175336092225582667 := by
  unfold tailWord_324371
  simp only [CollatzResearch.WordTrace]
  refine ⟨11830782307866740001436967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7887188205244493334291311 11830782307866740001436967)
  ·
    refine ⟨17746173461800110002155451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11830782307866740001436967 17746173461800110002155451)
    ·
      refine ⟨26619260192700165003233177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17746173461800110002155451 26619260192700165003233177)
      ·
        refine ⟨19964445144525123752424883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26619260192700165003233177 19964445144525123752424883)
        ·
          refine ⟨29946667716787685628637325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19964445144525123752424883 29946667716787685628637325)
          ·
            refine ⟨11230000393795382110738997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29946667716787685628637325 11230000393795382110738997)
            ·
              refine ⟨1052812536918317072881781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11230000393795382110738997 1052812536918317072881781)
              ·
                refine ⟨98701175336092225582667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1052812536918317072881781 98701175336092225582667)
                ·
                  rfl

theorem cell19_324371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_324371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324371 prefixEnd_324371 := by exact prefixLift 324371
  have htrace : WordTrace (prefixWord ++ tailWord_324371) baseStart_324371 baseEnd_324371 := by
    simpa [prefixWord, tailWord_324371, baseEnd_324371] using wordTrace_append hprefix tailTrace_324371
  have hstable : (prefixWord ++ tailWord_324371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324371).length < 2 ^ (prefixWord ++ tailWord_324371).sum := by decide
  have hdescent : baseEnd_324371 < baseStart_324371 := by decide
  rcases family_descends (prefixWord ++ tailWord_324371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324483 : List Nat := [1, 1, 1, 3, 4, 1, 5, 3]
def baseStart_324483 : Nat := 118140960795 + 324483 * 2 ^ 59
def prefixEnd_324483 : Nat := 4983230072969 + 3 ^ 40 * 324483 * 2
def baseEnd_324483 : Nat := 98735255237309151093473

theorem tailTrace_324483 : CollatzResearch.WordTrace tailWord_324483 prefixEnd_324483 98735255237309151093473 := by
  unfold tailWord_324483
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834867283460983129514103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7889911522307322086342735 11834867283460983129514103)
  ·
    refine ⟨17752300925191474694271155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11834867283460983129514103 17752300925191474694271155)
    ·
      refine ⟨26628451387787212041406733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17752300925191474694271155 26628451387787212041406733)
      ·
        refine ⟨9985669270420204515527525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26628451387787212041406733 9985669270420204515527525)
        ·
          refine ⟨1872312988203788346661411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9985669270420204515527525 1872312988203788346661411)
          ·
            refine ⟨2808469482305682519992117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872312988203788346661411 2808469482305682519992117)
            ·
              refine ⟨263294013966157736249261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2808469482305682519992117 263294013966157736249261)
              ·
                refine ⟨98735255237309151093473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263294013966157736249261 98735255237309151093473)
                ·
                  rfl

theorem cell19_324483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_324483 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324483 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324483 prefixEnd_324483 := by exact prefixLift 324483
  have htrace : WordTrace (prefixWord ++ tailWord_324483) baseStart_324483 baseEnd_324483 := by
    simpa [prefixWord, tailWord_324483, baseEnd_324483] using wordTrace_append hprefix tailTrace_324483
  have hstable : (prefixWord ++ tailWord_324483).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324483).length < 2 ^ (prefixWord ++ tailWord_324483).sum := by decide
  have hdescent : baseEnd_324483 < baseStart_324483 := by decide
  rcases family_descends (prefixWord ++ tailWord_324483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324534 : List Nat := [5, 1, 4, 1, 1, 1, 1, 5]
def baseStart_324534 : Nat := 118140960795 + 324534 * 2 ^ 59
def prefixEnd_324534 : Nat := 4983230072969 + 3 ^ 40 * 324534 * 2
def baseEnd_324534 : Nat := 98750773763756143960001

theorem tailTrace_324534 : CollatzResearch.WordTrace tailWord_324534 prefixEnd_324534 98750773763756143960001 := by
  unfold tailWord_324534
  simp only [CollatzResearch.WordTrace]
  refine ⟨739795462892263677476291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7891151604184145893080437 739795462892263677476291)
  ·
    refine ⟨1109693194338395516214437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 739795462892263677476291 1109693194338395516214437)
    ·
      refine ⟨208067473938449159290207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1109693194338395516214437 208067473938449159290207)
      ·
        refine ⟨312101210907673738935311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208067473938449159290207 312101210907673738935311)
        ·
          refine ⟨468151816361510608402967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312101210907673738935311 468151816361510608402967)
          ·
            refine ⟨702227724542265912604451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468151816361510608402967 702227724542265912604451)
            ·
              refine ⟨1053341586813398868906677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702227724542265912604451 1053341586813398868906677)
              ·
                refine ⟨98750773763756143960001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1053341586813398868906677 98750773763756143960001)
                ·
                  rfl

theorem cell19_324534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_324534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324534 prefixEnd_324534 := by exact prefixLift 324534
  have htrace : WordTrace (prefixWord ++ tailWord_324534) baseStart_324534 baseEnd_324534 := by
    simpa [prefixWord, tailWord_324534, baseEnd_324534] using wordTrace_append hprefix tailTrace_324534
  have hstable : (prefixWord ++ tailWord_324534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324534).length < 2 ^ (prefixWord ++ tailWord_324534).sum := by decide
  have hdescent : baseEnd_324534 < baseStart_324534 := by decide
  rcases family_descends (prefixWord ++ tailWord_324534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324614 : List Nat := [6, 2, 1, 10]
def baseStart_324614 : Nat := 118140960795 + 324614 * 2 ^ 59
def prefixEnd_324614 : Nat := 4983230072969 + 3 ^ 40 * 324614 * 2
def baseEnd_324614 : Nat := 1219445883337526693605

theorem tailTrace_324614 : CollatzResearch.WordTrace tailWord_324614 prefixEnd_324614 1219445883337526693605 := by
  unfold tailWord_324614
  simp only [CollatzResearch.WordTrace]
  refine ⟨369988913937074765704153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7893096830657595001688597 369988913937074765704153)
  ·
    refine ⟨277491685452806074278115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 369988913937074765704153 277491685452806074278115)
    ·
      refine ⟨416237528179209111417173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277491685452806074278115 416237528179209111417173)
      ·
        refine ⟨1219445883337526693605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 416237528179209111417173 1219445883337526693605)
        ·
          rfl

theorem cell19_324614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 10].length) (baseStart_324614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324614 prefixEnd_324614 := by exact prefixLift 324614
  have htrace : WordTrace (prefixWord ++ tailWord_324614) baseStart_324614 baseEnd_324614 := by
    simpa [prefixWord, tailWord_324614, baseEnd_324614] using wordTrace_append hprefix tailTrace_324614
  have hstable : (prefixWord ++ tailWord_324614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324614).length < 2 ^ (prefixWord ++ tailWord_324614).sum := by decide
  have hdescent : baseEnd_324614 < baseStart_324614 := by decide
  rcases family_descends (prefixWord ++ tailWord_324614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324618 : List Nat := [3, 1, 2, 2, 3, 8]
def baseStart_324618 : Nat := 118140960795 + 324618 * 2 ^ 59
def prefixEnd_324618 : Nat := 4983230072969 + 3 ^ 40 * 324618 * 2
def baseEnd_324618 : Nat := 10975148187740982010345

theorem tailTrace_324618 : CollatzResearch.WordTrace tailWord_324618 prefixEnd_324618 10975148187740982010345 := by
  unfold tailWord_324618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959947784492975296419627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7893194091981267457119005 2959947784492975296419627)
  ·
    refine ⟨4439921676739462944629441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2959947784492975296419627 4439921676739462944629441)
    ·
      refine ⟨3329941257554597208472081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4439921676739462944629441 3329941257554597208472081)
      ·
        refine ⟨2497455943165947906354061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3329941257554597208472081 2497455943165947906354061)
        ·
          refine ⟨936545978687230464882773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2497455943165947906354061 936545978687230464882773)
          ·
            refine ⟨10975148187740982010345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 936545978687230464882773 10975148187740982010345)
            ·
              rfl

theorem cell19_324618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_324618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324618 prefixEnd_324618 := by exact prefixLift 324618
  have htrace : WordTrace (prefixWord ++ tailWord_324618) baseStart_324618 baseEnd_324618 := by
    simpa [prefixWord, tailWord_324618, baseEnd_324618] using wordTrace_append hprefix tailTrace_324618
  have hstable : (prefixWord ++ tailWord_324618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324618).length < 2 ^ (prefixWord ++ tailWord_324618).sum := by decide
  have hdescent : baseEnd_324618 < baseStart_324618 := by decide
  rcases family_descends (prefixWord ++ tailWord_324618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324673 : List Nat := [1, 2, 5, 1, 3, 1, 6]
def baseStart_324673 : Nat := 118140960795 + 324673 * 2 ^ 59
def prefixEnd_324673 : Nat := 4983230072969 + 3 ^ 40 * 324673 * 2
def baseEnd_324673 : Nat := 32931023118481668956911

theorem tailTrace_324673 : CollatzResearch.WordTrace tailWord_324673 prefixEnd_324673 32931023118481668956911 := by
  unfold tailWord_324673
  simp only [CollatzResearch.WordTrace]
  refine ⟨11841797152772645578930673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7894531435181763719287115 11841797152772645578930673)
  ·
    refine ⟨8881347864579484184198005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11841797152772645578930673 8881347864579484184198005)
    ·
      refine ⟨832626362304326642268563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8881347864579484184198005 832626362304326642268563)
      ·
        refine ⟨1248939543456489963402845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832626362304326642268563 1248939543456489963402845)
        ·
          refine ⟨468352328796183736276067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1248939543456489963402845 468352328796183736276067)
          ·
            refine ⟨702528493194275604414101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468352328796183736276067 702528493194275604414101)
            ·
              refine ⟨32931023118481668956911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 702528493194275604414101 32931023118481668956911)
              ·
                rfl

theorem cell19_324673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_324673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324673 prefixEnd_324673 := by exact prefixLift 324673
  have htrace : WordTrace (prefixWord ++ tailWord_324673) baseStart_324673 baseEnd_324673 := by
    simpa [prefixWord, tailWord_324673, baseEnd_324673] using wordTrace_append hprefix tailTrace_324673
  have hstable : (prefixWord ++ tailWord_324673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324673).length < 2 ^ (prefixWord ++ tailWord_324673).sum := by decide
  have hdescent : baseEnd_324673 < baseStart_324673 := by decide
  rcases family_descends (prefixWord ++ tailWord_324673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324711 : List Nat := [1, 1, 5, 1, 1, 3, 4, 3]
def baseStart_324711 : Nat := 118140960795 + 324711 * 2 ^ 59
def prefixEnd_324711 : Nat := 4983230072969 + 3 ^ 40 * 324711 * 2
def baseEnd_324711 : Nat := 98804632179072178026185

theorem tailTrace_324711 : CollatzResearch.WordTrace tailWord_324711 prefixEnd_324711 98804632179072178026185 := by
  unfold tailWord_324711
  simp only [CollatzResearch.WordTrace]
  refine ⟨11843183126634978068813987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7895455417756652045875991 11843183126634978068813987)
  ·
    refine ⟨17764774689952467103220981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11843183126634978068813987 17764774689952467103220981)
    ·
      refine ⟨1665447627183043790926967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17764774689952467103220981 1665447627183043790926967)
      ·
        refine ⟨2498171440774565686390451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665447627183043790926967 2498171440774565686390451)
        ·
          refine ⟨3747257161161848529585677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498171440774565686390451 3747257161161848529585677)
          ·
            refine ⟨1405221435435693198594629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3747257161161848529585677 1405221435435693198594629)
            ·
              refine ⟨263479019144192474736493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1405221435435693198594629 263479019144192474736493)
              ·
                refine ⟨98804632179072178026185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263479019144192474736493 98804632179072178026185)
                ·
                  rfl

theorem cell19_324711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_324711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324711 prefixEnd_324711 := by exact prefixLift 324711
  have htrace : WordTrace (prefixWord ++ tailWord_324711) baseStart_324711 baseEnd_324711 := by
    simpa [prefixWord, tailWord_324711, baseEnd_324711] using wordTrace_append hprefix tailTrace_324711
  have hstable : (prefixWord ++ tailWord_324711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324711).length < 2 ^ (prefixWord ++ tailWord_324711).sum := by decide
  have hdescent : baseEnd_324711 < baseStart_324711 := by decide
  rcases family_descends (prefixWord ++ tailWord_324711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324713 : List Nat := [1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_324713 : Nat := 118140960795 + 324713 * 2 ^ 59
def prefixEnd_324713 : Nat := 4983230072969 + 3 ^ 40 * 324713 * 2
def baseEnd_324713 : Nat := 98805240748736765981735

theorem tailTrace_324713 : CollatzResearch.WordTrace tailWord_324713 prefixEnd_324713 98805240748736765981735 := by
  unfold tailWord_324713
  simp only [CollatzResearch.WordTrace]
  refine ⟨11843256072627732410386793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7895504048418488273591195 11843256072627732410386793)
  ·
    refine ⟨8882442054470799307790095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11843256072627732410386793 8882442054470799307790095)
    ·
      refine ⟨13323663081706198961685143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8882442054470799307790095 13323663081706198961685143)
      ·
        refine ⟨19985494622559298442527715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13323663081706198961685143 19985494622559298442527715)
        ·
          refine ⟨29978241933838947663791573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19985494622559298442527715 29978241933838947663791573)
          ·
            refine ⟨702615045324350335870115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29978241933838947663791573 702615045324350335870115)
            ·
              refine ⟨1053922567986525503805173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702615045324350335870115 1053922567986525503805173)
              ·
                refine ⟨98805240748736765981735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1053922567986525503805173 98805240748736765981735)
                ·
                  rfl

theorem cell19_324713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_324713 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324713 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324713 prefixEnd_324713 := by exact prefixLift 324713
  have htrace : WordTrace (prefixWord ++ tailWord_324713) baseStart_324713 baseEnd_324713 := by
    simpa [prefixWord, tailWord_324713, baseEnd_324713] using wordTrace_append hprefix tailTrace_324713
  have hstable : (prefixWord ++ tailWord_324713).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324713).length < 2 ^ (prefixWord ++ tailWord_324713).sum := by decide
  have hdescent : baseEnd_324713 < baseStart_324713 := by decide
  rcases family_descends (prefixWord ++ tailWord_324713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324804 : List Nat := [2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_324804 : Nat := 118140960795 + 324804 * 2 ^ 59
def prefixEnd_324804 : Nat := 4983230072969 + 3 ^ 40 * 324804 * 2
def baseEnd_324804 : Nat := 98832930668475517959265

theorem tailTrace_324804 : CollatzResearch.WordTrace tailWord_324804 prefixEnd_324804 98832930668475517959265 := by
  unfold tailWord_324804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923287557649027475974733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7897716743532036634632977 5923287557649027475974733)
  ·
    refine ⟨2221232834118385303490525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5923287557649027475974733 2221232834118385303490525)
    ·
      refine ⟨832962312794394488808947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2221232834118385303490525 832962312794394488808947)
      ·
        refine ⟨1249443469191591733213421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832962312794394488808947 1249443469191591733213421)
        ·
          refine ⟨468541300946846899955033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1249443469191591733213421 468541300946846899955033)
          ·
            refine ⟨351405975710135174966275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468541300946846899955033 351405975710135174966275)
            ·
              refine ⟨527108963565202762449413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351405975710135174966275 527108963565202762449413)
              ·
                refine ⟨98832930668475517959265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527108963565202762449413 98832930668475517959265)
                ·
                  rfl

theorem cell19_324804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_324804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324804 prefixEnd_324804 := by exact prefixLift 324804
  have htrace : WordTrace (prefixWord ++ tailWord_324804) baseStart_324804 baseEnd_324804 := by
    simpa [prefixWord, tailWord_324804, baseEnd_324804] using wordTrace_append hprefix tailTrace_324804
  have hstable : (prefixWord ++ tailWord_324804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324804).length < 2 ^ (prefixWord ++ tailWord_324804).sum := by decide
  have hdescent : baseEnd_324804 < baseStart_324804 := by decide
  rcases family_descends (prefixWord ++ tailWord_324804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324808 : List Nat := [2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_324808 : Nat := 118140960795 + 324808 * 2 ^ 59
def prefixEnd_324808 : Nat := 4983230072969 + 3 ^ 40 * 324808 * 2
def baseEnd_324808 : Nat := 98834147807804693870365

theorem tailTrace_324808 : CollatzResearch.WordTrace tailWord_324808 prefixEnd_324808 98834147807804693870365 := by
  unfold tailWord_324808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923360503641781817547539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7897814004855709090063385 5923360503641781817547539)
  ·
    refine ⟨8885040755462672726321309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923360503641781817547539 8885040755462672726321309)
    ·
      refine ⟨3331890283298502272370491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8885040755462672726321309 3331890283298502272370491)
      ·
        refine ⟨4997835424947753408555737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3331890283298502272370491 4997835424947753408555737)
        ·
          refine ⟨3748376568710815056416803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4997835424947753408555737 3748376568710815056416803)
          ·
            refine ⟨5622564853066222584625205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748376568710815056416803 5622564853066222584625205)
            ·
              refine ⟨527115454974958367308613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5622564853066222584625205 527115454974958367308613)
              ·
                refine ⟨98834147807804693870365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527115454974958367308613 98834147807804693870365)
                ·
                  rfl

theorem cell19_324808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_324808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324808 prefixEnd_324808 := by exact prefixLift 324808
  have htrace : WordTrace (prefixWord ++ tailWord_324808) baseStart_324808 baseEnd_324808 := by
    simpa [prefixWord, tailWord_324808, baseEnd_324808] using wordTrace_append hprefix tailTrace_324808
  have hstable : (prefixWord ++ tailWord_324808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324808).length < 2 ^ (prefixWord ++ tailWord_324808).sum := by decide
  have hdescent : baseEnd_324808 < baseStart_324808 := by decide
  rcases family_descends (prefixWord ++ tailWord_324808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324922 : List Nat := [3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_324922 : Nat := 118140960795 + 324922 * 2 ^ 59
def prefixEnd_324922 : Nat := 4983230072969 + 3 ^ 40 * 324922 * 2
def baseEnd_324922 : Nat := 98868836278686207336721

theorem tailTrace_324922 : CollatzResearch.WordTrace tailWord_324922 prefixEnd_324922 98868836278686207336721 := by
  unfold tailWord_324922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962719732217640276186255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7900585952580374069830013 2962719732217640276186255)
  ·
    refine ⟨4444079598326460414279383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2962719732217640276186255 4444079598326460414279383)
    ·
      refine ⟨6666119397489690621419075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444079598326460414279383 6666119397489690621419075)
      ·
        refine ⟨9999179096234535932128613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666119397489690621419075 9999179096234535932128613)
        ·
          refine ⟨1874846080543975487274115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9999179096234535932128613 1874846080543975487274115)
          ·
            refine ⟨2812269120815963230911173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874846080543975487274115 2812269120815963230911173)
            ·
              refine ⟨527300460152993105795845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2812269120815963230911173 527300460152993105795845)
              ·
                refine ⟨98868836278686207336721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527300460152993105795845 98868836278686207336721)
                ·
                  rfl

theorem cell19_324922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_324922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324922 prefixEnd_324922 := by exact prefixLift 324922
  have htrace : WordTrace (prefixWord ++ tailWord_324922) baseStart_324922 baseEnd_324922 := by
    simpa [prefixWord, tailWord_324922, baseEnd_324922] using wordTrace_append hprefix tailTrace_324922
  have hstable : (prefixWord ++ tailWord_324922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324922).length < 2 ^ (prefixWord ++ tailWord_324922).sum := by decide
  have hdescent : baseEnd_324922 < baseStart_324922 := by decide
  rcases family_descends (prefixWord ++ tailWord_324922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324996 : List Nat := [2, 3, 2, 1, 1, 4, 3, 3]
def baseStart_324996 : Nat := 118140960795 + 324996 * 2 ^ 59
def prefixEnd_324996 : Nat := 4983230072969 + 3 ^ 40 * 324996 * 2
def baseEnd_324996 : Nat := 98891353356275961692075

theorem tailTrace_324996 : CollatzResearch.WordTrace tailWord_324996 prefixEnd_324996 98891353356275961692075 := by
  unfold tailWord_324996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5926788965301235871469421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7902385287068314495292561 5926788965301235871469421)
  ·
    refine ⟨2222545861987963451801033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5926788965301235871469421 2222545861987963451801033)
    ·
      refine ⟨1666909396490972588850775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2222545861987963451801033 1666909396490972588850775)
      ·
        refine ⟨2500364094736458883276163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666909396490972588850775 2500364094736458883276163)
        ·
          refine ⟨3750546142104688324914245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500364094736458883276163 3750546142104688324914245)
          ·
            refine ⟨703227401644629060921421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3750546142104688324914245 703227401644629060921421)
            ·
              refine ⟨263710275616735897845533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703227401644629060921421 263710275616735897845533)
              ·
                refine ⟨98891353356275961692075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263710275616735897845533 98891353356275961692075)
                ·
                  rfl

theorem cell19_324996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_324996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_324996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_324996 prefixEnd_324996 := by exact prefixLift 324996
  have htrace : WordTrace (prefixWord ++ tailWord_324996) baseStart_324996 baseEnd_324996 := by
    simpa [prefixWord, tailWord_324996, baseEnd_324996] using wordTrace_append hprefix tailTrace_324996
  have hstable : (prefixWord ++ tailWord_324996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324996).length < 2 ^ (prefixWord ++ tailWord_324996).sum := by decide
  have hdescent : baseEnd_324996 < baseStart_324996 := by decide
  rcases family_descends (prefixWord ++ tailWord_324996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325093 : List Nat := [1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_325093 : Nat := 118140960795 + 325093 * 2 ^ 59
def prefixEnd_325093 : Nat := 4983230072969 + 3 ^ 40 * 325093 * 2
def baseEnd_325093 : Nat := 98920868985008477536255

theorem tailTrace_325093 : CollatzResearch.WordTrace tailWord_325093 prefixEnd_325093 98920868985008477536255 := by
  unfold tailWord_325093
  simp only [CollatzResearch.WordTrace]
  refine ⟨11857115811251057309219933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7904743874167371539479955 11857115811251057309219933)
  ·
    refine ⟨4446418429219146490957475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11857115811251057309219933 4446418429219146490957475)
    ·
      refine ⟨6669627643828719736436213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446418429219146490957475 6669627643828719736436213)
      ·
        refine ⟨625277591608942475290895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6669627643828719736436213 625277591608942475290895)
        ·
          refine ⟨937916387413413712936343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625277591608942475290895 937916387413413712936343)
          ·
            refine ⟨1406874581120120569404515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937916387413413712936343 1406874581120120569404515)
            ·
              refine ⟨2110311871680180854106773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406874581120120569404515 2110311871680180854106773)
              ·
                refine ⟨98920868985008477536255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2110311871680180854106773 98920868985008477536255)
                ·
                  rfl

theorem cell19_325093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_325093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325093 prefixEnd_325093 := by exact prefixLift 325093
  have htrace : WordTrace (prefixWord ++ tailWord_325093) baseStart_325093 baseEnd_325093 := by
    simpa [prefixWord, tailWord_325093, baseEnd_325093] using wordTrace_append hprefix tailTrace_325093
  have hstable : (prefixWord ++ tailWord_325093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325093).length < 2 ^ (prefixWord ++ tailWord_325093).sum := by decide
  have hdescent : baseEnd_325093 < baseStart_325093 := by decide
  rcases family_descends (prefixWord ++ tailWord_325093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325114 : List Nat := [3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_325114 : Nat := 118140960795 + 325114 * 2 ^ 59
def prefixEnd_325114 : Nat := 4983230072969 + 3 ^ 40 * 325114 * 2
def baseEnd_325114 : Nat := 98927258966486651069531

theorem tailTrace_325114 : CollatzResearch.WordTrace tailWord_325114 prefixEnd_325114 98927258966486651069531 := by
  unfold tailWord_325114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2964470436043744473933599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7905254496116651930489597 2964470436043744473933599)
  ·
    refine ⟨4446705654065616710900399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2964470436043744473933599 4446705654065616710900399)
    ·
      refine ⟨6670058481098425066350599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446705654065616710900399 6670058481098425066350599)
      ·
        refine ⟨10005087721647637599525899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6670058481098425066350599 10005087721647637599525899)
        ·
          refine ⟨15007631582471456399288849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10005087721647637599525899 15007631582471456399288849)
          ·
            refine ⟨11255723686853592299466637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15007631582471456399288849 11255723686853592299466637)
            ·
              refine ⟨4220896382570097112299989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11255723686853592299466637 4220896382570097112299989)
              ·
                refine ⟨98927258966486651069531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4220896382570097112299989 98927258966486651069531)
                ·
                  rfl

theorem cell19_325114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_325114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325114 prefixEnd_325114 := by exact prefixLift 325114
  have htrace : WordTrace (prefixWord ++ tailWord_325114) baseStart_325114 baseEnd_325114 := by
    simpa [prefixWord, tailWord_325114, baseEnd_325114] using wordTrace_append hprefix tailTrace_325114
  have hstable : (prefixWord ++ tailWord_325114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325114).length < 2 ^ (prefixWord ++ tailWord_325114).sum := by decide
  have hdescent : baseEnd_325114 < baseStart_325114 := by decide
  rcases family_descends (prefixWord ++ tailWord_325114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325131 : List Nat := [1, 1, 1, 1, 9, 6]
def baseStart_325131 : Nat := 118140960795 + 325131 * 2 ^ 59
def prefixEnd_325131 : Nat := 4983230072969 + 3 ^ 40 * 325131 * 2
def baseEnd_325131 : Nat := 10992492423181738743523

theorem tailTrace_325131 : CollatzResearch.WordTrace tailWord_325131 prefixEnd_325131 10992492423181738743523 := by
  unfold tailWord_325131
  simp only [CollatzResearch.WordTrace]
  refine ⟨11858501785113389799103247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7905667856742259866068831 11858501785113389799103247)
  ·
    refine ⟨17787752677670084698654871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11858501785113389799103247 17787752677670084698654871)
    ·
      refine ⟨26681629016505127047982307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17787752677670084698654871 26681629016505127047982307)
      ·
        refine ⟨40022443524757690571973461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26681629016505127047982307 40022443524757690571973461)
        ·
          refine ⟨234506505027877093195157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 40022443524757690571973461 234506505027877093195157)
          ·
            refine ⟨10992492423181738743523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 234506505027877093195157 10992492423181738743523)
            ·
              rfl

theorem cell19_325131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 6].length) (baseStart_325131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325131 prefixEnd_325131 := by exact prefixLift 325131
  have htrace : WordTrace (prefixWord ++ tailWord_325131) baseStart_325131 baseEnd_325131 := by
    simpa [prefixWord, tailWord_325131, baseEnd_325131] using wordTrace_append hprefix tailTrace_325131
  have hstable : (prefixWord ++ tailWord_325131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325131).length < 2 ^ (prefixWord ++ tailWord_325131).sum := by decide
  have hdescent : baseEnd_325131 < baseStart_325131 := by decide
  rcases family_descends (prefixWord ++ tailWord_325131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325224 : List Nat := [2, 1, 4, 3, 1, 1, 4, 3]
def baseStart_325224 : Nat := 118140960795 + 325224 * 2 ^ 59
def prefixEnd_325224 : Nat := 4983230072969 + 3 ^ 40 * 325224 * 2
def baseEnd_325224 : Nat := 98960730298038988624787

theorem tailTrace_325224 : CollatzResearch.WordTrace tailWord_325224 prefixEnd_325224 98960730298038988624787 := by
  unfold tailWord_325224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5930946886888233341119363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7907929182517644454825817 5930946886888233341119363)
  ·
    refine ⟨8896420330332350011679045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5930946886888233341119363 8896420330332350011679045)
    ·
      refine ⟨1668078811937315627189821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8896420330332350011679045 1668078811937315627189821)
      ·
        refine ⟨625529554476493360196183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1668078811937315627189821 625529554476493360196183)
        ·
          refine ⟨938294331714740040294275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625529554476493360196183 938294331714740040294275)
          ·
            refine ⟨1407441497572110060441413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938294331714740040294275 1407441497572110060441413)
            ·
              refine ⟨263895280794770636332765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1407441497572110060441413 263895280794770636332765)
              ·
                refine ⟨98960730298038988624787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263895280794770636332765 98960730298038988624787)
                ·
                  rfl

theorem cell19_325224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_325224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325224 prefixEnd_325224 := by exact prefixLift 325224
  have htrace : WordTrace (prefixWord ++ tailWord_325224) baseStart_325224 baseEnd_325224 := by
    simpa [prefixWord, tailWord_325224, baseEnd_325224] using wordTrace_append hprefix tailTrace_325224
  have hstable : (prefixWord ++ tailWord_325224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325224).length < 2 ^ (prefixWord ++ tailWord_325224).sum := by decide
  have hdescent : baseEnd_325224 < baseStart_325224 := by decide
  rcases family_descends (prefixWord ++ tailWord_325224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325226 : List Nat := [3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_325226 : Nat := 118140960795 + 325226 * 2 ^ 59
def prefixEnd_325226 : Nat := 4983230072969 + 3 ^ 40 * 325226 * 2
def baseEnd_325226 : Nat := 98961338867703576580337

theorem tailTrace_325226 : CollatzResearch.WordTrace tailWord_325226 prefixEnd_325226 98961338867703576580337 := by
  unfold tailWord_325226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965491679942305255952883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7907977813179480682541021 2965491679942305255952883)
  ·
    refine ⟨4448237519913457883929325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2965491679942305255952883 4448237519913457883929325)
    ·
      refine ⟨1668089069967546706473497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4448237519913457883929325 1668089069967546706473497)
      ·
        refine ⟨1251066802475660029855123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1668089069967546706473497 1251066802475660029855123)
        ·
          refine ⟨1876600203713490044782685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251066802475660029855123 1876600203713490044782685)
          ·
            refine ⟨703725076392558766793507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1876600203713490044782685 703725076392558766793507)
            ·
              refine ⟨1055587614588838150190261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703725076392558766793507 1055587614588838150190261)
              ·
                refine ⟨98961338867703576580337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1055587614588838150190261 98961338867703576580337)
                ·
                  rfl

theorem cell19_325226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_325226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325226 prefixEnd_325226 := by exact prefixLift 325226
  have htrace : WordTrace (prefixWord ++ tailWord_325226) baseStart_325226 baseEnd_325226 := by
    simpa [prefixWord, tailWord_325226, baseEnd_325226] using wordTrace_append hprefix tailTrace_325226
  have hstable : (prefixWord ++ tailWord_325226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325226).length < 2 ^ (prefixWord ++ tailWord_325226).sum := by decide
  have hdescent : baseEnd_325226 < baseStart_325226 := by decide
  rcases family_descends (prefixWord ++ tailWord_325226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325245 : List Nat := [1, 4, 1, 1, 4, 3, 5]
def baseStart_325245 : Nat := 118140960795 + 325245 * 2 ^ 59
def prefixEnd_325245 : Nat := 4983230072969 + 3 ^ 40 * 325245 * 2
def baseEnd_325245 : Nat := 32989040093172387386021

theorem tailTrace_325245 : CollatzResearch.WordTrace tailWord_325245 prefixEnd_325245 32989040093172387386021 := by
  unfold tailWord_325245
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862659706700387268753189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7908439804466924845835459 11862659706700387268753189)
  ·
    refine ⟨2224248695006322612891223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11862659706700387268753189 2224248695006322612891223)
    ·
      refine ⟨3336373042509483919336835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224248695006322612891223 3336373042509483919336835)
      ·
        refine ⟨5004559563764225879005253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336373042509483919336835 5004559563764225879005253)
        ·
          refine ⟨938354918205792352313485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5004559563764225879005253 938354918205792352313485)
          ·
            refine ⟨351883094327172132117557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 938354918205792352313485 351883094327172132117557)
            ·
              refine ⟨32989040093172387386021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 351883094327172132117557 32989040093172387386021)
              ·
                rfl

theorem cell19_325245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_325245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325245 prefixEnd_325245 := by exact prefixLift 325245
  have htrace : WordTrace (prefixWord ++ tailWord_325245) baseStart_325245 baseEnd_325245 := by
    simpa [prefixWord, tailWord_325245, baseEnd_325245] using wordTrace_append hprefix tailTrace_325245
  have hstable : (prefixWord ++ tailWord_325245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325245).length < 2 ^ (prefixWord ++ tailWord_325245).sum := by decide
  have hdescent : baseEnd_325245 < baseStart_325245 := by decide
  rcases family_descends (prefixWord ++ tailWord_325245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325285 : List Nat := [1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_325285 : Nat := 118140960795 + 325285 * 2 ^ 59
def prefixEnd_325285 : Nat := 4983230072969 + 3 ^ 40 * 325285 * 2
def baseEnd_325285 : Nat := 98979291672808921269065

theorem tailTrace_325285 : CollatzResearch.WordTrace tailWord_325285 prefixEnd_325285 98979291672808921269065 := by
  unfold tailWord_325285
  simp only [CollatzResearch.WordTrace]
  refine ⟨11864118626555474100209309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7909412417703649400139539 11864118626555474100209309)
  ·
    refine ⟨4449044484958302787578491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11864118626555474100209309 4449044484958302787578491)
    ·
      refine ⟨6673566727437454181367737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4449044484958302787578491 6673566727437454181367737)
      ·
        refine ⟨5005175045578090636025803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6673566727437454181367737 5005175045578090636025803)
        ·
          refine ⟨7507762568367135954038705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005175045578090636025803 7507762568367135954038705)
          ·
            refine ⟨5630821926275351965529029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7507762568367135954038705 5630821926275351965529029)
            ·
              refine ⟨1055779111176628493536693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5630821926275351965529029 1055779111176628493536693)
              ·
                refine ⟨98979291672808921269065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1055779111176628493536693 98979291672808921269065)
                ·
                  rfl

theorem cell19_325285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_325285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325285 prefixEnd_325285 := by exact prefixLift 325285
  have htrace : WordTrace (prefixWord ++ tailWord_325285) baseStart_325285 baseEnd_325285 := by
    simpa [prefixWord, tailWord_325285, baseEnd_325285] using wordTrace_append hprefix tailTrace_325285
  have hstable : (prefixWord ++ tailWord_325285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325285).length < 2 ^ (prefixWord ++ tailWord_325285).sum := by decide
  have hdescent : baseEnd_325285 < baseStart_325285 := by decide
  rcases family_descends (prefixWord ++ tailWord_325285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325334 : List Nat := [5, 2, 1, 3, 1, 1, 3, 3]
def baseStart_325334 : Nat := 118140960795 + 325334 * 2 ^ 59
def prefixEnd_325334 : Nat := 4983230072969 + 3 ^ 40 * 325334 * 2
def baseEnd_325334 : Nat := 98994201629591326180043

theorem tailTrace_325334 : CollatzResearch.WordTrace tailWord_325334 prefixEnd_325334 98994201629591326180043 := by
  unfold tailWord_325334
  simp only [CollatzResearch.WordTrace]
  refine ⟨741619112711122216796441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7910603868918636979162037 741619112711122216796441)
  ·
    refine ⟨556214334533341662597331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 741619112711122216796441 556214334533341662597331)
    ·
      refine ⟨834321501800012493895997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556214334533341662597331 834321501800012493895997)
      ·
        refine ⟨312870563175004685210999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 834321501800012493895997 312870563175004685210999)
        ·
          refine ⟨469305844762507027816499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312870563175004685210999 469305844762507027816499)
          ·
            refine ⟨703958767143760541724749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469305844762507027816499 703958767143760541724749)
            ·
              refine ⟨263984537678910203146781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703958767143760541724749 263984537678910203146781)
              ·
                refine ⟨98994201629591326180043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263984537678910203146781 98994201629591326180043)
                ·
                  rfl

theorem cell19_325334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_325334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325334 prefixEnd_325334 := by exact prefixLift 325334
  have htrace : WordTrace (prefixWord ++ tailWord_325334) baseStart_325334 baseEnd_325334 := by
    simpa [prefixWord, tailWord_325334, baseEnd_325334] using wordTrace_append hprefix tailTrace_325334
  have hstable : (prefixWord ++ tailWord_325334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325334).length < 2 ^ (prefixWord ++ tailWord_325334).sum := by decide
  have hdescent : baseEnd_325334 < baseStart_325334 := by decide
  rcases family_descends (prefixWord ++ tailWord_325334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325361 : List Nat := [1, 2, 2, 2, 2, 4, 6]
def baseStart_325361 : Nat := 118140960795 + 325361 * 2 ^ 59
def prefixEnd_325361 : Nat := 4983230072969 + 3 ^ 40 * 325361 * 2
def baseEnd_325361 : Nat := 33000805773354421193323

theorem tailTrace_325361 : CollatzResearch.WordTrace tailWord_325361 prefixEnd_325361 33000805773354421193323 := by
  unfold tailWord_325361
  simp only [CollatzResearch.WordTrace]
  refine ⟨11866890574280139079975937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7911260382853426053317291 11866890574280139079975937)
  ·
    refine ⟨8900167930710104309981953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11866890574280139079975937 8900167930710104309981953)
    ·
      refine ⟨6675125948032578232486465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8900167930710104309981953 6675125948032578232486465)
      ·
        refine ⟨5006344461024433674364849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6675125948032578232486465 5006344461024433674364849)
        ·
          refine ⟨3754758345768325255773637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5006344461024433674364849 3754758345768325255773637)
          ·
            refine ⟨704017189831560985457557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3754758345768325255773637 704017189831560985457557)
            ·
              refine ⟨33000805773354421193323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 704017189831560985457557 33000805773354421193323)
              ·
                rfl

theorem cell19_325361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_325361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325361 prefixEnd_325361 := by exact prefixLift 325361
  have htrace : WordTrace (prefixWord ++ tailWord_325361) baseStart_325361 baseEnd_325361 := by
    simpa [prefixWord, tailWord_325361, baseEnd_325361] using wordTrace_append hprefix tailTrace_325361
  have hstable : (prefixWord ++ tailWord_325361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325361).length < 2 ^ (prefixWord ++ tailWord_325361).sum := by decide
  have hdescent : baseEnd_325361 < baseStart_325361 := by decide
  rcases family_descends (prefixWord ++ tailWord_325361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325378 : List Nat := [3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_325378 : Nat := 118140960795 + 325378 * 2 ^ 59
def prefixEnd_325378 : Nat := 4983230072969 + 3 ^ 40 * 325378 * 2
def baseEnd_325378 : Nat := 99007590162212261202145

theorem tailTrace_325378 : CollatzResearch.WordTrace tailWord_325378 prefixEnd_325378 99007590162212261202145 := by
  unfold tailWord_325378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966877653804637745836197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7911673743479033988896525 2966877653804637745836197)
  ·
    refine ⟨556289560088369577344287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2966877653804637745836197 556289560088369577344287)
    ·
      refine ⟨834434340132554366016431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556289560088369577344287 834434340132554366016431)
      ·
        refine ⟨1251651510198831549024647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834434340132554366016431 1251651510198831549024647)
        ·
          refine ⟨1877477265298247323536971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251651510198831549024647 1877477265298247323536971)
          ·
            refine ⟨2816215897947370985305457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877477265298247323536971 2816215897947370985305457)
            ·
              refine ⟨2112161923460528238979093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2816215897947370985305457 2112161923460528238979093)
              ·
                refine ⟨99007590162212261202145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2112161923460528238979093 99007590162212261202145)
                ·
                  rfl

theorem cell19_325378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_325378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325378 prefixEnd_325378 := by exact prefixLift 325378
  have htrace : WordTrace (prefixWord ++ tailWord_325378) baseStart_325378 baseEnd_325378 := by
    simpa [prefixWord, tailWord_325378, baseEnd_325378] using wordTrace_append hprefix tailTrace_325378
  have hstable : (prefixWord ++ tailWord_325378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325378).length < 2 ^ (prefixWord ++ tailWord_325378).sum := by decide
  have hdescent : baseEnd_325378 < baseStart_325378 := by decide
  rcases family_descends (prefixWord ++ tailWord_325378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325397 : List Nat := [1, 3, 2, 1, 2, 3, 4, 3]
def baseStart_325397 : Nat := 118140960795 + 325397 * 2 ^ 59
def prefixEnd_325397 : Nat := 4983230072969 + 3 ^ 40 * 325397 * 2
def baseEnd_325397 : Nat := 99013371574025846779871

theorem tailTrace_325397 : CollatzResearch.WordTrace tailWord_325397 prefixEnd_325397 99013371574025846779871 := by
  unfold tailWord_325397
  simp only [CollatzResearch.WordTrace]
  refine ⟨11868203602149717228286445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7912135734766478152190963 11868203602149717228286445)
  ·
    refine ⟨4450576350806143960607417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11868203602149717228286445 4450576350806143960607417)
    ·
      refine ⟨3337932263104607970455563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4450576350806143960607417 3337932263104607970455563)
      ·
        refine ⟨5006898394656911955683345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337932263104607970455563 5006898394656911955683345)
        ·
          refine ⟨3755173795992683966762509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5006898394656911955683345 3755173795992683966762509)
          ·
            refine ⟨1408190173497256487535941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3755173795992683966762509 1408190173497256487535941)
            ·
              refine ⟨264035657530735591412989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1408190173497256487535941 264035657530735591412989)
              ·
                refine ⟨99013371574025846779871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264035657530735591412989 99013371574025846779871)
                ·
                  rfl

theorem cell19_325397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_325397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325397 prefixEnd_325397 := by exact prefixLift 325397
  have htrace : WordTrace (prefixWord ++ tailWord_325397) baseStart_325397 baseEnd_325397 := by
    simpa [prefixWord, tailWord_325397, baseEnd_325397] using wordTrace_append hprefix tailTrace_325397
  have hstable : (prefixWord ++ tailWord_325397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325397).length < 2 ^ (prefixWord ++ tailWord_325397).sum := by decide
  have hdescent : baseEnd_325397 < baseStart_325397 := by decide
  rcases family_descends (prefixWord ++ tailWord_325397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325416 : List Nat := [2, 1, 5, 1, 1, 4, 5]
def baseStart_325416 : Nat := 118140960795 + 325416 * 2 ^ 59
def prefixEnd_325416 : Nat := 4983230072969 + 3 ^ 40 * 325416 * 2
def baseEnd_325416 : Nat := 33006384328613144119199

theorem tailTrace_325416 : CollatzResearch.WordTrace tailWord_325416 prefixEnd_325416 33006384328613144119199 := by
  unfold tailWord_325416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5934448294540441736614051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7912597726053922315485401 5934448294540441736614051)
  ·
    refine ⟨8901672441810662604921077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5934448294540441736614051 8901672441810662604921077)
    ·
      refine ⟨834531791419749619211351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8901672441810662604921077 834531791419749619211351)
      ·
        refine ⟨1251797687129624428817027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834531791419749619211351 1251797687129624428817027)
        ·
          refine ⟨1877696530694436643225541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251797687129624428817027 1877696530694436643225541)
          ·
            refine ⟨352068099505206870604789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1877696530694436643225541 352068099505206870604789)
            ·
              refine ⟨33006384328613144119199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352068099505206870604789 33006384328613144119199)
              ·
                rfl

theorem cell19_325416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_325416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325416 prefixEnd_325416 := by exact prefixLift 325416
  have htrace : WordTrace (prefixWord ++ tailWord_325416) baseStart_325416 baseEnd_325416 := by
    simpa [prefixWord, tailWord_325416, baseEnd_325416] using wordTrace_append hprefix tailTrace_325416
  have hstable : (prefixWord ++ tailWord_325416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325416).length < 2 ^ (prefixWord ++ tailWord_325416).sum := by decide
  have hdescent : baseEnd_325416 < baseStart_325416 := by decide
  rcases family_descends (prefixWord ++ tailWord_325416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325433 : List Nat := [1, 2, 1, 7, 1, 1, 2, 4]
def baseStart_325433 : Nat := 118140960795 + 325433 * 2 ^ 59
def prefixEnd_325433 : Nat := 4983230072969 + 3 ^ 40 * 325433 * 2
def baseEnd_325433 : Nat := 99024325827988429979773

theorem tailTrace_325433 : CollatzResearch.WordTrace tailWord_325433 prefixEnd_325433 99024325827988429979773 := by
  unfold tailWord_325433
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869516630019295376596953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7913011086679530251064635 11869516630019295376596953)
  ·
    refine ⟨8902137472514471532447715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11869516630019295376596953 8902137472514471532447715)
    ·
      refine ⟨13353206208771707298671573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8902137472514471532447715 13353206208771707298671573)
      ·
        refine ⟨312965770518086889812615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13353206208771707298671573 312965770518086889812615)
        ·
          refine ⟨469448655777130334718923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312965770518086889812615 469448655777130334718923)
          ·
            refine ⟨704172983665695502078385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469448655777130334718923 704172983665695502078385)
            ·
              refine ⟨528129737749271626558789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704172983665695502078385 528129737749271626558789)
              ·
                refine ⟨99024325827988429979773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 528129737749271626558789 99024325827988429979773)
                ·
                  rfl

theorem cell19_325433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_325433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325433 prefixEnd_325433 := by exact prefixLift 325433
  have htrace : WordTrace (prefixWord ++ tailWord_325433) baseStart_325433 baseEnd_325433 := by
    simpa [prefixWord, tailWord_325433, baseEnd_325433] using wordTrace_append hprefix tailTrace_325433
  have hstable : (prefixWord ++ tailWord_325433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325433).length < 2 ^ (prefixWord ++ tailWord_325433).sum := by decide
  have hdescent : baseEnd_325433 < baseStart_325433 := by decide
  rcases family_descends (prefixWord ++ tailWord_325433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325475 : List Nat := [1, 1, 1, 5, 4, 7]
def baseStart_325475 : Nat := 118140960795 + 325475 * 2 ^ 59
def prefixEnd_325475 : Nat := 4983230072969 + 3 ^ 40 * 325475 * 2
def baseEnd_325475 : Nat := 11004122865660530782925

theorem tailTrace_325475 : CollatzResearch.WordTrace tailWord_325475 prefixEnd_325475 11004122865660530782925 := by
  unfold tailWord_325475
  simp only [CollatzResearch.WordTrace]
  refine ⟨11871048495867136549625879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7914032330578091033083919 11871048495867136549625879)
  ·
    refine ⟨17806572743800704824438819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11871048495867136549625879 17806572743800704824438819)
    ·
      refine ⟨26709859115701057236658229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17806572743800704824438819 26709859115701057236658229)
      ·
        refine ⟨2504049292096974115936709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26709859115701057236658229 2504049292096974115936709)
        ·
          refine ⟨469509242268182646738133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2504049292096974115936709 469509242268182646738133)
          ·
            refine ⟨11004122865660530782925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 469509242268182646738133 11004122865660530782925)
            ·
              rfl

theorem cell19_325475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_325475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325475 prefixEnd_325475 := by exact prefixLift 325475
  have htrace : WordTrace (prefixWord ++ tailWord_325475) baseStart_325475 baseEnd_325475 := by
    simpa [prefixWord, tailWord_325475, baseEnd_325475] using wordTrace_append hprefix tailTrace_325475
  have hstable : (prefixWord ++ tailWord_325475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325475).length < 2 ^ (prefixWord ++ tailWord_325475).sum := by decide
  have hdescent : baseEnd_325475 < baseStart_325475 := by decide
  rcases family_descends (prefixWord ++ tailWord_325475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325526 : List Nat := [5, 3, 1, 1, 2, 1, 6]
def baseStart_325526 : Nat := 118140960795 + 325526 * 2 ^ 59
def prefixEnd_325526 : Nat := 4983230072969 + 3 ^ 40 * 325526 * 2
def baseEnd_325526 : Nat := 33017541439130589970951

theorem tailTrace_325526 : CollatzResearch.WordTrace tailWord_325526 prefixEnd_325526 33017541439130589970951 := by
  unfold tailWord_325526
  simp only [CollatzResearch.WordTrace]
  refine ⟨742056788667648266233277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7915272412454914839821621 742056788667648266233277)
  ·
    refine ⟨278271295750368099837479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 742056788667648266233277 278271295750368099837479)
    ·
      refine ⟨417406943625552149756219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278271295750368099837479 417406943625552149756219)
      ·
        refine ⟨626110415438328224634329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417406943625552149756219 626110415438328224634329)
        ·
          refine ⟨469582811578746168475747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626110415438328224634329 469582811578746168475747)
          ·
            refine ⟨704374217368119252713621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469582811578746168475747 704374217368119252713621)
            ·
              refine ⟨33017541439130589970951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 704374217368119252713621 33017541439130589970951)
              ·
                rfl

theorem cell19_325526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_325526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325526 prefixEnd_325526 := by exact prefixLift 325526
  have htrace : WordTrace (prefixWord ++ tailWord_325526) baseStart_325526 baseEnd_325526 := by
    simpa [prefixWord, tailWord_325526, baseEnd_325526] using wordTrace_append hprefix tailTrace_325526
  have hstable : (prefixWord ++ tailWord_325526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325526).length < 2 ^ (prefixWord ++ tailWord_325526).sum := by decide
  have hdescent : baseEnd_325526 < baseStart_325526 := by decide
  rcases family_descends (prefixWord ++ tailWord_325526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325564 : List Nat := [2, 2, 2, 5, 1, 2, 2, 3]
def baseStart_325564 : Nat := 118140960795 + 325564 * 2 ^ 59
def prefixEnd_325564 : Nat := 4983230072969 + 3 ^ 40 * 325564 * 2
def baseEnd_325564 : Nat := 99064187141018941068305

theorem tailTrace_325564 : CollatzResearch.WordTrace tailWord_325564 prefixEnd_325564 99064187141018941068305 := by
  unfold tailWord_325564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937147296272352374807873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7916196395029803166410497 5937147296272352374807873)
  ·
    refine ⟨4452860472204264281105905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5937147296272352374807873 4452860472204264281105905)
    ·
      refine ⟨3339645354153198210829429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4452860472204264281105905 3339645354153198210829429)
      ·
        refine ⟨313091751951862332265259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3339645354153198210829429 313091751951862332265259)
        ·
          refine ⟨469637627927793498397889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313091751951862332265259 469637627927793498397889)
          ·
            refine ⟨352228220945845123798417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469637627927793498397889 352228220945845123798417)
            ·
              refine ⟨264171165709383842848813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352228220945845123798417 264171165709383842848813)
              ·
                refine ⟨99064187141018941068305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264171165709383842848813 99064187141018941068305)
                ·
                  rfl

theorem cell19_325564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_325564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325564 prefixEnd_325564 := by exact prefixLift 325564
  have htrace : WordTrace (prefixWord ++ tailWord_325564) baseStart_325564 baseEnd_325564 := by
    simpa [prefixWord, tailWord_325564, baseEnd_325564] using wordTrace_append hprefix tailTrace_325564
  have hstable : (prefixWord ++ tailWord_325564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325564).length < 2 ^ (prefixWord ++ tailWord_325564).sum := by decide
  have hdescent : baseEnd_325564 < baseStart_325564 := by decide
  rcases family_descends (prefixWord ++ tailWord_325564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325566 : List Nat := [4, 2, 1, 1, 1, 5, 2, 3]
def baseStart_325566 : Nat := 118140960795 + 325566 * 2 ^ 59
def prefixEnd_325566 : Nat := 4983230072969 + 3 ^ 40 * 325566 * 2
def baseEnd_325566 : Nat := 99064795710683529023855

theorem tailTrace_325566 : CollatzResearch.WordTrace tailWord_325566 prefixEnd_325566 99064795710683529023855 := by
  unfold tailWord_325566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484295942317182386398569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7916245025691639394125701 1484295942317182386398569)
  ·
    refine ⟨1113221956737886789798927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1484295942317182386398569 1113221956737886789798927)
    ·
      refine ⟨1669832935106830184698391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1113221956737886789798927 1669832935106830184698391)
      ·
        refine ⟨2504749402660245277047587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669832935106830184698391 2504749402660245277047587)
        ·
          refine ⟨3757124103990367915571381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504749402660245277047587 3757124103990367915571381)
          ·
            refine ⟨352230384749096992084817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3757124103990367915571381 352230384749096992084817)
            ·
              refine ⟨264172788561822744063613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352230384749096992084817 264172788561822744063613)
              ·
                refine ⟨99064795710683529023855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264172788561822744063613 99064795710683529023855)
                ·
                  rfl

theorem cell19_325566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_325566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325566 prefixEnd_325566 := by exact prefixLift 325566
  have htrace : WordTrace (prefixWord ++ tailWord_325566) baseStart_325566 baseEnd_325566 := by
    simpa [prefixWord, tailWord_325566, baseEnd_325566] using wordTrace_append hprefix tailTrace_325566
  have hstable : (prefixWord ++ tailWord_325566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325566).length < 2 ^ (prefixWord ++ tailWord_325566).sum := by decide
  have hdescent : baseEnd_325566 < baseStart_325566 := by decide
  rcases family_descends (prefixWord ++ tailWord_325566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325589 : List Nat := [1, 3, 2, 3, 2, 1, 7]
def baseStart_325589 : Nat := 118140960795 + 325589 * 2 ^ 59
def prefixEnd_325589 : Nat := 4983230072969 + 3 ^ 40 * 325589 * 2
def baseEnd_325589 : Nat := 33023931420608763504227

theorem tailTrace_325589 : CollatzResearch.WordTrace tailWord_325589 prefixEnd_325589 33023931420608763504227 := by
  unfold tailWord_325589
  simp only [CollatzResearch.WordTrace]
  refine ⟨11875206417454134019275821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7916804278302756012850547 11875206417454134019275821)
  ·
    refine ⟨4453202406545300257228433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11875206417454134019275821 4453202406545300257228433)
    ·
      refine ⟨3339901804908975192921325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4453202406545300257228433 3339901804908975192921325)
      ·
        refine ⟨1252463176840865697345497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3339901804908975192921325 1252463176840865697345497)
        ·
          refine ⟨939347382630649273009123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252463176840865697345497 939347382630649273009123)
          ·
            refine ⟨1409021073945973909513685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939347382630649273009123 1409021073945973909513685)
            ·
              refine ⟨33023931420608763504227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1409021073945973909513685 33023931420608763504227)
              ·
                rfl

theorem cell19_325589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_325589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325589 prefixEnd_325589 := by exact prefixLift 325589
  have htrace : WordTrace (prefixWord ++ tailWord_325589) baseStart_325589 baseEnd_325589 := by
    simpa [prefixWord, tailWord_325589, baseEnd_325589] using wordTrace_append hprefix tailTrace_325589
  have hstable : (prefixWord ++ tailWord_325589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325589).length < 2 ^ (prefixWord ++ tailWord_325589).sum := by decide
  have hdescent : baseEnd_325589 < baseStart_325589 := by decide
  rcases family_descends (prefixWord ++ tailWord_325589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325638 : List Nat := [6, 2, 1, 2, 2, 6]
def baseStart_325638 : Nat := 118140960795 + 325638 * 2 ^ 59
def prefixEnd_325638 : Nat := 4983230072969 + 3 ^ 40 * 325638 * 2
def baseEnd_325638 : Nat := 11009633802067632824851

theorem tailTrace_325638 : CollatzResearch.WordTrace tailWord_325638 prefixEnd_325638 11009633802067632824851 := by
  unfold tailWord_325638
  simp only [CollatzResearch.WordTrace]
  refine ⟨371156049821144230869049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7917995729517743591873045 371156049821144230869049)
  ·
    refine ⟨278367037365858173151787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 371156049821144230869049 278367037365858173151787)
    ·
      refine ⟨417550556048787259727681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278367037365858173151787 417550556048787259727681)
      ·
        refine ⟨313162917036590444795761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417550556048787259727681 313162917036590444795761)
        ·
          refine ⟨234872187777442833596821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313162917036590444795761 234872187777442833596821)
          ·
            refine ⟨11009633802067632824851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 234872187777442833596821 11009633802067632824851)
            ·
              rfl

theorem cell19_325638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 6].length) (baseStart_325638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325638 prefixEnd_325638 := by exact prefixLift 325638
  have htrace : WordTrace (prefixWord ++ tailWord_325638) baseStart_325638 baseEnd_325638 := by
    simpa [prefixWord, tailWord_325638, baseEnd_325638] using wordTrace_append hprefix tailTrace_325638
  have hstable : (prefixWord ++ tailWord_325638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325638).length < 2 ^ (prefixWord ++ tailWord_325638).sum := by decide
  have hdescent : baseEnd_325638 < baseStart_325638 := by decide
  rcases family_descends (prefixWord ++ tailWord_325638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325682 : List Nat := [3, 2, 1, 1, 2, 4, 3, 3]
def baseStart_325682 : Nat := 118140960795 + 325682 * 2 ^ 59
def prefixEnd_325682 : Nat := 4983230072969 + 3 ^ 40 * 325682 * 2
def baseEnd_325682 : Nat := 99100092751229630445761

theorem tailTrace_325682 : CollatzResearch.WordTrace tailWord_325682 prefixEnd_325682 99100092751229630445761 := by
  unfold tailWord_325682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969649601529302725602825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7919065604078140601607533 2969649601529302725602825)
  ·
    refine ⟨2227237201146977044202119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2969649601529302725602825 2227237201146977044202119)
    ·
      refine ⟨3340855801720465566303179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227237201146977044202119 3340855801720465566303179)
      ·
        refine ⟨5011283702580698349454769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340855801720465566303179 5011283702580698349454769)
        ·
          refine ⟨3758462776935523762091077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5011283702580698349454769 3758462776935523762091077)
          ·
            refine ⟨704711770675410705392077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3758462776935523762091077 704711770675410705392077)
            ·
              refine ⟨264266914003279014522029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 704711770675410705392077 264266914003279014522029)
              ·
                refine ⟨99100092751229630445761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264266914003279014522029 99100092751229630445761)
                ·
                  rfl

theorem cell19_325682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_325682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325682 prefixEnd_325682 := by exact prefixLift 325682
  have htrace : WordTrace (prefixWord ++ tailWord_325682) baseStart_325682 baseEnd_325682 := by
    simpa [prefixWord, tailWord_325682, baseEnd_325682] using wordTrace_append hprefix tailTrace_325682
  have hstable : (prefixWord ++ tailWord_325682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325682).length < 2 ^ (prefixWord ++ tailWord_325682).sum := by decide
  have hdescent : baseEnd_325682 < baseStart_325682 := by decide
  rcases family_descends (prefixWord ++ tailWord_325682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325705 : List Nat := [1, 2, 1, 1, 2, 2, 10]
def baseStart_325705 : Nat := 118140960795 + 325705 * 2 ^ 59
def prefixEnd_325705 : Nat := 4983230072969 + 3 ^ 40 * 325705 * 2
def baseEnd_325705 : Nat := 33035697100790797311529

theorem tailTrace_325705 : CollatzResearch.WordTrace tailWord_325705 prefixEnd_325705 33035697100790797311529 := by
  unfold tailWord_325705
  simp only [CollatzResearch.WordTrace]
  refine ⟨11879437285033885830498569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7919624856689257220332379 11879437285033885830498569)
  ·
    refine ⟨8909577963775414372873927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11879437285033885830498569 8909577963775414372873927)
    ·
      refine ⟨13364366945663121559310891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8909577963775414372873927 13364366945663121559310891)
      ·
        refine ⟨20046550418494682338966337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13364366945663121559310891 20046550418494682338966337)
        ·
          refine ⟨15034912813871011754224753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20046550418494682338966337 15034912813871011754224753)
          ·
            refine ⟨11276184610403258815668565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15034912813871011754224753 11276184610403258815668565)
            ·
              refine ⟨33035697100790797311529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11276184610403258815668565 33035697100790797311529)
              ·
                rfl

theorem cell19_325705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_325705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325705 prefixEnd_325705 := by exact prefixLift 325705
  have htrace : WordTrace (prefixWord ++ tailWord_325705) baseStart_325705 baseEnd_325705 := by
    simpa [prefixWord, tailWord_325705, baseEnd_325705] using wordTrace_append hprefix tailTrace_325705
  have hstable : (prefixWord ++ tailWord_325705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325705).length < 2 ^ (prefixWord ++ tailWord_325705).sum := by decide
  have hdescent : baseEnd_325705 < baseStart_325705 := by decide
  rcases family_descends (prefixWord ++ tailWord_325705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325741 : List Nat := [1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_325741 : Nat := 118140960795 + 325741 * 2 ^ 59
def prefixEnd_325741 : Nat := 4983230072969 + 3 ^ 40 * 325741 * 2
def baseEnd_325741 : Nat := 99118045556334975134489

theorem tailTrace_325741 : CollatzResearch.WordTrace tailWord_325741 prefixEnd_325741 99118045556334975134489 := by
  unfold tailWord_325741
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880750312903463978809077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7920500208602309319206051 11880750312903463978809077)
  ·
    refine ⟨1113820341834699748013351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11880750312903463978809077 1113820341834699748013351)
    ·
      refine ⟨1670730512752049622020027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1113820341834699748013351 1670730512752049622020027)
      ·
        refine ⟨2506095769128074433030041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670730512752049622020027 2506095769128074433030041)
        ·
          refine ⟨1879571826846055824772531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2506095769128074433030041 1879571826846055824772531)
          ·
            refine ⟨2819357740269083737158797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879571826846055824772531 2819357740269083737158797)
            ·
              refine ⟨1057259152600906401434549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2819357740269083737158797 1057259152600906401434549)
              ·
                refine ⟨99118045556334975134489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1057259152600906401434549 99118045556334975134489)
                ·
                  rfl

theorem cell19_325741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_325741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325741 prefixEnd_325741 := by exact prefixLift 325741
  have htrace : WordTrace (prefixWord ++ tailWord_325741) baseStart_325741 baseEnd_325741 := by
    simpa [prefixWord, tailWord_325741, baseEnd_325741] using wordTrace_append hprefix tailTrace_325741
  have hstable : (prefixWord ++ tailWord_325741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325741).length < 2 ^ (prefixWord ++ tailWord_325741).sum := by decide
  have hdescent : baseEnd_325741 < baseStart_325741 := by decide
  rcases family_descends (prefixWord ++ tailWord_325741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325874 : List Nat := [3, 2, 1, 3, 2, 2, 6]
def baseStart_325874 : Nat := 118140960795 + 325874 * 2 ^ 59
def prefixEnd_325874 : Nat := 4983230072969 + 3 ^ 40 * 325874 * 2
def baseEnd_325874 : Nat := 33052838479676691392857

theorem tailTrace_325874 : CollatzResearch.WordTrace tailWord_325874 prefixEnd_325874 33052838479676691392857 := by
  unfold tailWord_325874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971400305355406923350169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7923734147614418462267117 2971400305355406923350169)
  ·
    refine ⟨2228550229016555192512627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2971400305355406923350169 2228550229016555192512627)
    ·
      refine ⟨3342825343524832788768941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228550229016555192512627 3342825343524832788768941)
      ·
        refine ⟨1253559503821812295788353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3342825343524832788768941 1253559503821812295788353)
        ·
          refine ⟨940169627866359221841265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253559503821812295788353 940169627866359221841265)
          ·
            refine ⟨705127220899769416380949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940169627866359221841265 705127220899769416380949)
            ·
              refine ⟨33052838479676691392857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 705127220899769416380949 33052838479676691392857)
              ·
                rfl

theorem cell19_325874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_325874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325874 prefixEnd_325874 := by exact prefixLift 325874
  have htrace : WordTrace (prefixWord ++ tailWord_325874) baseStart_325874 baseEnd_325874 := by
    simpa [prefixWord, tailWord_325874, baseEnd_325874] using wordTrace_append hprefix tailTrace_325874
  have hstable : (prefixWord ++ tailWord_325874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325874).length < 2 ^ (prefixWord ++ tailWord_325874).sum := by decide
  have hdescent : baseEnd_325874 < baseStart_325874 := by decide
  rcases family_descends (prefixWord ++ tailWord_325874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325950 : List Nat := [4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_325950 : Nat := 118140960795 + 325950 * 2 ^ 59
def prefixEnd_325950 : Nat := 4983230072969 + 3 ^ 40 * 325950 * 2
def baseEnd_325950 : Nat := 99181641086284416489475

theorem tailTrace_325950 : CollatzResearch.WordTrace tailWord_325950 prefixEnd_325950 99181641086284416489475 := by
  unfold tailWord_325950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486046646143286584145913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7925582112764195115444869 1486046646143286584145913)
  ·
    refine ⟨1114534984607464938109435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1486046646143286584145913 1114534984607464938109435)
    ·
      refine ⟨1671802476911197407164153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114534984607464938109435 1671802476911197407164153)
      ·
        refine ⟨1253851857683398055373115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1671802476911197407164153 1253851857683398055373115)
        ·
          refine ⟨1880777786525097083059673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253851857683398055373115 1880777786525097083059673)
          ·
            refine ⟨1410583339893822812294755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880777786525097083059673 1410583339893822812294755)
            ·
              refine ⟨2115875009840734218442133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410583339893822812294755 2115875009840734218442133)
              ·
                refine ⟨99181641086284416489475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2115875009840734218442133 99181641086284416489475)
                ·
                  rfl

theorem cell19_325950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_325950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325950 prefixEnd_325950 := by exact prefixLift 325950
  have htrace : WordTrace (prefixWord ++ tailWord_325950) baseStart_325950 baseEnd_325950 := by
    simpa [prefixWord, tailWord_325950, baseEnd_325950] using wordTrace_append hprefix tailTrace_325950
  have hstable : (prefixWord ++ tailWord_325950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325950).length < 2 ^ (prefixWord ++ tailWord_325950).sum := by decide
  have hdescent : baseEnd_325950 < baseStart_325950 := by decide
  rcases family_descends (prefixWord ++ tailWord_325950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325982 : List Nat := [4, 4, 2, 1, 1, 7]
def baseStart_325982 : Nat := 118140960795 + 325982 * 2 ^ 59
def prefixEnd_325982 : Nat := 4983230072969 + 3 ^ 40 * 325982 * 2
def baseEnd_325982 : Nat := 11021264244546424864253

theorem tailTrace_325982 : CollatzResearch.WordTrace tailWord_325982 prefixEnd_325982 11021264244546424864253 := by
  unfold tailWord_325982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486192538128795267291525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7926360203353574758888133 1486192538128795267291525)
  ·
    refine ⟨278661100899149112617161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1486192538128795267291525 278661100899149112617161)
    ·
      refine ⟨208995825674361834462871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278661100899149112617161 208995825674361834462871)
      ·
        refine ⟨313493738511542751694307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208995825674361834462871 313493738511542751694307)
        ·
          refine ⟨470240607767314127541461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313493738511542751694307 470240607767314127541461)
          ·
            refine ⟨11021264244546424864253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 470240607767314127541461 11021264244546424864253)
            ·
              rfl

theorem cell19_325982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 7].length) (baseStart_325982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_325982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_325982 prefixEnd_325982 := by exact prefixLift 325982
  have htrace : WordTrace (prefixWord ++ tailWord_325982) baseStart_325982 baseEnd_325982 := by
    simpa [prefixWord, tailWord_325982, baseEnd_325982] using wordTrace_append hprefix tailTrace_325982
  have hstable : (prefixWord ++ tailWord_325982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325982).length < 2 ^ (prefixWord ++ tailWord_325982).sum := by decide
  have hdescent : baseEnd_325982 < baseStart_325982 := by decide
  rcases family_descends (prefixWord ++ tailWord_325982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326005 : List Nat := [1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_326005 : Nat := 118140960795 + 326005 * 2 ^ 59
def prefixEnd_326005 : Nat := 4983230072969 + 3 ^ 40 * 326005 * 2
def baseEnd_326005 : Nat := 99198376752060585267103

theorem tailTrace_326005 : CollatzResearch.WordTrace tailWord_326005 prefixEnd_326005 99198376752060585267103 := by
  unfold tailWord_326005
  simp only [CollatzResearch.WordTrace]
  refine ⟨11890379183947037066419469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7926919455964691377612979 11890379183947037066419469)
  ·
    refine ⟨4458892193980138899907301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11890379183947037066419469 4458892193980138899907301)
    ·
      refine ⟨836042286371276043732619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4458892193980138899907301 836042286371276043732619)
      ·
        refine ⟨1254063429556914065598929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836042286371276043732619 1254063429556914065598929)
        ·
          refine ⟨940547572167685549199197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254063429556914065598929 940547572167685549199197)
          ·
            refine ⟨352705339562882080949699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 940547572167685549199197 352705339562882080949699)
            ·
              refine ⟨529058009344323121424549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352705339562882080949699 529058009344323121424549)
              ·
                refine ⟨99198376752060585267103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529058009344323121424549 99198376752060585267103)
                ·
                  rfl

theorem cell19_326005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_326005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326005 prefixEnd_326005 := by exact prefixLift 326005
  have htrace : WordTrace (prefixWord ++ tailWord_326005) baseStart_326005 baseEnd_326005 := by
    simpa [prefixWord, tailWord_326005, baseEnd_326005] using wordTrace_append hprefix tailTrace_326005
  have hstable : (prefixWord ++ tailWord_326005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326005).length < 2 ^ (prefixWord ++ tailWord_326005).sum := by decide
  have hdescent : baseEnd_326005 < baseStart_326005 := by decide
  rcases family_descends (prefixWord ++ tailWord_326005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326045 : List Nat := [1, 4, 2, 1, 4, 1, 6]
def baseStart_326045 : Nat := 118140960795 + 326045 * 2 ^ 59
def prefixEnd_326045 : Nat := 4983230072969 + 3 ^ 40 * 326045 * 2
def baseEnd_326045 : Nat := 33070182715117448126035

theorem tailTrace_326045 : CollatzResearch.WordTrace tailWord_326045 prefixEnd_326045 33070182715117448126035 := by
  unfold tailWord_326045
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891838103802123897875589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7927892069201415931917059 11891838103802123897875589)
  ·
    refine ⟨2229719644462898230851673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11891838103802123897875589 2229719644462898230851673)
    ·
      refine ⟨1672289733347173673138755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2229719644462898230851673 1672289733347173673138755)
      ·
        refine ⟨2508434600020760509708133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672289733347173673138755 2508434600020760509708133)
        ·
          refine ⟨470331487503892595570275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2508434600020760509708133 470331487503892595570275)
          ·
            refine ⟨705497231255838893355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470331487503892595570275 705497231255838893355413)
            ·
              refine ⟨33070182715117448126035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 705497231255838893355413 33070182715117448126035)
              ·
                rfl

theorem cell19_326045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_326045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326045 prefixEnd_326045 := by exact prefixLift 326045
  have htrace : WordTrace (prefixWord ++ tailWord_326045) baseStart_326045 baseEnd_326045 := by
    simpa [prefixWord, tailWord_326045, baseEnd_326045] using wordTrace_append hprefix tailTrace_326045
  have hstable : (prefixWord ++ tailWord_326045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326045).length < 2 ^ (prefixWord ++ tailWord_326045).sum := by decide
  have hdescent : baseEnd_326045 < baseStart_326045 := by decide
  rcases family_descends (prefixWord ++ tailWord_326045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326047 : List Nat := [1, 1, 2, 5, 1, 1, 8]
def baseStart_326047 : Nat := 118140960795 + 326047 * 2 ^ 59
def prefixEnd_326047 : Nat := 4983230072969 + 3 ^ 40 * 326047 * 2
def baseEnd_326047 : Nat := 33070385571672310777885

theorem tailTrace_326047 : CollatzResearch.WordTrace tailWord_326047 prefixEnd_326047 33070385571672310777885 := by
  unfold tailWord_326047
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891911049794878239448395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7927940699863252159632263 11891911049794878239448395)
  ·
    refine ⟨17837866574692317359172593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11891911049794878239448395 17837866574692317359172593)
    ·
      refine ⟨13378399931019238019379445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17837866574692317359172593 13378399931019238019379445)
      ·
        refine ⟨1254224993533053564316823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13378399931019238019379445 1254224993533053564316823)
        ·
          refine ⟨1881337490299580346475235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254224993533053564316823 1881337490299580346475235)
          ·
            refine ⟨2822006235449370519712853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881337490299580346475235 2822006235449370519712853)
            ·
              refine ⟨33070385571672310777885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2822006235449370519712853 33070385571672310777885)
              ·
                rfl

theorem cell19_326047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_326047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326047 prefixEnd_326047 := by exact prefixLift 326047
  have htrace : WordTrace (prefixWord ++ tailWord_326047) baseStart_326047 baseEnd_326047 := by
    simpa [prefixWord, tailWord_326047, baseEnd_326047] using wordTrace_append hprefix tailTrace_326047
  have hstable : (prefixWord ++ tailWord_326047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326047).length < 2 ^ (prefixWord ++ tailWord_326047).sum := by decide
  have hdescent : baseEnd_326047 < baseStart_326047 := by decide
  rcases family_descends (prefixWord ++ tailWord_326047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326066 : List Nat := [3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_326066 : Nat := 118140960795 + 326066 * 2 ^ 59
def prefixEnd_326066 : Nat := 4983230072969 + 3 ^ 40 * 326066 * 2
def baseEnd_326066 : Nat := 99216938126830517911381

theorem tailTrace_326066 : CollatzResearch.WordTrace tailWord_326066 prefixEnd_326066 99216938126830517911381 := by
  unfold tailWord_326066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973151009181511121097513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7928402691150696322926701 2973151009181511121097513)
  ·
    refine ⟨2229863256886133340823135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2973151009181511121097513 2229863256886133340823135)
    ·
      refine ⟨3344794885329200011234703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229863256886133340823135 3344794885329200011234703)
      ·
        refine ⟨5017192327993800016852055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3344794885329200011234703 5017192327993800016852055)
        ·
          refine ⟨7525788491990700025278083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017192327993800016852055 7525788491990700025278083)
          ·
            refine ⟨11288682737986050037917125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7525788491990700025278083 11288682737986050037917125)
            ·
              refine ⟨2116628013372384382109461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11288682737986050037917125 2116628013372384382109461)
              ·
                refine ⟨99216938126830517911381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2116628013372384382109461 99216938126830517911381)
                ·
                  rfl

theorem cell19_326066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_326066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326066 prefixEnd_326066 := by exact prefixLift 326066
  have htrace : WordTrace (prefixWord ++ tailWord_326066) baseStart_326066 baseEnd_326066 := by
    simpa [prefixWord, tailWord_326066, baseEnd_326066] using wordTrace_append hprefix tailTrace_326066
  have hstable : (prefixWord ++ tailWord_326066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326066).length < 2 ^ (prefixWord ++ tailWord_326066).sum := by decide
  have hdescent : baseEnd_326066 < baseStart_326066 := by decide
  rcases family_descends (prefixWord ++ tailWord_326066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326098 : List Nat := [3, 2, 2, 4, 2, 1, 5]
def baseStart_326098 : Nat := 118140960795 + 326098 * 2 ^ 59
def prefixEnd_326098 : Nat := 4983230072969 + 3 ^ 40 * 326098 * 2
def baseEnd_326098 : Nat := 33075558413821308400061

theorem tailTrace_326098 : CollatzResearch.WordTrace tailWord_326098 prefixEnd_326098 33075558413821308400061 := by
  unfold tailWord_326098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973442793152528487388737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7929180781740075966369965 2973442793152528487388737)
  ·
    refine ⟨2230082094864396365541553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2973442793152528487388737 2230082094864396365541553)
    ·
      refine ⟨1672561571148297274156165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2230082094864396365541553 1672561571148297274156165)
      ·
        refine ⟨313605294590305738904281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1672561571148297274156165 313605294590305738904281)
        ·
          refine ⟨235203970942729304178211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313605294590305738904281 235203970942729304178211)
          ·
            refine ⟨352805956414093956267317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235203970942729304178211 352805956414093956267317)
            ·
              refine ⟨33075558413821308400061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352805956414093956267317 33075558413821308400061)
              ·
                rfl

theorem cell19_326098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_326098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326098 prefixEnd_326098 := by exact prefixLift 326098
  have htrace : WordTrace (prefixWord ++ tailWord_326098) baseStart_326098 baseEnd_326098 := by
    simpa [prefixWord, tailWord_326098, baseEnd_326098] using wordTrace_append hprefix tailTrace_326098
  have hstable : (prefixWord ++ tailWord_326098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326098).length < 2 ^ (prefixWord ++ tailWord_326098).sum := by decide
  have hdescent : baseEnd_326098 < baseStart_326098 := by decide
  rcases family_descends (prefixWord ++ tailWord_326098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326123 : List Nat := [1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_326123 : Nat := 118140960795 + 326123 * 2 ^ 59
def prefixEnd_326123 : Nat := 4983230072969 + 3 ^ 40 * 326123 * 2
def baseEnd_326123 : Nat := 99234282362271274644559

theorem tailTrace_326123 : CollatzResearch.WordTrace tailWord_326123 prefixEnd_326123 99234282362271274644559 := by
  unfold tailWord_326123
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894682997519543219215023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7929788665013028812810015 11894682997519543219215023)
  ·
    refine ⟨17842024496279314828822535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11894682997519543219215023 17842024496279314828822535)
    ·
      refine ⟨26763036744418972243233803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17842024496279314828822535 26763036744418972243233803)
      ·
        refine ⟨40144555116628458364850705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26763036744418972243233803 40144555116628458364850705)
        ·
          refine ⟨30108416337471343773638029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40144555116628458364850705 30108416337471343773638029)
          ·
            refine ⟨11290656126551753915114261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30108416337471343773638029 11290656126551753915114261)
            ·
              refine ⟨529249505932113464770981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11290656126551753915114261 529249505932113464770981)
              ·
                refine ⟨99234282362271274644559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529249505932113464770981 99234282362271274644559)
                ·
                  rfl

theorem cell19_326123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_326123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326123 prefixEnd_326123 := by exact prefixLift 326123
  have htrace : WordTrace (prefixWord ++ tailWord_326123) baseStart_326123 baseEnd_326123 := by
    simpa [prefixWord, tailWord_326123, baseEnd_326123] using wordTrace_append hprefix tailTrace_326123
  have hstable : (prefixWord ++ tailWord_326123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326123).length < 2 ^ (prefixWord ++ tailWord_326123).sum := by decide
  have hdescent : baseEnd_326123 < baseStart_326123 := by decide
  rcases family_descends (prefixWord ++ tailWord_326123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326157 : List Nat := [1, 7, 1, 1, 1, 8]
def baseStart_326157 : Nat := 118140960795 + 326157 * 2 ^ 59
def prefixEnd_326157 : Nat := 4983230072969 + 3 ^ 40 * 326157 * 2
def baseEnd_326157 : Nat := 11027180894063252209879

theorem tailTrace_326157 : CollatzResearch.WordTrace tailWord_326157 prefixEnd_326157 11027180894063252209879 := by
  unfold tailWord_326157
  simp only [CollatzResearch.WordTrace]
  refine ⟨11895923079396367025952725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7930615386264244683968483 11895923079396367025952725)
  ·
    refine ⟨278810697173352352170767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11895923079396367025952725 278810697173352352170767)
    ·
      refine ⟨418216045760028528256151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278810697173352352170767 418216045760028528256151)
      ·
        refine ⟨627324068640042792384227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418216045760028528256151 627324068640042792384227)
        ·
          refine ⟨940986102960064188576341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627324068640042792384227 940986102960064188576341)
          ·
            refine ⟨11027180894063252209879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 940986102960064188576341 11027180894063252209879)
            ·
              rfl

theorem cell19_326157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 8].length) (baseStart_326157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326157 prefixEnd_326157 := by exact prefixLift 326157
  have htrace : WordTrace (prefixWord ++ tailWord_326157) baseStart_326157 baseEnd_326157 := by
    simpa [prefixWord, tailWord_326157, baseEnd_326157] using wordTrace_append hprefix tailTrace_326157
  have hstable : (prefixWord ++ tailWord_326157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326157).length < 2 ^ (prefixWord ++ tailWord_326157).sum := by decide
  have hdescent : baseEnd_326157 < baseStart_326157 := by decide
  rcases family_descends (prefixWord ++ tailWord_326157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326176 : List Nat := [2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_326176 : Nat := 118140960795 + 326176 * 2 ^ 59
def prefixEnd_326176 : Nat := 4983230072969 + 3 ^ 40 * 326176 * 2
def baseEnd_326176 : Nat := 99250409458382855466637

theorem tailTrace_326176 : CollatzResearch.WordTrace tailWord_326176 prefixEnd_326176 99250409458382855466637 := by
  unfold tailWord_326176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5948308033163766635447191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7931077377551688847262921 5948308033163766635447191)
  ·
    refine ⟨8922462049745649953170787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5948308033163766635447191 8922462049745649953170787)
    ·
      refine ⟨13383693074618474929756181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8922462049745649953170787 13383693074618474929756181)
      ·
        refine ⟨627360612872741012332321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13383693074618474929756181 627360612872741012332321)
        ·
          refine ⟨470520459654555759249241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627360612872741012332321 470520459654555759249241)
          ·
            refine ⟨352890344740916819436931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470520459654555759249241 352890344740916819436931)
            ·
              refine ⟨529335517111375229155397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352890344740916819436931 529335517111375229155397)
              ·
                refine ⟨99250409458382855466637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529335517111375229155397 99250409458382855466637)
                ·
                  rfl

theorem cell19_326176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_326176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326176 prefixEnd_326176 := by exact prefixLift 326176
  have htrace : WordTrace (prefixWord ++ tailWord_326176) baseStart_326176 baseEnd_326176 := by
    simpa [prefixWord, tailWord_326176, baseEnd_326176] using wordTrace_append hprefix tailTrace_326176
  have hstable : (prefixWord ++ tailWord_326176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326176).length < 2 ^ (prefixWord ++ tailWord_326176).sum := by decide
  have hdescent : baseEnd_326176 < baseStart_326176 := by decide
  rcases family_descends (prefixWord ++ tailWord_326176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326197 : List Nat := [1, 3, 3, 1, 1, 2, 5, 3]
def baseStart_326197 : Nat := 118140960795 + 326197 * 2 ^ 59
def prefixEnd_326197 : Nat := 4983230072969 + 3 ^ 40 * 326197 * 2
def baseEnd_326197 : Nat := 99256799439861028999913

theorem tailTrace_326197 : CollatzResearch.WordTrace tailWord_326197 prefixEnd_326197 99256799439861028999913 := by
  unfold tailWord_326197
  simp only [CollatzResearch.WordTrace]
  refine ⟨11897381999251453857408845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7931587999500969238272563 11897381999251453857408845)
  ·
    refine ⟨4461518249719295196528317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11897381999251453857408845 4461518249719295196528317)
    ·
      refine ⟨1673069343644735698698119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4461518249719295196528317 1673069343644735698698119)
      ·
        refine ⟨2509604015467103548047179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673069343644735698698119 2509604015467103548047179)
        ·
          refine ⟨3764406023200655322070769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509604015467103548047179 3764406023200655322070769)
          ·
            refine ⟨2823304517400491491553077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3764406023200655322070769 2823304517400491491553077)
            ·
              refine ⟨264684798506296077333101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2823304517400491491553077 264684798506296077333101)
              ·
                refine ⟨99256799439861028999913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264684798506296077333101 99256799439861028999913)
                ·
                  rfl

theorem cell19_326197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_326197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326197 prefixEnd_326197 := by exact prefixLift 326197
  have htrace : WordTrace (prefixWord ++ tailWord_326197) baseStart_326197 baseEnd_326197 := by
    simpa [prefixWord, tailWord_326197, baseEnd_326197] using wordTrace_append hprefix tailTrace_326197
  have hstable : (prefixWord ++ tailWord_326197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326197).length < 2 ^ (prefixWord ++ tailWord_326197).sum := by decide
  have hdescent : baseEnd_326197 < baseStart_326197 := by decide
  rcases family_descends (prefixWord ++ tailWord_326197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326212 : List Nat := [2, 3, 5, 1, 1, 1, 6]
def baseStart_326212 : Nat := 118140960795 + 326212 * 2 ^ 59
def prefixEnd_326212 : Nat := 4983230072969 + 3 ^ 40 * 326212 * 2
def baseEnd_326212 : Nat := 33087121237448479555513

theorem tailTrace_326212 : CollatzResearch.WordTrace tailWord_326212 prefixEnd_326212 33087121237448479555513 := by
  unfold tailWord_326212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5948964547098555709602445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7931952729464740946136593 5948964547098555709602445)
  ·
    refine ⟨2230861705161958391100917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5948964547098555709602445 2230861705161958391100917)
    ·
      refine ⟨209143284858933599165711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2230861705161958391100917 209143284858933599165711)
      ·
        refine ⟨313714927288400398748567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209143284858933599165711 313714927288400398748567)
        ·
          refine ⟨470572390932600598122851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313714927288400398748567 470572390932600598122851)
          ·
            refine ⟨705858586398900897184277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470572390932600598122851 705858586398900897184277)
            ·
              refine ⟨33087121237448479555513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 705858586398900897184277 33087121237448479555513)
              ·
                rfl

theorem cell19_326212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_326212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326212 prefixEnd_326212 := by exact prefixLift 326212
  have htrace : WordTrace (prefixWord ++ tailWord_326212) baseStart_326212 baseEnd_326212 := by
    simpa [prefixWord, tailWord_326212, baseEnd_326212] using wordTrace_append hprefix tailTrace_326212
  have hstable : (prefixWord ++ tailWord_326212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326212).length < 2 ^ (prefixWord ++ tailWord_326212).sum := by decide
  have hdescent : baseEnd_326212 < baseStart_326212 := by decide
  rcases family_descends (prefixWord ++ tailWord_326212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326214 : List Nat := [6, 1, 1, 1, 2, 2, 6]
def baseStart_326214 : Nat := 118140960795 + 326214 * 2 ^ 59
def prefixEnd_326214 : Nat := 4983230072969 + 3 ^ 40 * 326214 * 2
def baseEnd_326214 : Nat := 33087324094003342207363

theorem tailTrace_326214 : CollatzResearch.WordTrace tailWord_326214 prefixEnd_326214 33087324094003342207363 := by
  unfold tailWord_326214
  simp only [CollatzResearch.WordTrace]
  refine ⟨371812563755933305024303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7932001360126577173851797 371812563755933305024303)
  ·
    refine ⟨557718845633899957536455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371812563755933305024303 557718845633899957536455)
    ·
      refine ⟨836578268450849936304683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557718845633899957536455 836578268450849936304683)
      ·
        refine ⟨1254867402676274904457025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836578268450849936304683 1254867402676274904457025)
        ·
          refine ⟨941150552007206178342769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254867402676274904457025 941150552007206178342769)
          ·
            refine ⟨705862914005404633757077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941150552007206178342769 705862914005404633757077)
            ·
              refine ⟨33087324094003342207363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 705862914005404633757077 33087324094003342207363)
              ·
                rfl

theorem cell19_326214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_326214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326214 prefixEnd_326214 := by exact prefixLift 326214
  have htrace : WordTrace (prefixWord ++ tailWord_326214) baseStart_326214 baseEnd_326214 := by
    simpa [prefixWord, tailWord_326214, baseEnd_326214] using wordTrace_append hprefix tailTrace_326214
  have hstable : (prefixWord ++ tailWord_326214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326214).length < 2 ^ (prefixWord ++ tailWord_326214).sum := by decide
  have hdescent : baseEnd_326214 < baseStart_326214 := by decide
  rcases family_descends (prefixWord ++ tailWord_326214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326218 : List Nat := [3, 1, 2, 1, 1, 5, 6]
def baseStart_326218 : Nat := 118140960795 + 326218 * 2 ^ 59
def prefixEnd_326218 : Nat := 4983230072969 + 3 ^ 40 * 326218 * 2
def baseEnd_326218 : Nat := 33087729807113067511063

theorem tailTrace_326218 : CollatzResearch.WordTrace tailWord_326218 prefixEnd_326218 33087729807113067511063 := by
  unfold tailWord_326218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974536983043843610980827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7932098621450249629282205 2974536983043843610980827)
  ·
    refine ⟨4461805474565765416471241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2974536983043843610980827 4461805474565765416471241)
    ·
      refine ⟨3346354105924324062353431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4461805474565765416471241 3346354105924324062353431)
      ·
        refine ⟨5019531158886486093530147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3346354105924324062353431 5019531158886486093530147)
        ·
          refine ⟨7529296738329729140295221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5019531158886486093530147 7529296738329729140295221)
          ·
            refine ⟨705871569218412106902677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7529296738329729140295221 705871569218412106902677)
            ·
              refine ⟨33087729807113067511063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 705871569218412106902677 33087729807113067511063)
              ·
                rfl

theorem cell19_326218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_326218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326218 prefixEnd_326218 := by exact prefixLift 326218
  have htrace : WordTrace (prefixWord ++ tailWord_326218) baseStart_326218 baseEnd_326218 := by
    simpa [prefixWord, tailWord_326218, baseEnd_326218] using wordTrace_append hprefix tailTrace_326218
  have hstable : (prefixWord ++ tailWord_326218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326218).length < 2 ^ (prefixWord ++ tailWord_326218).sum := by decide
  have hdescent : baseEnd_326218 < baseStart_326218 := by decide
  rcases family_descends (prefixWord ++ tailWord_326218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326254 : List Nat := [4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_326254 : Nat := 118140960795 + 326254 * 2 ^ 59
def prefixEnd_326254 : Nat := 4983230072969 + 3 ^ 40 * 326254 * 2
def baseEnd_326254 : Nat := 99274143675301785733091

theorem tailTrace_326254 : CollatzResearch.WordTrace tailWord_326254 prefixEnd_326254 99274143675301785733091 := by
  unfold tailWord_326254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487432620005619074029227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7932973973363301728155877 1487432620005619074029227)
  ·
    refine ⟨2231148930008428611043841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1487432620005619074029227 2231148930008428611043841)
    ·
      refine ⟨1673361697506321458282881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2231148930008428611043841 1673361697506321458282881)
      ·
        refine ⟨1255021273129741093712161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1673361697506321458282881 1255021273129741093712161)
        ·
          refine ⟨941265954847305820284121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1255021273129741093712161 941265954847305820284121)
          ·
            refine ⟨705949466135479365213091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941265954847305820284121 705949466135479365213091)
            ·
              refine ⟨1058924199203219047819637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705949466135479365213091 1058924199203219047819637)
              ·
                refine ⟨99274143675301785733091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1058924199203219047819637 99274143675301785733091)
                ·
                  rfl

theorem cell19_326254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_326254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326254 prefixEnd_326254 := by exact prefixLift 326254
  have htrace : WordTrace (prefixWord ++ tailWord_326254) baseStart_326254 baseEnd_326254 := by
    simpa [prefixWord, tailWord_326254, baseEnd_326254] using wordTrace_append hprefix tailTrace_326254
  have hstable : (prefixWord ++ tailWord_326254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326254).length < 2 ^ (prefixWord ++ tailWord_326254).sum := by decide
  have hdescent : baseEnd_326254 < baseStart_326254 := by decide
  rcases family_descends (prefixWord ++ tailWord_326254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326292 : List Nat := [2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_326292 : Nat := 118140960795 + 326292 * 2 ^ 59
def prefixEnd_326292 : Nat := 4983230072969 + 3 ^ 40 * 326292 * 2
def baseEnd_326292 : Nat := 99285706498928956888543

theorem tailTrace_326292 : CollatzResearch.WordTrace tailWord_326292 prefixEnd_326292 99285706498928956888543 := by
  unfold tailWord_326292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5950423466953642541058565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7933897955938190054744753 5950423466953642541058565)
  ·
    refine ⟨1115704400053807976448481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5950423466953642541058565 1115704400053807976448481)
    ·
      refine ⟨836778300040355982336361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1115704400053807976448481 836778300040355982336361)
      ·
        refine ⟨627583725030266986752271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 836778300040355982336361 627583725030266986752271)
        ·
          refine ⟨941375587545400480128407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627583725030266986752271 941375587545400480128407)
          ·
            refine ⟨1412063381318100720192611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941375587545400480128407 1412063381318100720192611)
            ·
              refine ⟨2118095071977151080288917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412063381318100720192611 2118095071977151080288917)
              ·
                refine ⟨99285706498928956888543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2118095071977151080288917 99285706498928956888543)
                ·
                  rfl

theorem cell19_326292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_326292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326292 prefixEnd_326292 := by exact prefixLift 326292
  have htrace : WordTrace (prefixWord ++ tailWord_326292) baseStart_326292 baseEnd_326292 := by
    simpa [prefixWord, tailWord_326292, baseEnd_326292] using wordTrace_append hprefix tailTrace_326292
  have hstable : (prefixWord ++ tailWord_326292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326292).length < 2 ^ (prefixWord ++ tailWord_326292).sum := by decide
  have hdescent : baseEnd_326292 < baseStart_326292 := by decide
  rcases family_descends (prefixWord ++ tailWord_326292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326423 : List Nat := [1, 1, 3, 4, 3, 2, 2, 3]
def baseStart_326423 : Nat := 118140960795 + 326423 * 2 ^ 59
def prefixEnd_326423 : Nat := 4983230072969 + 3 ^ 40 * 326423 * 2
def baseEnd_326423 : Nat := 99325567811959467977075

theorem tailTrace_326423 : CollatzResearch.WordTrace tailWord_326423 prefixEnd_326423 99325567811959467977075 := by
  unfold tailWord_326423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11905624896432694455135923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7937083264288462970090615 11905624896432694455135923)
  ·
    refine ⟨17858437344649041682703885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11905624896432694455135923 17858437344649041682703885)
    ·
      refine ⟨6696914004243390631013957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17858437344649041682703885 6696914004243390631013957)
      ·
        refine ⟨1255671375795635743315117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6696914004243390631013957 1255671375795635743315117)
        ·
          refine ⟨470876765923363403743169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1255671375795635743315117 470876765923363403743169)
          ·
            refine ⟨353157574442522552807377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470876765923363403743169 353157574442522552807377)
            ·
              refine ⟨264868180831891914605533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353157574442522552807377 264868180831891914605533)
              ·
                refine ⟨99325567811959467977075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264868180831891914605533 99325567811959467977075)
                ·
                  rfl

theorem cell19_326423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_326423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326423 prefixEnd_326423 := by exact prefixLift 326423
  have htrace : WordTrace (prefixWord ++ tailWord_326423) baseStart_326423 baseEnd_326423 := by
    simpa [prefixWord, tailWord_326423, baseEnd_326423] using wordTrace_append hprefix tailTrace_326423
  have hstable : (prefixWord ++ tailWord_326423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326423).length < 2 ^ (prefixWord ++ tailWord_326423).sum := by decide
  have hdescent : baseEnd_326423 < baseStart_326423 := by decide
  rcases family_descends (prefixWord ++ tailWord_326423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326442 : List Nat := [3, 1, 4, 3, 1, 2, 5]
def baseStart_326442 : Nat := 118140960795 + 326442 * 2 ^ 59
def prefixEnd_326442 : Nat := 4983230072969 + 3 ^ 40 * 326442 * 2
def baseEnd_326442 : Nat := 33110449741257684518267

theorem tailTrace_326442 : CollatzResearch.WordTrace tailWord_326442 prefixEnd_326442 33110449741257684518267 := by
  unfold tailWord_326442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976579470840965175019395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7937545255575907133385053 2976579470840965175019395)
  ·
    refine ⟨4464869206261447762529093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2976579470840965175019395 4464869206261447762529093)
    ·
      refine ⟨837162976174021455474205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4464869206261447762529093 837162976174021455474205)
      ·
        refine ⟨313936116065258045802827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 837162976174021455474205 313936116065258045802827)
        ·
          refine ⟨470904174097887068704241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313936116065258045802827 470904174097887068704241)
          ·
            refine ⟨353178130573415301528181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470904174097887068704241 353178130573415301528181)
            ·
              refine ⟨33110449741257684518267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353178130573415301528181 33110449741257684518267)
              ·
                rfl

theorem cell19_326442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_326442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326442 prefixEnd_326442 := by exact prefixLift 326442
  have htrace : WordTrace (prefixWord ++ tailWord_326442) baseStart_326442 baseEnd_326442 := by
    simpa [prefixWord, tailWord_326442, baseEnd_326442] using wordTrace_append hprefix tailTrace_326442
  have hstable : (prefixWord ++ tailWord_326442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326442).length < 2 ^ (prefixWord ++ tailWord_326442).sum := by decide
  have hdescent : baseEnd_326442 < baseStart_326442 := by decide
  rcases family_descends (prefixWord ++ tailWord_326442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326518 : List Nat := [5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_326518 : Nat := 118140960795 + 326518 * 2 ^ 59
def prefixEnd_326518 : Nat := 4983230072969 + 3 ^ 40 * 326518 * 2
def baseEnd_326518 : Nat := 99354474871027395865705

theorem tailTrace_326518 : CollatzResearch.WordTrace tailWord_326518 prefixEnd_326518 99354474871027395865705 := by
  unfold tailWord_326518
  simp only [CollatzResearch.WordTrace]
  refine ⟨744318114443032854990263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7939393220725683786562805 744318114443032854990263)
  ·
    refine ⟨1116477171664549282485395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744318114443032854990263 1116477171664549282485395)
    ·
      refine ⟨1674715757496823923728093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116477171664549282485395 1674715757496823923728093)
      ·
        refine ⟨628018409061308971398035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1674715757496823923728093 628018409061308971398035)
        ·
          refine ⟨942027613591963457097053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628018409061308971398035 942027613591963457097053)
          ·
            refine ⟨353260355096986296411395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 942027613591963457097053 353260355096986296411395)
            ·
              refine ⟨529890532645479444617093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353260355096986296411395 529890532645479444617093)
              ·
                refine ⟨99354474871027395865705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529890532645479444617093 99354474871027395865705)
                ·
                  rfl

theorem cell19_326518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_326518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326518 prefixEnd_326518 := by exact prefixLift 326518
  have htrace : WordTrace (prefixWord ++ tailWord_326518) baseStart_326518 baseEnd_326518 := by
    simpa [prefixWord, tailWord_326518, baseEnd_326518] using wordTrace_append hprefix tailTrace_326518
  have hstable : (prefixWord ++ tailWord_326518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326518).length < 2 ^ (prefixWord ++ tailWord_326518).sum := by decide
  have hdescent : baseEnd_326518 < baseStart_326518 := by decide
  rcases family_descends (prefixWord ++ tailWord_326518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326617 : List Nat := [1, 2, 1, 2, 5, 3, 5]
def baseStart_326617 : Nat := 118140960795 + 326617 * 2 ^ 59
def prefixEnd_326617 : Nat := 4983230072969 + 3 ^ 40 * 326617 * 2
def baseEnd_326617 : Nat := 33128199689808166555145

theorem tailTrace_326617 : CollatzResearch.WordTrace tailWord_326617 prefixEnd_326617 33128199689808166555145 := by
  unfold tailWord_326617
  simp only [CollatzResearch.WordTrace]
  refine ⟨11912700657729865587698105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7941800438486577058465403 11912700657729865587698105)
  ·
    refine ⟨8934525493297399190773579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11912700657729865587698105 8934525493297399190773579)
    ·
      refine ⟨13401788239946098786160369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8934525493297399190773579 13401788239946098786160369)
      ·
        refine ⟨10051341179959574089620277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13401788239946098786160369 10051341179959574089620277)
        ·
          refine ⟨942313235621210070901901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10051341179959574089620277 942313235621210070901901)
          ·
            refine ⟨353367463357953776588213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 942313235621210070901901 353367463357953776588213)
            ·
              refine ⟨33128199689808166555145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353367463357953776588213 33128199689808166555145)
              ·
                rfl

theorem cell19_326617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_326617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326617 prefixEnd_326617 := by exact prefixLift 326617
  have htrace : WordTrace (prefixWord ++ tailWord_326617) baseStart_326617 baseEnd_326617 := by
    simpa [prefixWord, tailWord_326617, baseEnd_326617] using wordTrace_append hprefix tailTrace_326617
  have hstable : (prefixWord ++ tailWord_326617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326617).length < 2 ^ (prefixWord ++ tailWord_326617).sum := by decide
  have hdescent : baseEnd_326617 < baseStart_326617 := by decide
  rcases family_descends (prefixWord ++ tailWord_326617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326708 : List Nat := [2, 5, 1, 2, 1, 2, 3, 3]
def baseStart_326708 : Nat := 118140960795 + 326708 * 2 ^ 59
def prefixEnd_326708 : Nat := 4983230072969 + 3 ^ 40 * 326708 * 2
def baseEnd_326708 : Nat := 99412288989163251642965

theorem tailTrace_326708 : CollatzResearch.WordTrace tailWord_326708 prefixEnd_326708 99412288989163251642965 := by
  unfold tailWord_326708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958009850200094064630389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7944013133600125419507185 5958009850200094064630389)
  ·
    refine ⟨558563423456258818559099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5958009850200094064630389 558563423456258818559099)
    ·
      refine ⟨837845135184388227838649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558563423456258818559099 837845135184388227838649)
      ·
        refine ⟨628383851388291170878987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 837845135184388227838649 628383851388291170878987)
        ·
          refine ⟨942575777082436756318481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628383851388291170878987 942575777082436756318481)
          ·
            refine ⟨706931832811827567238861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 942575777082436756318481 706931832811827567238861)
            ·
              refine ⟨265099437304435337714573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 706931832811827567238861 265099437304435337714573)
              ·
                refine ⟨99412288989163251642965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265099437304435337714573 99412288989163251642965)
                ·
                  rfl

theorem cell19_326708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_326708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326708 prefixEnd_326708 := by exact prefixLift 326708
  have htrace : WordTrace (prefixWord ++ tailWord_326708) baseStart_326708 baseEnd_326708 := by
    simpa [prefixWord, tailWord_326708, baseEnd_326708] using wordTrace_append hprefix tailTrace_326708
  have hstable : (prefixWord ++ tailWord_326708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326708).length < 2 ^ (prefixWord ++ tailWord_326708).sum := by decide
  have hdescent : baseEnd_326708 < baseStart_326708 := by decide
  rcases family_descends (prefixWord ++ tailWord_326708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326714 : List Nat := [3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_326714 : Nat := 118140960795 + 326714 * 2 ^ 59
def prefixEnd_326714 : Nat := 4983230072969 + 3 ^ 40 * 326714 * 2
def baseEnd_326714 : Nat := 99414114698157015509615

theorem tailTrace_326714 : CollatzResearch.WordTrace tailWord_326714 prefixEnd_326714 99414114698157015509615 := by
  unfold tailWord_326714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979059634594612788494799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7944159025585634102652797 2979059634594612788494799)
  ·
    refine ⟨4468589451891919182742199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2979059634594612788494799 4468589451891919182742199)
    ·
      refine ⟨6702884177837878774113299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4468589451891919182742199 6702884177837878774113299)
      ·
        refine ⟨10054326266756818161169949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6702884177837878774113299 10054326266756818161169949)
        ·
          refine ⟨3770372350033806810438731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10054326266756818161169949 3770372350033806810438731)
          ·
            refine ⟨5655558525050710215658097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770372350033806810438731 5655558525050710215658097)
            ·
              refine ⟨4241668893788032661743573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5655558525050710215658097 4241668893788032661743573)
              ·
                refine ⟨99414114698157015509615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4241668893788032661743573 99414114698157015509615)
                ·
                  rfl

theorem cell19_326714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_326714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326714 prefixEnd_326714 := by exact prefixLift 326714
  have htrace : WordTrace (prefixWord ++ tailWord_326714) baseStart_326714 baseEnd_326714 := by
    simpa [prefixWord, tailWord_326714, baseEnd_326714] using wordTrace_append hprefix tailTrace_326714
  have hstable : (prefixWord ++ tailWord_326714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326714).length < 2 ^ (prefixWord ++ tailWord_326714).sum := by decide
  have hdescent : baseEnd_326714 < baseStart_326714 := by decide
  rcases family_descends (prefixWord ++ tailWord_326714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326752 : List Nat := [2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_326752 : Nat := 118140960795 + 326752 * 2 ^ 59
def prefixEnd_326752 : Nat := 4983230072969 + 3 ^ 40 * 326752 * 2
def baseEnd_326752 : Nat := 99425677521784186665067

theorem tailTrace_326752 : CollatzResearch.WordTrace tailWord_326752 prefixEnd_326752 99425677521784186665067 := by
  unfold tailWord_326752
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958812256120391821931255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7945083008160522429241673 5958812256120391821931255)
  ·
    refine ⟨8938218384180587732896883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5958812256120391821931255 8938218384180587732896883)
    ·
      refine ⟨13407327576270881599345325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8938218384180587732896883 13407327576270881599345325)
      ·
        refine ⟨5027747841101580599754497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13407327576270881599345325 5027747841101580599754497)
        ·
          refine ⟨3770810880826185449815873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5027747841101580599754497 3770810880826185449815873)
          ·
            refine ⟨2828108160619639087361905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3770810880826185449815873 2828108160619639087361905)
            ·
              refine ⟨2121081120464729315521429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2828108160619639087361905 2121081120464729315521429)
              ·
                refine ⟨99425677521784186665067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2121081120464729315521429 99425677521784186665067)
                ·
                  rfl

theorem cell19_326752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_326752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326752 prefixEnd_326752 := by exact prefixLift 326752
  have htrace : WordTrace (prefixWord ++ tailWord_326752) baseStart_326752 baseEnd_326752 := by
    simpa [prefixWord, tailWord_326752, baseEnd_326752] using wordTrace_append hprefix tailTrace_326752
  have hstable : (prefixWord ++ tailWord_326752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326752).length < 2 ^ (prefixWord ++ tailWord_326752).sum := by decide
  have hdescent : baseEnd_326752 < baseStart_326752 := by decide
  rcases family_descends (prefixWord ++ tailWord_326752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326782 : List Nat := [4, 2, 4, 1, 1, 2, 5]
def baseStart_326782 : Nat := 118140960795 + 326782 * 2 ^ 59
def prefixEnd_326782 : Nat := 4983230072969 + 3 ^ 40 * 326782 * 2
def baseEnd_326782 : Nat := 33144935355584335332773

theorem tailTrace_326782 : CollatzResearch.WordTrace tailWord_326782 prefixEnd_326782 33144935355584335332773 := by
  unfold tailWord_326782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489839837766512345931825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7945812468088065844969733 1489839837766512345931825)
  ·
    refine ⟨1117379878324884259448869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1489839837766512345931825 1117379878324884259448869)
    ·
      refine ⟨209508727185915798646663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1117379878324884259448869 209508727185915798646663)
      ·
        refine ⟨314263090778873697969995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209508727185915798646663 314263090778873697969995)
        ·
          refine ⟨471394636168310546954993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314263090778873697969995 471394636168310546954993)
          ·
            refine ⟨353545977126232910216245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471394636168310546954993 353545977126232910216245)
            ·
              refine ⟨33144935355584335332773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353545977126232910216245 33144935355584335332773)
              ·
                rfl

theorem cell19_326782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_326782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326782 prefixEnd_326782 := by exact prefixLift 326782
  have htrace : WordTrace (prefixWord ++ tailWord_326782) baseStart_326782 baseEnd_326782 := by
    simpa [prefixWord, tailWord_326782, baseEnd_326782] using wordTrace_append hprefix tailTrace_326782
  have hstable : (prefixWord ++ tailWord_326782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326782).length < 2 ^ (prefixWord ++ tailWord_326782).sum := by decide
  have hdescent : baseEnd_326782 < baseStart_326782 := by decide
  rcases family_descends (prefixWord ++ tailWord_326782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326788 : List Nat := [2, 3, 2, 1, 2, 4, 5]
def baseStart_326788 : Nat := 118140960795 + 326788 * 2 ^ 59
def prefixEnd_326788 : Nat := 4983230072969 + 3 ^ 40 * 326788 * 2
def baseEnd_326788 : Nat := 33145543925248923288323

theorem tailTrace_326788 : CollatzResearch.WordTrace tailWord_326788 prefixEnd_326788 33145543925248923288323 := by
  unfold tailWord_326788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5959468770055180896086509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7945958360073574528115345 5959468770055180896086509)
  ·
    refine ⟨2234800788770692836032441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5959468770055180896086509 2234800788770692836032441)
    ·
      refine ⟨1676100591578019627024331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2234800788770692836032441 1676100591578019627024331)
      ·
        refine ⟨2514150887367029440536497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676100591578019627024331 2514150887367029440536497)
        ·
          refine ⟨1885613165525272080402373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2514150887367029440536497 1885613165525272080402373)
          ·
            refine ⟨353552468535988515075445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1885613165525272080402373 353552468535988515075445)
            ·
              refine ⟨33145543925248923288323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353552468535988515075445 33145543925248923288323)
              ·
                rfl

theorem cell19_326788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_326788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326788 prefixEnd_326788 := by exact prefixLift 326788
  have htrace : WordTrace (prefixWord ++ tailWord_326788) baseStart_326788 baseEnd_326788 := by
    simpa [prefixWord, tailWord_326788, baseEnd_326788] using wordTrace_append hprefix tailTrace_326788
  have hstable : (prefixWord ++ tailWord_326788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326788).length < 2 ^ (prefixWord ++ tailWord_326788).sum := by decide
  have hdescent : baseEnd_326788 < baseStart_326788 := by decide
  rcases family_descends (prefixWord ++ tailWord_326788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326807 : List Nat := [1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_326807 : Nat := 118140960795 + 326807 * 2 ^ 59
def prefixEnd_326807 : Nat := 4983230072969 + 3 ^ 40 * 326807 * 2
def baseEnd_326807 : Nat := 99442413187560355442695

theorem tailTrace_326807 : CollatzResearch.WordTrace tailWord_326807 prefixEnd_326807 99442413187560355442695 := by
  unfold tailWord_326807
  simp only [CollatzResearch.WordTrace]
  refine ⟨11919630527041528037114675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7946420351361018691409783 11919630527041528037114675)
  ·
    refine ⟨17879445790562292055672013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11919630527041528037114675 17879445790562292055672013)
    ·
      refine ⟨6704792171460859520877005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17879445790562292055672013 6704792171460859520877005)
      ·
        refine ⟨2514297064297822320328877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6704792171460859520877005 2514297064297822320328877)
        ·
          refine ⟨942861399111683370123329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2514297064297822320328877 942861399111683370123329)
          ·
            refine ⟨707146049333762527592497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 942861399111683370123329 707146049333762527592497)
            ·
              refine ⟨530359537000321895694373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707146049333762527592497 530359537000321895694373)
              ·
                refine ⟨99442413187560355442695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530359537000321895694373 99442413187560355442695)
                ·
                  rfl

theorem cell19_326807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_326807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326807 prefixEnd_326807 := by exact prefixLift 326807
  have htrace : WordTrace (prefixWord ++ tailWord_326807) baseStart_326807 baseEnd_326807 := by
    simpa [prefixWord, tailWord_326807, baseEnd_326807] using wordTrace_append hprefix tailTrace_326807
  have hstable : (prefixWord ++ tailWord_326807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326807).length < 2 ^ (prefixWord ++ tailWord_326807).sum := by decide
  have hdescent : baseEnd_326807 < baseStart_326807 := by decide
  rcases family_descends (prefixWord ++ tailWord_326807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326862 : List Nat := [4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_326862 : Nat := 118140960795 + 326862 * 2 ^ 59
def prefixEnd_326862 : Nat := 4983230072969 + 3 ^ 40 * 326862 * 2
def baseEnd_326862 : Nat := 99459148853336524220323

theorem tailTrace_326862 : CollatzResearch.WordTrace tailWord_326862 prefixEnd_326862 99459148853336524220323 := by
  unfold tailWord_326862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490204567730284053795855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7947757694561514953577893 1490204567730284053795855)
  ·
    refine ⟨2235306851595426080693783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490204567730284053795855 2235306851595426080693783)
    ·
      refine ⟨3352960277393139121040675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2235306851595426080693783 3352960277393139121040675)
      ·
        refine ⟨5029440416089708681561013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352960277393139121040675 5029440416089708681561013)
        ·
          refine ⟨471510039008410188896345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5029440416089708681561013 471510039008410188896345)
          ·
            refine ⟨353632529256307641672259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471510039008410188896345 353632529256307641672259)
            ·
              refine ⟨530448793884461462508389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353632529256307641672259 530448793884461462508389)
              ·
                refine ⟨99459148853336524220323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530448793884461462508389 99459148853336524220323)
                ·
                  rfl

theorem cell19_326862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_326862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326862 prefixEnd_326862 := by exact prefixLift 326862
  have htrace : WordTrace (prefixWord ++ tailWord_326862) baseStart_326862 baseEnd_326862 := by
    simpa [prefixWord, tailWord_326862, baseEnd_326862] using wordTrace_append hprefix tailTrace_326862
  have hstable : (prefixWord ++ tailWord_326862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326862).length < 2 ^ (prefixWord ++ tailWord_326862).sum := by decide
  have hdescent : baseEnd_326862 < baseStart_326862 := by decide
  rcases family_descends (prefixWord ++ tailWord_326862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326938 : List Nat := [3, 1, 1, 3, 3, 3, 2, 3]
def baseStart_326938 : Nat := 118140960795 + 326938 * 2 ^ 59
def prefixEnd_326938 : Nat := 4983230072969 + 3 ^ 40 * 326938 * 2
def baseEnd_326938 : Nat := 99482274500590866531227

theorem tailTrace_326938 : CollatzResearch.WordTrace tailWord_326938 prefixEnd_326938 99482274500590866531227 := by
  unfold tailWord_326938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981102122391734352533367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7949605659711291606755645 2981102122391734352533367)
  ·
    refine ⟨4471653183587601528800051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2981102122391734352533367 4471653183587601528800051)
    ·
      refine ⟨6707479775381402293200077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4471653183587601528800051 6707479775381402293200077)
      ·
        refine ⟨2515304915768025859950029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6707479775381402293200077 2515304915768025859950029)
        ·
          refine ⟨943239343413009697481261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2515304915768025859950029 943239343413009697481261)
          ·
            refine ⟨353714753779878636555473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 943239343413009697481261 353714753779878636555473)
            ·
              refine ⟨265286065334908977416605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353714753779878636555473 265286065334908977416605)
              ·
                refine ⟨99482274500590866531227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265286065334908977416605 99482274500590866531227)
                ·
                  rfl

theorem cell19_326938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_326938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326938 prefixEnd_326938 := by exact prefixLift 326938
  have htrace : WordTrace (prefixWord ++ tailWord_326938) baseStart_326938 baseEnd_326938 := by
    simpa [prefixWord, tailWord_326938, baseEnd_326938] using wordTrace_append hprefix tailTrace_326938
  have hstable : (prefixWord ++ tailWord_326938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326938).length < 2 ^ (prefixWord ++ tailWord_326938).sum := by decide
  have hdescent : baseEnd_326938 < baseStart_326938 := by decide
  rcases family_descends (prefixWord ++ tailWord_326938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326940 : List Nat := [2, 2, 3, 1, 1, 1, 6, 3]
def baseStart_326940 : Nat := 118140960795 + 326940 * 2 ^ 59
def prefixEnd_326940 : Nat := 4983230072969 + 3 ^ 40 * 326940 * 2
def baseEnd_326940 : Nat := 99482883070255454486777

theorem tailTrace_326940 : CollatzResearch.WordTrace tailWord_326940 prefixEnd_326940 99482883070255454486777 := by
  unfold tailWord_326940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962240717779845875853137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7949654290373127834470849 5962240717779845875853137)
  ·
    refine ⟨4471680538334884406889853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5962240717779845875853137 4471680538334884406889853)
    ·
      refine ⟨1676880201875581652583695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4471680538334884406889853 1676880201875581652583695)
      ·
        refine ⟨2515320302813372478875543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676880201875581652583695 2515320302813372478875543)
        ·
          refine ⟨3772980454220058718313315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515320302813372478875543 3772980454220058718313315)
          ·
            refine ⟨5659470681330088077469973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772980454220058718313315 5659470681330088077469973)
            ·
              refine ⟨265287688187347878631405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5659470681330088077469973 265287688187347878631405)
              ·
                refine ⟨99482883070255454486777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265287688187347878631405 99482883070255454486777)
                ·
                  rfl

theorem cell19_326940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_326940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326940 prefixEnd_326940 := by exact prefixLift 326940
  have htrace : WordTrace (prefixWord ++ tailWord_326940) baseStart_326940 baseEnd_326940 := by
    simpa [prefixWord, tailWord_326940, baseEnd_326940] using wordTrace_append hprefix tailTrace_326940
  have hstable : (prefixWord ++ tailWord_326940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326940).length < 2 ^ (prefixWord ++ tailWord_326940).sum := by decide
  have hdescent : baseEnd_326940 < baseStart_326940 := by decide
  rcases family_descends (prefixWord ++ tailWord_326940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326957 : List Nat := [1, 5, 3, 1, 1, 3, 5]
def baseStart_326957 : Nat := 118140960795 + 326957 * 2 ^ 59
def prefixEnd_326957 : Nat := 4983230072969 + 3 ^ 40 * 326957 * 2
def baseEnd_326957 : Nat := 33162685304134817369651

theorem tailTrace_326957 : CollatzResearch.WordTrace tailWord_326957 prefixEnd_326957 33162685304134817369651 := by
  unfold tailWord_326957
  simp only [CollatzResearch.WordTrace]
  refine ⟨11925101476498103655075125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7950067650998735770050083 11925101476498103655075125)
  ·
    refine ⟨1117978263421697217663293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11925101476498103655075125 1117978263421697217663293)
    ·
      refine ⟨419241848783136456623735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1117978263421697217663293 419241848783136456623735)
      ·
        refine ⟨628862773174704684935603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419241848783136456623735 628862773174704684935603)
        ·
          refine ⟨943294159762057027403405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628862773174704684935603 943294159762057027403405)
          ·
            refine ⟨353735309910771385276277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 943294159762057027403405 353735309910771385276277)
            ·
              refine ⟨33162685304134817369651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353735309910771385276277 33162685304134817369651)
              ·
                rfl

theorem cell19_326957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_326957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326957 prefixEnd_326957 := by exact prefixLift 326957
  have htrace : WordTrace (prefixWord ++ tailWord_326957) baseStart_326957 baseEnd_326957 := by
    simpa [prefixWord, tailWord_326957, baseEnd_326957] using wordTrace_append hprefix tailTrace_326957
  have hstable : (prefixWord ++ tailWord_326957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326957).length < 2 ^ (prefixWord ++ tailWord_326957).sum := by decide
  have hdescent : baseEnd_326957 < baseStart_326957 := by decide
  rcases family_descends (prefixWord ++ tailWord_326957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326961 : List Nat := [1, 2, 2, 3, 3, 1, 7]
def baseStart_326961 : Nat := 118140960795 + 326961 * 2 ^ 59
def prefixEnd_326961 : Nat := 4983230072969 + 3 ^ 40 * 326961 * 2
def baseEnd_326961 : Nat := 33163091017244542673351

theorem tailTrace_326961 : CollatzResearch.WordTrace tailWord_326961 prefixEnd_326961 33163091017244542673351 := by
  unfold tailWord_326961
  simp only [CollatzResearch.WordTrace]
  refine ⟨11925247368483612338220737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7950164912322408225480491 11925247368483612338220737)
  ·
    refine ⟨8943935526362709253665553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11925247368483612338220737 8943935526362709253665553)
    ·
      refine ⟨6707951644772031940249165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8943935526362709253665553 6707951644772031940249165)
      ·
        refine ⟨2515481866789511977593437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6707951644772031940249165 2515481866789511977593437)
        ·
          refine ⟨943305700046066991597539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2515481866789511977593437 943305700046066991597539)
          ·
            refine ⟨1414958550069100487396309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943305700046066991597539 1414958550069100487396309)
            ·
              refine ⟨33163091017244542673351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1414958550069100487396309 33163091017244542673351)
              ·
                rfl

theorem cell19_326961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_326961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326961 prefixEnd_326961 := by exact prefixLift 326961
  have htrace : WordTrace (prefixWord ++ tailWord_326961) baseStart_326961 baseEnd_326961 := by
    simpa [prefixWord, tailWord_326961, baseEnd_326961] using wordTrace_append hprefix tailTrace_326961
  have hstable : (prefixWord ++ tailWord_326961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326961).length < 2 ^ (prefixWord ++ tailWord_326961).sum := by decide
  have hdescent : baseEnd_326961 < baseStart_326961 := by decide
  rcases family_descends (prefixWord ++ tailWord_326961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326999 : List Nat := [1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_326999 : Nat := 118140960795 + 326999 * 2 ^ 59
def prefixEnd_326999 : Nat := 4983230072969 + 3 ^ 40 * 326999 * 2
def baseEnd_326999 : Nat := 99500835875360799175505

theorem tailTrace_326999 : CollatzResearch.WordTrace tailWord_326999 prefixEnd_326999 99500835875360799175505 := by
  unfold tailWord_326999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926633342345944828104051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7951088894897296552069367 11926633342345944828104051)
  ·
    refine ⟨17889950013518917242156077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11926633342345944828104051 17889950013518917242156077)
    ·
      refine ⟨6708731255069593965808529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17889950013518917242156077 6708731255069593965808529)
      ·
        refine ⟨5031548441302195474356397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6708731255069593965808529 5031548441302195474356397)
        ·
          refine ⟨1886830665488323302883649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5031548441302195474356397 1886830665488323302883649)
          ·
            refine ⟨1415122999116242477162737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886830665488323302883649 1415122999116242477162737)
            ·
              refine ⟨1061342249337181857872053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415122999116242477162737 1061342249337181857872053)
              ·
                refine ⟨99500835875360799175505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1061342249337181857872053 99500835875360799175505)
                ·
                  rfl

theorem cell19_326999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_326999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_326999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_326999 prefixEnd_326999 := by exact prefixLift 326999
  have htrace : WordTrace (prefixWord ++ tailWord_326999) baseStart_326999 baseEnd_326999 := by
    simpa [prefixWord, tailWord_326999, baseEnd_326999] using wordTrace_append hprefix tailTrace_326999
  have hstable : (prefixWord ++ tailWord_326999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326999).length < 2 ^ (prefixWord ++ tailWord_326999).sum := by decide
  have hdescent : baseEnd_326999 < baseStart_326999 := by decide
  rcases family_descends (prefixWord ++ tailWord_326999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327016 : List Nat := [2, 1, 4, 2, 4, 6]
def baseStart_327016 : Nat := 118140960795 + 327016 * 2 ^ 59
def prefixEnd_327016 : Nat := 4983230072969 + 3 ^ 40 * 327016 * 2
def baseEnd_327016 : Nat := 11056223190834421866409

theorem tailTrace_327016 : CollatzResearch.WordTrace tailWord_327016 prefixEnd_327016 11056223190834421866409 := by
  unfold tailWord_327016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5963626691642178365736451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7951502255522904487648601 5963626691642178365736451)
  ·
    refine ⟨8945440037463267548604677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5963626691642178365736451 8945440037463267548604677)
    ·
      refine ⟨1677270007024362665363377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8945440037463267548604677 1677270007024362665363377)
      ·
        refine ⟨1257952505268271999022533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1677270007024362665363377 1257952505268271999022533)
        ·
          refine ⟨235866094737800999816725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1257952505268271999022533 235866094737800999816725)
          ·
            refine ⟨11056223190834421866409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 235866094737800999816725 11056223190834421866409)
            ·
              rfl

theorem cell19_327016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 6].length) (baseStart_327016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327016 prefixEnd_327016 := by exact prefixLift 327016
  have htrace : WordTrace (prefixWord ++ tailWord_327016) baseStart_327016 baseEnd_327016 := by
    simpa [prefixWord, tailWord_327016, baseEnd_327016] using wordTrace_append hprefix tailTrace_327016
  have hstable : (prefixWord ++ tailWord_327016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327016).length < 2 ^ (prefixWord ++ tailWord_327016).sum := by decide
  have hdescent : baseEnd_327016 < baseStart_327016 := by decide
  rcases family_descends (prefixWord ++ tailWord_327016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327018 : List Nat := [3, 1, 3, 3, 9]
def baseStart_327018 : Nat := 118140960795 + 327018 * 2 ^ 59
def prefixEnd_327018 : Nat := 4983230072969 + 3 ^ 40 * 327018 * 2
def baseEnd_327018 : Nat := 3685430269895347583453

theorem tailTrace_327018 : CollatzResearch.WordTrace tailWord_327018 prefixEnd_327018 3685430269895347583453 := by
  unfold tailWord_327018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981831582319277768261427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7951550886184740715363805 2981831582319277768261427)
  ·
    refine ⟨4472747373478916652392141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2981831582319277768261427 4472747373478916652392141)
    ·
      refine ⟨1677280265054593744647053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4472747373478916652392141 1677280265054593744647053)
      ·
        refine ⟨628980099395472654242645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1677280265054593744647053 628980099395472654242645)
        ·
          refine ⟨3685430269895347583453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 628980099395472654242645 3685430269895347583453)
          ·
            rfl

theorem cell19_327018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 9].length) (baseStart_327018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327018 prefixEnd_327018 := by exact prefixLift 327018
  have htrace : WordTrace (prefixWord ++ tailWord_327018) baseStart_327018 baseEnd_327018 := by
    simpa [prefixWord, tailWord_327018, baseEnd_327018] using wordTrace_append hprefix tailTrace_327018
  have hstable : (prefixWord ++ tailWord_327018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327018).length < 2 ^ (prefixWord ++ tailWord_327018).sum := by decide
  have hdescent : baseEnd_327018 < baseStart_327018 := by decide
  rcases family_descends (prefixWord ++ tailWord_327018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327191 : List Nat := [1, 1, 3, 14]
def baseStart_327191 : Nat := 118140960795 + 327191 * 2 ^ 59
def prefixEnd_327191 : Nat := 4983230072969 + 3 ^ 40 * 327191 * 2
def baseEnd_327191 : Nat := 1229126648927916579115

theorem tailTrace_327191 : CollatzResearch.WordTrace tailWord_327191 prefixEnd_327191 1229126648927916579115 := by
  unfold tailWord_327191
  simp only [CollatzResearch.WordTrace]
  refine ⟨11933636157650361619093427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7955757438433574412728951 11933636157650361619093427)
  ·
    refine ⟨17900454236475542428640141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11933636157650361619093427 17900454236475542428640141)
    ·
      refine ⟨6712670338678328410740053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17900454236475542428640141 6712670338678328410740053)
      ·
        refine ⟨1229126648927916579115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 6712670338678328410740053 1229126648927916579115)
        ·
          rfl

theorem cell19_327191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 14].length) (baseStart_327191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327191 prefixEnd_327191 := by exact prefixLift 327191
  have htrace : WordTrace (prefixWord ++ tailWord_327191) baseStart_327191 baseEnd_327191 := by
    simpa [prefixWord, tailWord_327191, baseEnd_327191] using wordTrace_append hprefix tailTrace_327191
  have hstable : (prefixWord ++ tailWord_327191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327191).length < 2 ^ (prefixWord ++ tailWord_327191).sum := by decide
  have hdescent : baseEnd_327191 < baseStart_327191 := by decide
  rcases family_descends (prefixWord ++ tailWord_327191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327198 : List Nat := [4, 3, 3, 1, 2, 1, 1, 4]
def baseStart_327198 : Nat := 118140960795 + 327198 * 2 ^ 59
def prefixEnd_327198 : Nat := 4983230072969 + 3 ^ 40 * 327198 * 2
def baseEnd_327198 : Nat := 99561388556987300752741

theorem tailTrace_327198 : CollatzResearch.WordTrace tailWord_327198 prefixEnd_327198 99561388556987300752741 := by
  unfold tailWord_327198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491736433578125226824781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7955927645750001209732165 1491736433578125226824781)
  ·
    refine ⟨559401162591796960059293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1491736433578125226824781 559401162591796960059293)
    ·
      refine ⟨209775435971923860022235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 559401162591796960059293 209775435971923860022235)
      ·
        refine ⟨314663153957885790033353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209775435971923860022235 314663153957885790033353)
        ·
          refine ⟨235997365468414342525015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314663153957885790033353 235997365468414342525015)
          ·
            refine ⟨353996048202621513787523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235997365468414342525015 353996048202621513787523)
            ·
              refine ⟨530994072303932270681285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353996048202621513787523 530994072303932270681285)
              ·
                refine ⟨99561388556987300752741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530994072303932270681285 99561388556987300752741)
                ·
                  rfl

theorem cell19_327198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_327198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327198 prefixEnd_327198 := by exact prefixLift 327198
  have htrace : WordTrace (prefixWord ++ tailWord_327198) baseStart_327198 baseEnd_327198 := by
    simpa [prefixWord, tailWord_327198, baseEnd_327198] using wordTrace_append hprefix tailTrace_327198
  have hstable : (prefixWord ++ tailWord_327198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327198).length < 2 ^ (prefixWord ++ tailWord_327198).sum := by decide
  have hdescent : baseEnd_327198 < baseStart_327198 := by decide
  rcases family_descends (prefixWord ++ tailWord_327198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327225 : List Nat := [1, 2, 1, 5, 1, 3, 3, 3]
def baseStart_327225 : Nat := 118140960795 + 327225 * 2 ^ 59
def prefixEnd_327225 : Nat := 4983230072969 + 3 ^ 40 * 327225 * 2
def baseEnd_327225 : Nat := 99569604247459238152667

theorem tailTrace_327225 : CollatzResearch.WordTrace tailWord_327225 prefixEnd_327225 99569604247459238152667 := by
  unfold tailWord_327225
  simp only [CollatzResearch.WordTrace]
  refine ⟨11934876239527185425831129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7956584159684790283887419 11934876239527185425831129)
  ·
    refine ⟨8951157179645389069373347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11934876239527185425831129 8951157179645389069373347)
    ·
      refine ⟨13426735769468083604060021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8951157179645389069373347 13426735769468083604060021)
      ·
        refine ⟨1258756478387632837880627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13426735769468083604060021 1258756478387632837880627)
        ·
          refine ⟨1888134717581449256820941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258756478387632837880627 1888134717581449256820941)
          ·
            refine ⟨708050519093043471307853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1888134717581449256820941 708050519093043471307853)
            ·
              refine ⟨265518944659891301740445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708050519093043471307853 265518944659891301740445)
              ·
                refine ⟨99569604247459238152667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265518944659891301740445 99569604247459238152667)
                ·
                  rfl

theorem cell19_327225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_327225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327225 prefixEnd_327225 := by exact prefixLift 327225
  have htrace : WordTrace (prefixWord ++ tailWord_327225) baseStart_327225 baseEnd_327225 := by
    simpa [prefixWord, tailWord_327225, baseEnd_327225] using wordTrace_append hprefix tailTrace_327225
  have hstable : (prefixWord ++ tailWord_327225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327225).length < 2 ^ (prefixWord ++ tailWord_327225).sum := by decide
  have hdescent : baseEnd_327225 < baseStart_327225 := by decide
  rcases family_descends (prefixWord ++ tailWord_327225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327248 : List Nat := [2, 1, 1, 1, 1, 3, 10]
def baseStart_327248 : Nat := 118140960795 + 327248 * 2 ^ 59
def prefixEnd_327248 : Nat := 4983230072969 + 3 ^ 40 * 327248 * 2
def baseEnd_327248 : Nat := 33192200932867333213831

theorem tailTrace_327248 : CollatzResearch.WordTrace tailWord_327248 prefixEnd_327248 33192200932867333213831 := by
  unfold tailWord_327248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967857559221930176959199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7957143412295906902612265 5967857559221930176959199)
  ·
    refine ⟨8951786338832895265438799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5967857559221930176959199 8951786338832895265438799)
    ·
      refine ⟨13427679508249342898158199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8951786338832895265438799 13427679508249342898158199)
      ·
        refine ⟨20141519262374014347237299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13427679508249342898158199 20141519262374014347237299)
        ·
          refine ⟨30212278893561021520855949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20141519262374014347237299 30212278893561021520855949)
          ·
            refine ⟨11329604585085383070320981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30212278893561021520855949 11329604585085383070320981)
            ·
              refine ⟨33192200932867333213831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11329604585085383070320981 33192200932867333213831)
              ·
                rfl

theorem cell19_327248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_327248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327248 prefixEnd_327248 := by exact prefixLift 327248
  have htrace : WordTrace (prefixWord ++ tailWord_327248) baseStart_327248 baseEnd_327248 := by
    simpa [prefixWord, tailWord_327248, baseEnd_327248] using wordTrace_append hprefix tailTrace_327248
  have hstable : (prefixWord ++ tailWord_327248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327248).length < 2 ^ (prefixWord ++ tailWord_327248).sum := by decide
  have hdescent : baseEnd_327248 < baseStart_327248 := by decide
  rcases family_descends (prefixWord ++ tailWord_327248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327278 : List Nat := [4, 1, 2, 2, 4, 1, 2, 3]
def baseStart_327278 : Nat := 118140960795 + 327278 * 2 ^ 59
def prefixEnd_327278 : Nat := 4983230072969 + 3 ^ 40 * 327278 * 2
def baseEnd_327278 : Nat := 99585731343570818974745

theorem tailTrace_327278 : CollatzResearch.WordTrace tailWord_327278 prefixEnd_327278 99585731343570818974745 := by
  unfold tailWord_327278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492101163541896934688811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7957872872223450318340325 1492101163541896934688811)
  ·
    refine ⟨2238151745312845402033217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1492101163541896934688811 2238151745312845402033217)
    ·
      refine ⟨1678613808984634051524913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2238151745312845402033217 1678613808984634051524913)
      ·
        refine ⟨1258960356738475538643685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678613808984634051524913 1258960356738475538643685)
        ·
          refine ⟨236055066888464163495691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1258960356738475538643685 236055066888464163495691)
          ·
            refine ⟨354082600332696245243537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236055066888464163495691 354082600332696245243537)
            ·
              refine ⟨265561950249522183932653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354082600332696245243537 265561950249522183932653)
              ·
                refine ⟨99585731343570818974745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265561950249522183932653 99585731343570818974745)
                ·
                  rfl

theorem cell19_327278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_327278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327278 prefixEnd_327278 := by exact prefixLift 327278
  have htrace : WordTrace (prefixWord ++ tailWord_327278) baseStart_327278 baseEnd_327278 := by
    simpa [prefixWord, tailWord_327278, baseEnd_327278] using wordTrace_append hprefix tailTrace_327278
  have hstable : (prefixWord ++ tailWord_327278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327278).length < 2 ^ (prefixWord ++ tailWord_327278).sum := by decide
  have hdescent : baseEnd_327278 < baseStart_327278 := by decide
  rcases family_descends (prefixWord ++ tailWord_327278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327282 : List Nat := [3, 2, 1, 2, 3, 1, 4, 3]
def baseStart_327282 : Nat := 118140960795 + 327282 * 2 ^ 59
def prefixEnd_327282 : Nat := 4983230072969 + 3 ^ 40 * 327282 * 2
def baseEnd_327282 : Nat := 99586948482899994885845

theorem tailTrace_327282 : CollatzResearch.WordTrace tailWord_327282 prefixEnd_327282 99586948482899994885845 := by
  unfold tailWord_327282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984238800080171040164025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7957970133547122773770733 2984238800080171040164025)
  ·
    refine ⟨2238179100060128280123019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2984238800080171040164025 2238179100060128280123019)
    ·
      refine ⟨3357268650090192420184529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238179100060128280123019 3357268650090192420184529)
      ·
        refine ⟨2517951487567644315138397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3357268650090192420184529 2517951487567644315138397)
        ·
          refine ⟨944231807837866618176899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2517951487567644315138397 944231807837866618176899)
          ·
            refine ⟨1416347711756799927265349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944231807837866618176899 1416347711756799927265349)
            ·
              refine ⟨265565195954399986362253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1416347711756799927265349 265565195954399986362253)
              ·
                refine ⟨99586948482899994885845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265565195954399986362253 99586948482899994885845)
                ·
                  rfl

theorem cell19_327282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_327282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327282 prefixEnd_327282 := by exact prefixLift 327282
  have htrace : WordTrace (prefixWord ++ tailWord_327282) baseStart_327282 baseEnd_327282 := by
    simpa [prefixWord, tailWord_327282, baseEnd_327282] using wordTrace_append hprefix tailTrace_327282
  have hstable : (prefixWord ++ tailWord_327282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327282).length < 2 ^ (prefixWord ++ tailWord_327282).sum := by decide
  have hdescent : baseEnd_327282 < baseStart_327282 := by decide
  rcases family_descends (prefixWord ++ tailWord_327282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327303 : List Nat := [1, 1, 4, 2, 1, 5, 5]
def baseStart_327303 : Nat := 118140960795 + 327303 * 2 ^ 59
def prefixEnd_327303 : Nat := 4983230072969 + 3 ^ 40 * 327303 * 2
def baseEnd_327303 : Nat := 33197779488126056139707

theorem tailTrace_327303 : CollatzResearch.WordTrace tailWord_327303 prefixEnd_327303 33197779488126056139707 := by
  unfold tailWord_327303
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937721133244604747170563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7958480755496403164780375 11937721133244604747170563)
  ·
    refine ⟨17906581699866907120755845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937721133244604747170563 17906581699866907120755845)
    ·
      refine ⟨3357484068725045085141721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17906581699866907120755845 3357484068725045085141721)
      ·
        refine ⟨2518113051543783813856291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3357484068725045085141721 2518113051543783813856291)
        ·
          refine ⟨3777169577315675720784437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518113051543783813856291 3777169577315675720784437)
          ·
            refine ⟨354109647873344598823541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3777169577315675720784437 354109647873344598823541)
            ·
              refine ⟨33197779488126056139707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 354109647873344598823541 33197779488126056139707)
              ·
                rfl

theorem cell19_327303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_327303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327303 prefixEnd_327303 := by exact prefixLift 327303
  have htrace : WordTrace (prefixWord ++ tailWord_327303) baseStart_327303 baseEnd_327303 := by
    simpa [prefixWord, tailWord_327303, baseEnd_327303] using wordTrace_append hprefix tailTrace_327303
  have hstable : (prefixWord ++ tailWord_327303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327303).length < 2 ^ (prefixWord ++ tailWord_327303).sum := by decide
  have hdescent : baseEnd_327303 < baseStart_327303 := by decide
  rcases family_descends (prefixWord ++ tailWord_327303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327305 : List Nat := [1, 2, 1, 1, 4, 1, 9]
def baseStart_327305 : Nat := 118140960795 + 327305 * 2 ^ 59
def prefixEnd_327305 : Nat := 4983230072969 + 3 ^ 40 * 327305 * 2
def baseEnd_327305 : Nat := 33197982344680918791557

theorem tailTrace_327305 : CollatzResearch.WordTrace tailWord_327305 prefixEnd_327305 33197982344680918791557 := by
  unfold tailWord_327305
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937794079237359088743369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7958529386158239392495579 11937794079237359088743369)
  ·
    refine ⟨8953345559428019316557527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11937794079237359088743369 8953345559428019316557527)
    ·
      refine ⟨13430018339142028974836291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8953345559428019316557527 13430018339142028974836291)
      ·
        refine ⟨20145027508713043462254437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13430018339142028974836291 20145027508713043462254437)
        ·
          refine ⟨3777192657883695649172707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20145027508713043462254437 3777192657883695649172707)
          ·
            refine ⟨5665788986825543473759061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3777192657883695649172707 5665788986825543473759061)
            ·
              refine ⟨33197982344680918791557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5665788986825543473759061 33197982344680918791557)
              ·
                rfl

theorem cell19_327305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_327305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327305 prefixEnd_327305 := by exact prefixLift 327305
  have htrace : WordTrace (prefixWord ++ tailWord_327305) baseStart_327305 baseEnd_327305 := by
    simpa [prefixWord, tailWord_327305, baseEnd_327305] using wordTrace_append hprefix tailTrace_327305
  have hstable : (prefixWord ++ tailWord_327305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327305).length < 2 ^ (prefixWord ++ tailWord_327305).sum := by decide
  have hdescent : baseEnd_327305 < baseStart_327305 := by decide
  rcases family_descends (prefixWord ++ tailWord_327305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327341 : List Nat := [1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_327341 : Nat := 118140960795 + 327341 * 2 ^ 59
def prefixEnd_327341 : Nat := 4983230072969 + 3 ^ 40 * 327341 * 2
def baseEnd_327341 : Nat := 99604901288005339574573

theorem tailTrace_327341 : CollatzResearch.WordTrace tailWord_327341 prefixEnd_327341 99604901288005339574573 := by
  unfold tailWord_327341
  simp only [CollatzResearch.WordTrace]
  refine ⟨11939107107106937237053877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7959404738071291491369251 11939107107106937237053877)
  ·
    refine ⟨1119291291291275365973801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11939107107106937237053877 1119291291291275365973801)
    ·
      refine ⟨839468468468456524480351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1119291291291275365973801 839468468468456524480351)
      ·
        refine ⟨1259202702702684786720527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839468468468456524480351 1259202702702684786720527)
        ·
          refine ⟨1888804054054027180080791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259202702702684786720527 1888804054054027180080791)
          ·
            refine ⟨2833206081081040770121187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888804054054027180080791 2833206081081040770121187)
            ·
              refine ⟨4249809121621561155181781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833206081081040770121187 4249809121621561155181781)
              ·
                refine ⟨99604901288005339574573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4249809121621561155181781 99604901288005339574573)
                ·
                  rfl

theorem cell19_327341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_327341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327341 prefixEnd_327341 := by exact prefixLift 327341
  have htrace : WordTrace (prefixWord ++ tailWord_327341) baseStart_327341 baseEnd_327341 := by
    simpa [prefixWord, tailWord_327341, baseEnd_327341] using wordTrace_append hprefix tailTrace_327341
  have hstable : (prefixWord ++ tailWord_327341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327341).length < 2 ^ (prefixWord ++ tailWord_327341).sum := by decide
  have hdescent : baseEnd_327341 < baseStart_327341 := by decide
  rcases family_descends (prefixWord ++ tailWord_327341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327343 : List Nat := [1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_327343 : Nat := 118140960795 + 327343 * 2 ^ 59
def prefixEnd_327343 : Nat := 4983230072969 + 3 ^ 40 * 327343 * 2
def baseEnd_327343 : Nat := 99605509857669927530123

theorem tailTrace_327343 : CollatzResearch.WordTrace tailWord_327343 prefixEnd_327343 99605509857669927530123 := by
  unfold tailWord_327343
  simp only [CollatzResearch.WordTrace]
  refine ⟨11939180053099691578626683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7959453368733127719084455 11939180053099691578626683)
  ·
    refine ⟨17908770079649537367940025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11939180053099691578626683 17908770079649537367940025)
    ·
      refine ⟨13431577559737153025955019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17908770079649537367940025 13431577559737153025955019)
      ·
        refine ⟨20147366339605729538932529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13431577559737153025955019 20147366339605729538932529)
        ·
          refine ⟨15110524754704297154199397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20147366339605729538932529 15110524754704297154199397)
          ·
            refine ⟨2833223391507055716412387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15110524754704297154199397 2833223391507055716412387)
            ·
              refine ⟨4249835087260583574618581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833223391507055716412387 4249835087260583574618581)
              ·
                refine ⟨99605509857669927530123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4249835087260583574618581 99605509857669927530123)
                ·
                  rfl

theorem cell19_327343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_327343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327343 prefixEnd_327343 := by exact prefixLift 327343
  have htrace : WordTrace (prefixWord ++ tailWord_327343) baseStart_327343 baseEnd_327343 := by
    simpa [prefixWord, tailWord_327343, baseEnd_327343] using wordTrace_append hprefix tailTrace_327343
  have hstable : (prefixWord ++ tailWord_327343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327343).length < 2 ^ (prefixWord ++ tailWord_327343).sum := by decide
  have hdescent : baseEnd_327343 < baseStart_327343 := by decide
  rcases family_descends (prefixWord ++ tailWord_327343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327470 : List Nat := [4, 1, 3, 2, 3, 1, 5]
def baseStart_327470 : Nat := 118140960795 + 327470 * 2 ^ 59
def prefixEnd_327470 : Nat := 4983230072969 + 3 ^ 40 * 327470 * 2
def baseEnd_327470 : Nat := 33214718010457087569185

theorem tailTrace_327470 : CollatzResearch.WordTrace tailWord_327470 prefixEnd_327470 33214718010457087569185 := by
  unfold tailWord_327470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492976515454949033562483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7962541415759728178999909 1492976515454949033562483)
  ·
    refine ⟨2239464773182423550343725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1492976515454949033562483 2239464773182423550343725)
    ·
      refine ⟨839799289943408831378897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2239464773182423550343725 839799289943408831378897)
      ·
        refine ⟨629849467457556623534173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839799289943408831378897 629849467457556623534173)
        ·
          refine ⟨236193550296583733825315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 629849467457556623534173 236193550296583733825315)
          ·
            refine ⟨354290325444875600737973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236193550296583733825315 354290325444875600737973)
            ·
              refine ⟨33214718010457087569185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 354290325444875600737973 33214718010457087569185)
              ·
                rfl

theorem cell19_327470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_327470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327470 prefixEnd_327470 := by exact prefixLift 327470
  have htrace : WordTrace (prefixWord ++ tailWord_327470) baseStart_327470 baseEnd_327470 := by
    simpa [prefixWord, tailWord_327470, baseEnd_327470] using wordTrace_append hprefix tailTrace_327470
  have hstable : (prefixWord ++ tailWord_327470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327470).length < 2 ^ (prefixWord ++ tailWord_327470).sum := by decide
  have hdescent : baseEnd_327470 < baseStart_327470 := by decide
  rcases family_descends (prefixWord ++ tailWord_327470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327474 : List Nat := [3, 2, 1, 1, 3, 4, 5]
def baseStart_327474 : Nat := 118140960795 + 327474 * 2 ^ 59
def prefixEnd_327474 : Nat := 4983230072969 + 3 ^ 40 * 327474 * 2
def baseEnd_327474 : Nat := 33215123723566812872885

theorem tailTrace_327474 : CollatzResearch.WordTrace tailWord_327474 prefixEnd_327474 33215123723566812872885 := by
  unfold tailWord_327474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985989503906275237911369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7962638677083400634430317 2985989503906275237911369)
  ·
    refine ⟨2239492127929706428433527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2985989503906275237911369 2239492127929706428433527)
    ·
      refine ⟨3359238191894559642650291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239492127929706428433527 3359238191894559642650291)
      ·
        refine ⟨5038857287841839463975437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359238191894559642650291 5038857287841839463975437)
        ·
          refine ⟨1889571482940689798990789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5038857287841839463975437 1889571482940689798990789)
          ·
            refine ⟨354294653051379337310773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1889571482940689798990789 354294653051379337310773)
            ·
              refine ⟨33215123723566812872885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 354294653051379337310773 33215123723566812872885)
              ·
                rfl

theorem cell19_327474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_327474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327474 prefixEnd_327474 := by exact prefixLift 327474
  have htrace : WordTrace (prefixWord ++ tailWord_327474) baseStart_327474 baseEnd_327474 := by
    simpa [prefixWord, tailWord_327474, baseEnd_327474] using wordTrace_append hprefix tailTrace_327474
  have hstable : (prefixWord ++ tailWord_327474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327474).length < 2 ^ (prefixWord ++ tailWord_327474).sum := by decide
  have hdescent : baseEnd_327474 < baseStart_327474 := by decide
  rcases family_descends (prefixWord ++ tailWord_327474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327495 : List Nat := [1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_327495 : Nat := 118140960795 + 327495 * 2 ^ 59
def prefixEnd_327495 : Nat := 4983230072969 + 3 ^ 40 * 327495 * 2
def baseEnd_327495 : Nat := 99651761152178612151931

theorem tailTrace_327495 : CollatzResearch.WordTrace tailWord_327495 prefixEnd_327495 99651761152178612151931 := by
  unfold tailWord_327495
  simp only [CollatzResearch.WordTrace]
  refine ⟨11944723948549021538159939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7963149299032681025439959 11944723948549021538159939)
  ·
    refine ⟨17917085922823532307239909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11944723948549021538159939 17917085922823532307239909)
    ·
      refine ⟨3359453610529412307607483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17917085922823532307239909 3359453610529412307607483)
      ·
        refine ⟨5039180415794118461411225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359453610529412307607483 5039180415794118461411225)
        ·
          refine ⟨3779385311845588846058419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5039180415794118461411225 3779385311845588846058419)
          ·
            refine ⟨5669077967768383269087629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779385311845588846058419 5669077967768383269087629)
            ·
              refine ⟨2125904237913143725907861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5669077967768383269087629 2125904237913143725907861)
              ·
                refine ⟨99651761152178612151931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2125904237913143725907861 99651761152178612151931)
                ·
                  rfl

theorem cell19_327495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_327495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327495 prefixEnd_327495 := by exact prefixLift 327495
  have htrace : WordTrace (prefixWord ++ tailWord_327495) baseStart_327495 baseEnd_327495 := by
    simpa [prefixWord, tailWord_327495, baseEnd_327495] using wordTrace_append hprefix tailTrace_327495
  have hstable : (prefixWord ++ tailWord_327495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327495).length < 2 ^ (prefixWord ++ tailWord_327495).sum := by decide
  have hdescent : baseEnd_327495 < baseStart_327495 := by decide
  rcases family_descends (prefixWord ++ tailWord_327495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327514 : List Nat := [3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_327514 : Nat := 118140960795 + 327514 * 2 ^ 59
def prefixEnd_327514 : Nat := 4983230072969 + 3 ^ 40 * 327514 * 2
def baseEnd_327514 : Nat := 99657542563992197729657

theorem tailTrace_327514 : CollatzResearch.WordTrace tailWord_327514 prefixEnd_327514 99657542563992197729657 := by
  unfold tailWord_327514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986354233870046945775399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7963611290320125188734397 2986354233870046945775399)
  ·
    refine ⟨4479531350805070418663099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2986354233870046945775399 4479531350805070418663099)
    ·
      refine ⟨6719297026207605627994649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4479531350805070418663099 6719297026207605627994649)
      ·
        refine ⟨5039472769655704220995987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6719297026207605627994649 5039472769655704220995987)
        ·
          refine ⟨7559209154483556331493981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039472769655704220995987 7559209154483556331493981)
          ·
            refine ⟨2834703432931333624310243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7559209154483556331493981 2834703432931333624310243)
            ·
              refine ⟨4252055149397000436465365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834703432931333624310243 4252055149397000436465365)
              ·
                refine ⟨99657542563992197729657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4252055149397000436465365 99657542563992197729657)
                ·
                  rfl

theorem cell19_327514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_327514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327514 prefixEnd_327514 := by exact prefixLift 327514
  have htrace : WordTrace (prefixWord ++ tailWord_327514) baseStart_327514 baseEnd_327514 := by
    simpa [prefixWord, tailWord_327514, baseEnd_327514] using wordTrace_append hprefix tailTrace_327514
  have hstable : (prefixWord ++ tailWord_327514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327514).length < 2 ^ (prefixWord ++ tailWord_327514).sum := by decide
  have hdescent : baseEnd_327514 < baseStart_327514 := by decide
  rcases family_descends (prefixWord ++ tailWord_327514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327609 : List Nat := [1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_327609 : Nat := 118140960795 + 327609 * 2 ^ 59
def prefixEnd_327609 : Nat := 4983230072969 + 3 ^ 40 * 327609 * 2
def baseEnd_327609 : Nat := 99686449623060125618287

theorem tailTrace_327609 : CollatzResearch.WordTrace tailWord_327609 prefixEnd_327609 99686449623060125618287 := by
  unfold tailWord_327609
  simp only [CollatzResearch.WordTrace]
  refine ⟨11948881870136019007809881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7965921246757346005206587 11948881870136019007809881)
  ·
    refine ⟨8961661402602014255857411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11948881870136019007809881 8961661402602014255857411)
    ·
      refine ⟨13442492103903021383786117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8961661402602014255857411 13442492103903021383786117)
      ·
        refine ⟨2520467269481816509459897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13442492103903021383786117 2520467269481816509459897)
        ·
          refine ⟨1890350452111362382094923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520467269481816509459897 1890350452111362382094923)
          ·
            refine ⟨2835525678167043573142385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890350452111362382094923 2835525678167043573142385)
            ·
              refine ⟨2126644258625282679856789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2835525678167043573142385 2126644258625282679856789)
              ·
                refine ⟨99686449623060125618287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2126644258625282679856789 99686449623060125618287)
                ·
                  rfl

theorem cell19_327609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_327609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327609 prefixEnd_327609 := by exact prefixLift 327609
  have htrace : WordTrace (prefixWord ++ tailWord_327609) baseStart_327609 baseEnd_327609 := by
    simpa [prefixWord, tailWord_327609, baseEnd_327609] using wordTrace_append hprefix tailTrace_327609
  have hstable : (prefixWord ++ tailWord_327609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327609).length < 2 ^ (prefixWord ++ tailWord_327609).sum := by decide
  have hdescent : baseEnd_327609 < baseStart_327609 := by decide
  rcases family_descends (prefixWord ++ tailWord_327609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327624 : List Nat := [2, 1, 3, 1, 4, 3, 2, 3]
def baseStart_327624 : Nat := 118140960795 + 327624 * 2 ^ 59
def prefixEnd_327624 : Nat := 4983230072969 + 3 ^ 40 * 327624 * 2
def baseEnd_327624 : Nat := 99691013895544535284913

theorem tailTrace_327624 : CollatzResearch.WordTrace tailWord_327624 prefixEnd_327624 99691013895544535284913 := by
  unfold tailWord_327624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974714482540838284802963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7966285976721117713070617 5974714482540838284802963)
  ·
    refine ⟨8962071723811257427204445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5974714482540838284802963 8962071723811257427204445)
    ·
      refine ⟨3360776896429221535201667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8962071723811257427204445 3360776896429221535201667)
      ·
        refine ⟨5041165344643832302802501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360776896429221535201667 5041165344643832302802501)
        ·
          refine ⟨945218502120718556775469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5041165344643832302802501 945218502120718556775469)
          ·
            refine ⟨354456938295269458790801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 945218502120718556775469 354456938295269458790801)
            ·
              refine ⟨265842703721452094093101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354456938295269458790801 265842703721452094093101)
              ·
                refine ⟨99691013895544535284913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265842703721452094093101 99691013895544535284913)
                ·
                  rfl

theorem cell19_327624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_327624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327624 prefixEnd_327624 := by exact prefixLift 327624
  have htrace : WordTrace (prefixWord ++ tailWord_327624) baseStart_327624 baseEnd_327624 := by
    simpa [prefixWord, tailWord_327624, baseEnd_327624] using wordTrace_append hprefix tailTrace_327624
  have hstable : (prefixWord ++ tailWord_327624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327624).length < 2 ^ (prefixWord ++ tailWord_327624).sum := by decide
  have hdescent : baseEnd_327624 < baseStart_327624 := by decide
  rcases family_descends (prefixWord ++ tailWord_327624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327626 : List Nat := [3, 1, 2, 1, 2, 1, 6, 3]
def baseStart_327626 : Nat := 118140960795 + 327626 * 2 ^ 59
def prefixEnd_327626 : Nat := 4983230072969 + 3 ^ 40 * 327626 * 2
def baseEnd_327626 : Nat := 99691622465209123240463

theorem tailTrace_327626 : CollatzResearch.WordTrace tailWord_327626 prefixEnd_327626 99691622465209123240463 := by
  unfold tailWord_327626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987375477768607727794683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7966334607382953940785821 2987375477768607727794683)
  ·
    refine ⟨4481063216652911591692025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2987375477768607727794683 4481063216652911591692025)
    ·
      refine ⟨3360797412489683693769019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4481063216652911591692025 3360797412489683693769019)
      ·
        refine ⟨5041196118734525540653529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360797412489683693769019 5041196118734525540653529)
        ·
          refine ⟨3780897089050894155490147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5041196118734525540653529 3780897089050894155490147)
          ·
            refine ⟨5671345633576341233235221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780897089050894155490147 5671345633576341233235221)
            ·
              refine ⟨265844326573890995307901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5671345633576341233235221 265844326573890995307901)
              ·
                refine ⟨99691622465209123240463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265844326573890995307901 99691622465209123240463)
                ·
                  rfl

theorem cell19_327626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_327626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327626 prefixEnd_327626 := by exact prefixLift 327626
  have htrace : WordTrace (prefixWord ++ tailWord_327626) baseStart_327626 baseEnd_327626 := by
    simpa [prefixWord, tailWord_327626, baseEnd_327626] using wordTrace_append hprefix tailTrace_327626
  have hstable : (prefixWord ++ tailWord_327626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327626).length < 2 ^ (prefixWord ++ tailWord_327626).sum := by decide
  have hdescent : baseEnd_327626 < baseStart_327626 := by decide
  rcases family_descends (prefixWord ++ tailWord_327626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327647 : List Nat := [1, 1, 2, 3, 4, 1, 7]
def baseStart_327647 : Nat := 118140960795 + 327647 * 2 ^ 59
def prefixEnd_327647 : Nat := 4983230072969 + 3 ^ 40 * 327647 * 2
def baseEnd_327647 : Nat := 33232670815562432257913

theorem tailTrace_327647 : CollatzResearch.WordTrace tailWord_327647 prefixEnd_327647 33232670815562432257913 := by
  unfold tailWord_327647
  simp only [CollatzResearch.WordTrace]
  refine ⟨11950267843998351497693195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7966845229332234331795463 11950267843998351497693195)
  ·
    refine ⟨17925401765997527246539793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11950267843998351497693195 17925401765997527246539793)
    ·
      refine ⟨13444051324498145434904845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17925401765997527246539793 13444051324498145434904845)
      ·
        refine ⟨5041519246686804538089317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13444051324498145434904845 5041519246686804538089317)
        ·
          refine ⟨945284858753775850891747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5041519246686804538089317 945284858753775850891747)
          ·
            refine ⟨1417927288130663776337621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945284858753775850891747 1417927288130663776337621)
            ·
              refine ⟨33232670815562432257913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1417927288130663776337621 33232670815562432257913)
              ·
                rfl

theorem cell19_327647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_327647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327647 prefixEnd_327647 := by exact prefixLift 327647
  have htrace : WordTrace (prefixWord ++ tailWord_327647) baseStart_327647 baseEnd_327647 := by
    simpa [prefixWord, tailWord_327647, baseEnd_327647] using wordTrace_append hprefix tailTrace_327647
  have hstable : (prefixWord ++ tailWord_327647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327647).length < 2 ^ (prefixWord ++ tailWord_327647).sum := by decide
  have hdescent : baseEnd_327647 < baseStart_327647 := by decide
  rcases family_descends (prefixWord ++ tailWord_327647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327685 : List Nat := [1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_327685 : Nat := 118140960795 + 327685 * 2 ^ 59
def prefixEnd_327685 : Nat := 4983230072969 + 3 ^ 40 * 327685 * 2
def baseEnd_327685 : Nat := 99709575270314467929191

theorem tailTrace_327685 : CollatzResearch.WordTrace tailWord_327685 prefixEnd_327685 99709575270314467929191 := by
  unfold tailWord_327685
  simp only [CollatzResearch.WordTrace]
  refine ⟨11951653817860683987576509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7967769211907122658384339 11951653817860683987576509)
  ·
    refine ⟨4481870181697756495341191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11951653817860683987576509 4481870181697756495341191)
    ·
      refine ⟨6722805272546634743011787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4481870181697756495341191 6722805272546634743011787)
      ·
        refine ⟨10084207908819952114517681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6722805272546634743011787 10084207908819952114517681)
        ·
          refine ⟨7563155931614964085888261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10084207908819952114517681 7563155931614964085888261)
          ·
            refine ⟨1418091737177805766104049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7563155931614964085888261 1418091737177805766104049)
            ·
              refine ⟨1063568802883354324578037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418091737177805766104049 1063568802883354324578037)
              ·
                refine ⟨99709575270314467929191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1063568802883354324578037 99709575270314467929191)
                ·
                  rfl

theorem cell19_327685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_327685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327685 prefixEnd_327685 := by exact prefixLift 327685
  have htrace : WordTrace (prefixWord ++ tailWord_327685) baseStart_327685 baseEnd_327685 := by
    simpa [prefixWord, tailWord_327685, baseEnd_327685] using wordTrace_append hprefix tailTrace_327685
  have hstable : (prefixWord ++ tailWord_327685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327685).length < 2 ^ (prefixWord ++ tailWord_327685).sum := by decide
  have hdescent : baseEnd_327685 < baseStart_327685 := by decide
  rcases family_descends (prefixWord ++ tailWord_327685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327700 : List Nat := [2, 4, 3, 2, 1, 7]
def baseStart_327700 : Nat := 118140960795 + 327700 * 2 ^ 59
def prefixEnd_327700 : Nat := 4983230072969 + 3 ^ 40 * 327700 * 2
def baseEnd_327700 : Nat := 11079348838088764177313

theorem tailTrace_327700 : CollatzResearch.WordTrace tailWord_327700 prefixEnd_327700 11079348838088764177313 := by
  unfold tailWord_327700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976100456403170774686277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7968133941870894366248369 5976100456403170774686277)
  ·
    refine ⟨1120518835575594520253677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5976100456403170774686277 1120518835575594520253677)
    ·
      refine ⟨420194563340847945095129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1120518835575594520253677 420194563340847945095129)
      ·
        refine ⟨315145922505635958821347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420194563340847945095129 315145922505635958821347)
        ·
          refine ⟨472718883758453938232021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315145922505635958821347 472718883758453938232021)
          ·
            refine ⟨11079348838088764177313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 472718883758453938232021 11079348838088764177313)
            ·
              rfl

theorem cell19_327700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 7].length) (baseStart_327700 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327700 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327700 prefixEnd_327700 := by exact prefixLift 327700
  have htrace : WordTrace (prefixWord ++ tailWord_327700) baseStart_327700 baseEnd_327700 := by
    simpa [prefixWord, tailWord_327700, baseEnd_327700] using wordTrace_append hprefix tailTrace_327700
  have hstable : (prefixWord ++ tailWord_327700).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327700).length < 2 ^ (prefixWord ++ tailWord_327700).sum := by decide
  have hdescent : baseEnd_327700 < baseStart_327700 := by decide
  rcases family_descends (prefixWord ++ tailWord_327700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327740 : List Nat := [2, 2, 2, 2, 2, 1, 5, 3]
def baseStart_327740 : Nat := 118140960795 + 327740 * 2 ^ 59
def prefixEnd_327740 : Nat := 4983230072969 + 3 ^ 40 * 327740 * 2
def baseEnd_327740 : Nat := 99726310936090636706819

theorem tailTrace_327740 : CollatzResearch.WordTrace tailWord_327740 prefixEnd_327740 99726310936090636706819 := by
  unfold tailWord_327740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976829916330714190414337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7969106555107618920552449 5976829916330714190414337)
  ·
    refine ⟨4482622437248035642810753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5976829916330714190414337 4482622437248035642810753)
    ·
      refine ⟨3361966827936026732108065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4482622437248035642810753 3361966827936026732108065)
      ·
        refine ⟨2521475120952020049081049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3361966827936026732108065 2521475120952020049081049)
        ·
          refine ⟨1891106340714015036810787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521475120952020049081049 1891106340714015036810787)
          ·
            refine ⟨2836659511071022555216181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891106340714015036810787 2836659511071022555216181)
            ·
              refine ⟨265936829162908364551517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2836659511071022555216181 265936829162908364551517)
              ·
                refine ⟨99726310936090636706819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265936829162908364551517 99726310936090636706819)
                ·
                  rfl

theorem cell19_327740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_327740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327740 prefixEnd_327740 := by exact prefixLift 327740
  have htrace : WordTrace (prefixWord ++ tailWord_327740) baseStart_327740 baseEnd_327740 := by
    simpa [prefixWord, tailWord_327740, baseEnd_327740] using wordTrace_append hprefix tailTrace_327740
  have hstable : (prefixWord ++ tailWord_327740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327740).length < 2 ^ (prefixWord ++ tailWord_327740).sum := by decide
  have hdescent : baseEnd_327740 < baseStart_327740 := by decide
  rcases family_descends (prefixWord ++ tailWord_327740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327799 : List Nat := [1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_327799 : Nat := 118140960795 + 327799 * 2 ^ 59
def prefixEnd_327799 : Nat := 4983230072969 + 3 ^ 40 * 327799 * 2
def baseEnd_327799 : Nat := 99744263741195981395547

theorem tailTrace_327799 : CollatzResearch.WordTrace tailWord_327799 prefixEnd_327799 99744263741195981395547 := by
  unfold tailWord_327799
  simp only [CollatzResearch.WordTrace]
  refine ⟨11955811739447681457226451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7970541159631787638150967 11955811739447681457226451)
  ·
    refine ⟨17933717609171522185839677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11955811739447681457226451 17933717609171522185839677)
    ·
      refine ⟨6725144103439320819689879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17933717609171522185839677 6725144103439320819689879)
      ·
        refine ⟨10087716155158981229534819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6725144103439320819689879 10087716155158981229534819)
        ·
          refine ⟨15131574232738471844302229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10087716155158981229534819 15131574232738471844302229)
          ·
            refine ⟨709292542159615867701667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15131574232738471844302229 709292542159615867701667)
            ·
              refine ⟨1063938813239423801552501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709292542159615867701667 1063938813239423801552501)
              ·
                refine ⟨99744263741195981395547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1063938813239423801552501 99744263741195981395547)
                ·
                  rfl

theorem cell19_327799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_327799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327799 prefixEnd_327799 := by exact prefixLift 327799
  have htrace : WordTrace (prefixWord ++ tailWord_327799) baseStart_327799 baseEnd_327799 := by
    simpa [prefixWord, tailWord_327799, baseEnd_327799] using wordTrace_append hprefix tailTrace_327799
  have hstable : (prefixWord ++ tailWord_327799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327799).length < 2 ^ (prefixWord ++ tailWord_327799).sum := by decide
  have hdescent : baseEnd_327799 < baseStart_327799 := by decide
  rcases family_descends (prefixWord ++ tailWord_327799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327816 : List Nat := [2, 1, 3, 4, 1, 3, 5]
def baseStart_327816 : Nat := 118140960795 + 327816 * 2 ^ 59
def prefixEnd_327816 : Nat := 4983230072969 + 3 ^ 40 * 327816 * 2
def baseEnd_327816 : Nat := 33249812194448326339241

theorem tailTrace_327816 : CollatzResearch.WordTrace tailWord_327816 prefixEnd_327816 33249812194448326339241 := by
  unfold tailWord_327816
  simp only [CollatzResearch.WordTrace]
  refine ⟨5978215890193046680297651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7970954520257395573730201 5978215890193046680297651)
  ·
    refine ⟨8967323835289570020446477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5978215890193046680297651 8967323835289570020446477)
    ·
      refine ⟨3362746438233588757667429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8967323835289570020446477 3362746438233588757667429)
      ·
        refine ⟨630514957168797892062643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3362746438233588757667429 630514957168797892062643)
        ·
          refine ⟨945772435753196838093965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630514957168797892062643 945772435753196838093965)
          ·
            refine ⟨354664663407448814285237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 945772435753196838093965 354664663407448814285237)
            ·
              refine ⟨33249812194448326339241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 354664663407448814285237 33249812194448326339241)
              ·
                rfl

theorem cell19_327816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_327816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327816 prefixEnd_327816 := by exact prefixLift 327816
  have htrace : WordTrace (prefixWord ++ tailWord_327816) baseStart_327816 baseEnd_327816 := by
    simpa [prefixWord, tailWord_327816, baseEnd_327816] using wordTrace_append hprefix tailTrace_327816
  have hstable : (prefixWord ++ tailWord_327816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327816).length < 2 ^ (prefixWord ++ tailWord_327816).sum := by decide
  have hdescent : baseEnd_327816 < baseStart_327816 := by decide
  rcases family_descends (prefixWord ++ tailWord_327816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327818 : List Nat := [3, 1, 2, 3, 1, 2, 7]
def baseStart_327818 : Nat := 118140960795 + 327818 * 2 ^ 59
def prefixEnd_327818 : Nat := 4983230072969 + 3 ^ 40 * 327818 * 2
def baseEnd_327818 : Nat := 33250015051003188991091

theorem tailTrace_327818 : CollatzResearch.WordTrace tailWord_327818 prefixEnd_327818 33250015051003188991091 := by
  unfold tailWord_327818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989126181594711925542027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7971003150919231801445405 2989126181594711925542027)
  ·
    refine ⟨4483689272392067888313041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2989126181594711925542027 4483689272392067888313041)
    ·
      refine ⟨3362766954294050916234781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4483689272392067888313041 3362766954294050916234781)
      ·
        refine ⟨1261037607860269093588043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3362766954294050916234781 1261037607860269093588043)
        ·
          refine ⟨1891556411790403640382065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261037607860269093588043 1891556411790403640382065)
          ·
            refine ⟨1418667308842802730286549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1891556411790403640382065 1418667308842802730286549)
            ·
              refine ⟨33250015051003188991091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1418667308842802730286549 33250015051003188991091)
              ·
                rfl

theorem cell19_327818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_327818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327818 prefixEnd_327818 := by exact prefixLift 327818
  have htrace : WordTrace (prefixWord ++ tailWord_327818) baseStart_327818 baseEnd_327818 := by
    simpa [prefixWord, tailWord_327818, baseEnd_327818] using wordTrace_append hprefix tailTrace_327818
  have hstable : (prefixWord ++ tailWord_327818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327818).length < 2 ^ (prefixWord ++ tailWord_327818).sum := by decide
  have hdescent : baseEnd_327818 < baseStart_327818 := by decide
  rcases family_descends (prefixWord ++ tailWord_327818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327837 : List Nat := [1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_327837 : Nat := 118140960795 + 327837 * 2 ^ 59
def prefixEnd_327837 : Nat := 4983230072969 + 3 ^ 40 * 327837 * 2
def baseEnd_327837 : Nat := 99755826564823152550999

theorem tailTrace_327837 : CollatzResearch.WordTrace tailWord_327837 prefixEnd_327837 99755826564823152550999 := by
  unfold tailWord_327837
  simp only [CollatzResearch.WordTrace]
  refine ⟨11957197713310013947109765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7971465142206675964739843 11957197713310013947109765)
  ·
    refine ⟨2241974571245627615083081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11957197713310013947109765 2241974571245627615083081)
    ·
      refine ⟨1681480928434220711312311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2241974571245627615083081 1681480928434220711312311)
      ·
        refine ⟨2522221392651331066968467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1681480928434220711312311 2522221392651331066968467)
        ·
          refine ⟨3783332088976996600452701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522221392651331066968467 3783332088976996600452701)
          ·
            refine ⟨1418749533366373725169763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3783332088976996600452701 1418749533366373725169763)
            ·
              refine ⟨2128124300049560587754645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418749533366373725169763 2128124300049560587754645)
              ·
                refine ⟨99755826564823152550999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2128124300049560587754645 99755826564823152550999)
                ·
                  rfl

theorem cell19_327837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_327837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327837 prefixEnd_327837 := by exact prefixLift 327837
  have htrace : WordTrace (prefixWord ++ tailWord_327837) baseStart_327837 baseEnd_327837 := by
    simpa [prefixWord, tailWord_327837, baseEnd_327837] using wordTrace_append hprefix tailTrace_327837
  have hstable : (prefixWord ++ tailWord_327837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327837).length < 2 ^ (prefixWord ++ tailWord_327837).sum := by decide
  have hdescent : baseEnd_327837 < baseStart_327837 := by decide
  rcases family_descends (prefixWord ++ tailWord_327837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327873 : List Nat := [1, 2, 6, 1, 2, 7]
def baseStart_327873 : Nat := 118140960795 + 327873 * 2 ^ 59
def prefixEnd_327873 : Nat := 4983230072969 + 3 ^ 40 * 327873 * 2
def baseEnd_327873 : Nat := 11085197868753970638989

theorem tailTrace_327873 : CollatzResearch.WordTrace tailWord_327873 prefixEnd_327873 11085197868753970638989 := by
  unfold tailWord_327873
  simp only [CollatzResearch.WordTrace]
  refine ⟨11958510741179592095420273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7972340494119728063613515 11958510741179592095420273)
  ·
    refine ⟨8968883055884694071565205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11958510741179592095420273 8968883055884694071565205)
    ·
      refine ⟨420416393244595034604619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8968883055884694071565205 420416393244595034604619)
      ·
        refine ⟨630624589866892551906929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420416393244595034604619 630624589866892551906929)
        ·
          refine ⟨472968442400169413930197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630624589866892551906929 472968442400169413930197)
          ·
            refine ⟨11085197868753970638989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 472968442400169413930197 11085197868753970638989)
            ·
              rfl

theorem cell19_327873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_327873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327873 prefixEnd_327873 := by exact prefixLift 327873
  have htrace : WordTrace (prefixWord ++ tailWord_327873) baseStart_327873 baseEnd_327873 := by
    simpa [prefixWord, tailWord_327873, baseEnd_327873] using wordTrace_append hprefix tailTrace_327873
  have hstable : (prefixWord ++ tailWord_327873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327873).length < 2 ^ (prefixWord ++ tailWord_327873).sum := by decide
  have hdescent : baseEnd_327873 < baseStart_327873 := by decide
  rcases family_descends (prefixWord ++ tailWord_327873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327932 : List Nat := [2, 2, 2, 1, 4, 2, 6]
def baseStart_327932 : Nat := 118140960795 + 327932 * 2 ^ 59
def prefixEnd_327932 : Nat := 4983230072969 + 3 ^ 40 * 327932 * 2
def baseEnd_327932 : Nat := 33261577874630360146543

theorem tailTrace_327932 : CollatzResearch.WordTrace tailWord_327932 prefixEnd_327932 33261577874630360146543 := by
  unfold tailWord_327932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980331323982922585909025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7973775098643896781212033 5980331323982922585909025)
  ·
    refine ⟨4485248492987191939431769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5980331323982922585909025 4485248492987191939431769)
    ·
      refine ⟨3363936369740393954573827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4485248492987191939431769 3363936369740393954573827)
      ·
        refine ⟨5045904554610590931860741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363936369740393954573827 5045904554610590931860741)
        ·
          refine ⟨946107103989485799723889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5045904554610590931860741 946107103989485799723889)
          ·
            refine ⟨709580327992114349792917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946107103989485799723889 709580327992114349792917)
            ·
              refine ⟨33261577874630360146543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 709580327992114349792917 33261577874630360146543)
              ·
                rfl

theorem cell19_327932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_327932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327932 prefixEnd_327932 := by exact prefixLift 327932
  have htrace : WordTrace (prefixWord ++ tailWord_327932) baseStart_327932 baseEnd_327932 := by
    simpa [prefixWord, tailWord_327932, baseEnd_327932] using wordTrace_append hprefix tailTrace_327932
  have hstable : (prefixWord ++ tailWord_327932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327932).length < 2 ^ (prefixWord ++ tailWord_327932).sum := by decide
  have hdescent : baseEnd_327932 < baseStart_327932 := by decide
  rcases family_descends (prefixWord ++ tailWord_327932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327966 : List Nat := [4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_327966 : Nat := 118140960795 + 327966 * 2 ^ 59
def prefixEnd_327966 : Nat := 4983230072969 + 3 ^ 40 * 327966 * 2
def baseEnd_327966 : Nat := 99795079308189075683981

theorem tailTrace_327966 : CollatzResearch.WordTrace tailWord_327966 prefixEnd_327966 99795079308189075683981 := by
  unfold tailWord_327966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495237841230333622319469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7974601819895112652370501 1495237841230333622319469)
  ·
    refine ⟨560714190461375108369801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1495237841230333622319469 560714190461375108369801)
    ·
      refine ⟨420535642846031331277351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 560714190461375108369801 420535642846031331277351)
      ·
        refine ⟨630803464269046996916027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420535642846031331277351 630803464269046996916027)
        ·
          refine ⟨946205196403570495374041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630803464269046996916027 946205196403570495374041)
          ·
            refine ⟨709653897302677871530531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946205196403570495374041 709653897302677871530531)
            ·
              refine ⟨1064480845954016807295797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709653897302677871530531 1064480845954016807295797)
              ·
                refine ⟨99795079308189075683981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1064480845954016807295797 99795079308189075683981)
                ·
                  rfl

theorem cell19_327966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_327966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327966 prefixEnd_327966 := by exact prefixLift 327966
  have htrace : WordTrace (prefixWord ++ tailWord_327966) baseStart_327966 baseEnd_327966 := by
    simpa [prefixWord, tailWord_327966, baseEnd_327966] using wordTrace_append hprefix tailTrace_327966
  have hstable : (prefixWord ++ tailWord_327966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327966).length < 2 ^ (prefixWord ++ tailWord_327966).sum := by decide
  have hdescent : baseEnd_327966 < baseStart_327966 := by decide
  rcases family_descends (prefixWord ++ tailWord_327966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327968 : List Nat := [2, 1, 1, 5, 2, 1, 4, 3]
def baseStart_327968 : Nat := 118140960795 + 327968 * 2 ^ 59
def prefixEnd_327968 : Nat := 4983230072969 + 3 ^ 40 * 327968 * 2
def baseEnd_327968 : Nat := 99795687877853663639531

theorem tailTrace_327968 : CollatzResearch.WordTrace tailWord_327968 prefixEnd_327968 99795687877853663639531 := by
  unfold tailWord_327968
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980987837917711660064279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7974650450556948880085705 5980987837917711660064279)
  ·
    refine ⟨8971481756876567490096419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5980987837917711660064279 8971481756876567490096419)
    ·
      refine ⟨13457222635314851235144629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8971481756876567490096419 13457222635314851235144629)
      ·
        refine ⟨1261614622060767303294809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13457222635314851235144629 1261614622060767303294809)
        ·
          refine ⟨946210966545575477471107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1261614622060767303294809 946210966545575477471107)
          ·
            refine ⟨1419316449818363216206661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946210966545575477471107 1419316449818363216206661)
            ·
              refine ⟨266121834340943103038749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1419316449818363216206661 266121834340943103038749)
              ·
                refine ⟨99795687877853663639531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266121834340943103038749 99795687877853663639531)
                ·
                  rfl

theorem cell19_327968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_327968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_327968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_327968 prefixEnd_327968 := by exact prefixLift 327968
  have htrace : WordTrace (prefixWord ++ tailWord_327968) baseStart_327968 baseEnd_327968 := by
    simpa [prefixWord, tailWord_327968, baseEnd_327968] using wordTrace_append hprefix tailTrace_327968
  have hstable : (prefixWord ++ tailWord_327968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327968).length < 2 ^ (prefixWord ++ tailWord_327968).sum := by decide
  have hdescent : baseEnd_327968 < baseStart_327968 := by decide
  rcases family_descends (prefixWord ++ tailWord_327968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328004 : List Nat := [2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_328004 : Nat := 118140960795 + 328004 * 2 ^ 59
def prefixEnd_328004 : Nat := 4983230072969 + 3 ^ 40 * 328004 * 2
def baseEnd_328004 : Nat := 99806642131816246839433

theorem tailTrace_328004 : CollatzResearch.WordTrace tailWord_328004 prefixEnd_328004 99806642131816246839433 := by
  unfold tailWord_328004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981644351852500734219533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7975525802470000978959377 5981644351852500734219533)
  ·
    refine ⟨2243116631944687775332325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5981644351852500734219533 2243116631944687775332325)
    ·
      refine ⟨420584368489628957874811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2243116631944687775332325 420584368489628957874811)
      ·
        refine ⟨630876552734443436812217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420584368489628957874811 630876552734443436812217)
        ·
          refine ⟨473157414550832577609163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630876552734443436812217 473157414550832577609163)
          ·
            refine ⟨709736121826248866413745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473157414550832577609163 709736121826248866413745)
            ·
              refine ⟨532302091369686649810309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709736121826248866413745 532302091369686649810309)
              ·
                refine ⟨99806642131816246839433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532302091369686649810309 99806642131816246839433)
                ·
                  rfl

theorem cell19_328004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_328004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328004 prefixEnd_328004 := by exact prefixLift 328004
  have htrace : WordTrace (prefixWord ++ tailWord_328004) baseStart_328004 baseEnd_328004 := by
    simpa [prefixWord, tailWord_328004, baseEnd_328004] using wordTrace_append hprefix tailTrace_328004
  have hstable : (prefixWord ++ tailWord_328004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328004).length < 2 ^ (prefixWord ++ tailWord_328004).sum := by decide
  have hdescent : baseEnd_328004 < baseStart_328004 := by decide
  rcases family_descends (prefixWord ++ tailWord_328004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328048 : List Nat := [2, 1, 1, 1, 4, 10]
def baseStart_328048 : Nat := 118140960795 + 328048 * 2 ^ 59
def prefixEnd_328048 : Nat := 4983230072969 + 3 ^ 40 * 328048 * 2
def baseEnd_328048 : Nat := 11091114518270797984615

theorem tailTrace_328048 : CollatzResearch.WordTrace tailWord_328048 prefixEnd_328048 11091114518270797984615 := by
  unfold tailWord_328048
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982446757772798491520399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7976595677030397988693865 5982446757772798491520399)
  ·
    refine ⟨8973670136659197737280599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5982446757772798491520399 8973670136659197737280599)
    ·
      refine ⟨13460505204988796605920899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8973670136659197737280599 13460505204988796605920899)
      ·
        refine ⟨20190757807483194908881349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13460505204988796605920899 20190757807483194908881349)
        ·
          refine ⟨3785767088903099045415253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20190757807483194908881349 3785767088903099045415253)
          ·
            refine ⟨11091114518270797984615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3785767088903099045415253 11091114518270797984615)
            ·
              rfl

theorem cell19_328048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_328048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328048 prefixEnd_328048 := by exact prefixLift 328048
  have htrace : WordTrace (prefixWord ++ tailWord_328048) baseStart_328048 baseEnd_328048 := by
    simpa [prefixWord, tailWord_328048, baseEnd_328048] using wordTrace_append hprefix tailTrace_328048
  have hstable : (prefixWord ++ tailWord_328048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328048).length < 2 ^ (prefixWord ++ tailWord_328048).sum := by decide
  have hdescent : baseEnd_328048 < baseStart_328048 := by decide
  rcases family_descends (prefixWord ++ tailWord_328048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328103 : List Nat := [1, 1, 6, 1, 1, 3, 6]
def baseStart_328103 : Nat := 118140960795 + 328103 * 2 ^ 59
def prefixEnd_328103 : Nat := 4983230072969 + 3 ^ 40 * 328103 * 2
def baseEnd_328103 : Nat := 33278922110071116879721

theorem tailTrace_328103 : CollatzResearch.WordTrace tailWord_328103 prefixEnd_328103 33278922110071116879721 := by
  unfold tailWord_328103
  simp only [CollatzResearch.WordTrace]
  refine ⟨11966899530346341376292963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7977933020230894250861975 11966899530346341376292963)
  ·
    refine ⟨17950349295519512064439445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11966899530346341376292963 17950349295519512064439445)
    ·
      refine ⟨841422623227477128020599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17950349295519512064439445 841422623227477128020599)
      ·
        refine ⟨1262133934841215692030899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841422623227477128020599 1262133934841215692030899)
        ·
          refine ⟨1893200902261823538046349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262133934841215692030899 1893200902261823538046349)
          ·
            refine ⟨709950338348183826767381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1893200902261823538046349 709950338348183826767381)
            ·
              refine ⟨33278922110071116879721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 709950338348183826767381 33278922110071116879721)
              ·
                rfl

theorem cell19_328103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_328103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328103 prefixEnd_328103 := by exact prefixLift 328103
  have htrace : WordTrace (prefixWord ++ tailWord_328103) baseStart_328103 baseEnd_328103 := by
    simpa [prefixWord, tailWord_328103, baseEnd_328103] using wordTrace_append hprefix tailTrace_328103
  have hstable : (prefixWord ++ tailWord_328103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328103).length < 2 ^ (prefixWord ++ tailWord_328103).sum := by decide
  have hdescent : baseEnd_328103 < baseStart_328103 := by decide
  rcases family_descends (prefixWord ++ tailWord_328103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328215 : List Nat := [1, 1, 3, 6, 2, 6]
def baseStart_328215 : Nat := 118140960795 + 328215 * 2 ^ 59
def prefixEnd_328215 : Nat := 4983230072969 + 3 ^ 40 * 328215 * 2
def baseEnd_328215 : Nat := 11096760692381141794441

theorem tailTrace_328215 : CollatzResearch.WordTrace tailWord_328215 prefixEnd_328215 11096760692381141794441 := by
  unfold tailWord_328215
  simp only [CollatzResearch.WordTrace]
  refine ⟨11970984505940584504370099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7980656337293723002913399 11970984505940584504370099)
  ·
    refine ⟨17956476758910876756555149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11970984505940584504370099 17956476758910876756555149)
    ·
      refine ⟨6733678784591578783708181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17956476758910876756555149 6733678784591578783708181)
      ·
        refine ⟨315641193027730255486321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6733678784591578783708181 315641193027730255486321)
        ·
          refine ⟨236730894770797691614741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315641193027730255486321 236730894770797691614741)
          ·
            refine ⟨11096760692381141794441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 236730894770797691614741 11096760692381141794441)
            ·
              rfl

theorem cell19_328215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 6].length) (baseStart_328215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328215 prefixEnd_328215 := by exact prefixLift 328215
  have htrace : WordTrace (prefixWord ++ tailWord_328215) baseStart_328215 baseEnd_328215 := by
    simpa [prefixWord, tailWord_328215, baseEnd_328215] using wordTrace_append hprefix tailTrace_328215
  have hstable : (prefixWord ++ tailWord_328215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328215).length < 2 ^ (prefixWord ++ tailWord_328215).sum := by decide
  have hdescent : baseEnd_328215 < baseStart_328215 := by decide
  rcases family_descends (prefixWord ++ tailWord_328215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328234 : List Nat := [3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_328234 : Nat := 118140960795 + 328234 * 2 ^ 59
def prefixEnd_328234 : Nat := 4983230072969 + 3 ^ 40 * 328234 * 2
def baseEnd_328234 : Nat := 99876627643243861727695

theorem tailTrace_328234 : CollatzResearch.WordTrace tailWord_328234 prefixEnd_328234 99876627643243861727695 := by
  unfold tailWord_328234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992919373217937687327939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7981118328581167166207837 2992919373217937687327939)
  ·
    refine ⟨4489379059826906530991909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2992919373217937687327939 4489379059826906530991909)
    ·
      refine ⟨841758573717544974560983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4489379059826906530991909 841758573717544974560983)
      ·
        refine ⟨1262637860576317461841475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841758573717544974560983 1262637860576317461841475)
        ·
          refine ⟨1893956790864476192762213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262637860576317461841475 1893956790864476192762213)
          ·
            refine ⟨355116898287089286142915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1893956790864476192762213 355116898287089286142915)
            ·
              refine ⟨532675347430633929214373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355116898287089286142915 532675347430633929214373)
              ·
                refine ⟨99876627643243861727695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532675347430633929214373 99876627643243861727695)
                ·
                  rfl

theorem cell19_328234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_328234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328234 prefixEnd_328234 := by exact prefixLift 328234
  have htrace : WordTrace (prefixWord ++ tailWord_328234) baseStart_328234 baseEnd_328234 := by
    simpa [prefixWord, tailWord_328234, baseEnd_328234] using wordTrace_append hprefix tailTrace_328234
  have hstable : (prefixWord ++ tailWord_328234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328234).length < 2 ^ (prefixWord ++ tailWord_328234).sum := by decide
  have hdescent : baseEnd_328234 < baseStart_328234 := by decide
  rcases family_descends (prefixWord ++ tailWord_328234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328253 : List Nat := [1, 4, 1, 3, 2, 2, 3, 3]
def baseStart_328253 : Nat := 118140960795 + 328253 * 2 ^ 59
def prefixEnd_328253 : Nat := 4983230072969 + 3 ^ 40 * 328253 * 2
def baseEnd_328253 : Nat := 99882409055057447305421

theorem tailTrace_328253 : CollatzResearch.WordTrace tailWord_328253 prefixEnd_328253 99882409055057447305421 := by
  unfold tailWord_328253
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972370479802916994253413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7981580319868611329502275 11972370479802916994253413)
  ·
    refine ⟨2244819464963046936422515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11972370479802916994253413 2244819464963046936422515)
    ·
      refine ⟨3367229197444570404633773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244819464963046936422515 3367229197444570404633773)
      ·
        refine ⟨1262710949041713901737665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3367229197444570404633773 1262710949041713901737665)
        ·
          refine ⟨947033211781285426303249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1262710949041713901737665 947033211781285426303249)
          ·
            refine ⟨710274908835964069727437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947033211781285426303249 710274908835964069727437)
            ·
              refine ⟨266353090813486526147789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710274908835964069727437 266353090813486526147789)
              ·
                refine ⟨99882409055057447305421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266353090813486526147789 99882409055057447305421)
                ·
                  rfl

theorem cell19_328253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_328253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328253 prefixEnd_328253 := by exact prefixLift 328253
  have htrace : WordTrace (prefixWord ++ tailWord_328253) baseStart_328253 baseEnd_328253 := by
    simpa [prefixWord, tailWord_328253, baseEnd_328253] using wordTrace_append hprefix tailTrace_328253
  have hstable : (prefixWord ++ tailWord_328253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328253).length < 2 ^ (prefixWord ++ tailWord_328253).sum := by decide
  have hdescent : baseEnd_328253 < baseStart_328253 := by decide
  rcases family_descends (prefixWord ++ tailWord_328253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328255 : List Nat := [1, 1, 2, 2, 3, 2, 5, 3]
def baseStart_328255 : Nat := 118140960795 + 328255 * 2 ^ 59
def prefixEnd_328255 : Nat := 4983230072969 + 3 ^ 40 * 328255 * 2
def baseEnd_328255 : Nat := 99883017624722035260971

theorem tailTrace_328255 : CollatzResearch.WordTrace tailWord_328255 prefixEnd_328255 99883017624722035260971 := by
  unfold tailWord_328255
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972443425795671335826219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7981628950530447557217479 11972443425795671335826219)
  ·
    refine ⟨17958665138693507003739329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11972443425795671335826219 17958665138693507003739329)
    ·
      refine ⟨13468998854020130252804497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17958665138693507003739329 13468998854020130252804497)
      ·
        refine ⟨10101749140515097689603373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13468998854020130252804497 10101749140515097689603373)
        ·
          refine ⟨3788155927693161633601265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10101749140515097689603373 3788155927693161633601265)
          ·
            refine ⟨2841116945769871225200949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3788155927693161633601265 2841116945769871225200949)
            ·
              refine ⟨266354713665925427362589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2841116945769871225200949 266354713665925427362589)
              ·
                refine ⟨99883017624722035260971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266354713665925427362589 99883017624722035260971)
                ·
                  rfl

theorem cell19_328255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_328255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328255 prefixEnd_328255 := by exact prefixLift 328255
  have htrace : WordTrace (prefixWord ++ tailWord_328255) baseStart_328255 baseEnd_328255 := by
    simpa [prefixWord, tailWord_328255, baseEnd_328255] using wordTrace_append hprefix tailTrace_328255
  have hstable : (prefixWord ++ tailWord_328255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328255).length < 2 ^ (prefixWord ++ tailWord_328255).sum := by decide
  have hdescent : baseEnd_328255 < baseStart_328255 := by decide
  rcases family_descends (prefixWord ++ tailWord_328255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328295 : List Nat := [1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_328295 : Nat := 118140960795 + 328295 * 2 ^ 59
def prefixEnd_328295 : Nat := 4983230072969 + 3 ^ 40 * 328295 * 2
def baseEnd_328295 : Nat := 99895189018013794371973

theorem tailTrace_328295 : CollatzResearch.WordTrace tailWord_328295 prefixEnd_328295 99895189018013794371973 := by
  unfold tailWord_328295
  simp only [CollatzResearch.WordTrace]
  refine ⟨11973902345650758167282339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7982601563767172111521559 11973902345650758167282339)
  ·
    refine ⟨17960853518476137250923509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11973902345650758167282339 17960853518476137250923509)
    ·
      refine ⟨1683830017357137867274079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17960853518476137250923509 1683830017357137867274079)
      ·
        refine ⟨2525745026035706800911119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683830017357137867274079 2525745026035706800911119)
        ·
          refine ⟨3788617539053560201366679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525745026035706800911119 3788617539053560201366679)
          ·
            refine ⟨5682926308580340302050019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788617539053560201366679 5682926308580340302050019)
            ·
              refine ⟨8524389462870510453075029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682926308580340302050019 8524389462870510453075029)
              ·
                refine ⟨99895189018013794371973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8524389462870510453075029 99895189018013794371973)
                ·
                  rfl

theorem cell19_328295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_328295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328295 prefixEnd_328295 := by exact prefixLift 328295
  have htrace : WordTrace (prefixWord ++ tailWord_328295) baseStart_328295 baseEnd_328295 := by
    simpa [prefixWord, tailWord_328295, baseEnd_328295] using wordTrace_append hprefix tailTrace_328295
  have hstable : (prefixWord ++ tailWord_328295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328295).length < 2 ^ (prefixWord ++ tailWord_328295).sum := by decide
  have hdescent : baseEnd_328295 < baseStart_328295 := by decide
  rcases family_descends (prefixWord ++ tailWord_328295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328310 : List Nat := [5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_328310 : Nat := 118140960795 + 328310 * 2 ^ 59
def prefixEnd_328310 : Nat := 4983230072969 + 3 ^ 40 * 328310 * 2
def baseEnd_328310 : Nat := 99899753290498204038599

theorem tailTrace_328310 : CollatzResearch.WordTrace tailWord_328310 prefixEnd_328310 99899753290498204038599 := by
  unfold tailWord_328310
  simp only [CollatzResearch.WordTrace]
  refine ⟨748403090037275983067399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7982966293730943819385589 748403090037275983067399)
  ·
    refine ⟨1122604635055913974601099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748403090037275983067399 1122604635055913974601099)
    ·
      refine ⟨1683906952583870961901649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122604635055913974601099 1683906952583870961901649)
      ·
        refine ⟨1262930214437903221426237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683906952583870961901649 1262930214437903221426237)
        ·
          refine ⟨473598830414213708034839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1262930214437903221426237 473598830414213708034839)
          ·
            refine ⟨710398245621320562052259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473598830414213708034839 710398245621320562052259)
            ·
              refine ⟨1065597368431980843078389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710398245621320562052259 1065597368431980843078389)
              ·
                refine ⟨99899753290498204038599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1065597368431980843078389 99899753290498204038599)
                ·
                  rfl

theorem cell19_328310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_328310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328310 prefixEnd_328310 := by exact prefixLift 328310
  have htrace : WordTrace (prefixWord ++ tailWord_328310) baseStart_328310 baseEnd_328310 := by
    simpa [prefixWord, tailWord_328310, baseEnd_328310] using wordTrace_append hprefix tailTrace_328310
  have hstable : (prefixWord ++ tailWord_328310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328310).length < 2 ^ (prefixWord ++ tailWord_328310).sum := by decide
  have hdescent : baseEnd_328310 < baseStart_328310 := by decide
  rcases family_descends (prefixWord ++ tailWord_328310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328371 : List Nat := [1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_328371 : Nat := 118140960795 + 328371 * 2 ^ 59
def prefixEnd_328371 : Nat := 4983230072969 + 3 ^ 40 * 328371 * 2
def baseEnd_328371 : Nat := 99918314665268136682877

theorem tailTrace_328371 : CollatzResearch.WordTrace tailWord_328371 prefixEnd_328371 99918314665268136682877 := by
  unfold tailWord_328371
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976674293375423147048967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7984449528916948764699311 11976674293375423147048967)
  ·
    refine ⟨17965011440063134720573451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11976674293375423147048967 17965011440063134720573451)
    ·
      refine ⟨26947517160094702080860177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17965011440063134720573451 26947517160094702080860177)
      ·
        refine ⟨20210637870071026560645133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26947517160094702080860177 20210637870071026560645133)
        ·
          refine ⟨7578989201276634960241925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20210637870071026560645133 7578989201276634960241925)
          ·
            refine ⟨1421060475239369055045361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7578989201276634960241925 1421060475239369055045361)
            ·
              refine ⟨1065795356429526791284021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421060475239369055045361 1065795356429526791284021)
              ·
                refine ⟨99918314665268136682877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1065795356429526791284021 99918314665268136682877)
                ·
                  rfl

theorem cell19_328371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_328371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328371 prefixEnd_328371 := by exact prefixLift 328371
  have htrace : WordTrace (prefixWord ++ tailWord_328371) baseStart_328371 baseEnd_328371 := by
    simpa [prefixWord, tailWord_328371, baseEnd_328371] using wordTrace_append hprefix tailTrace_328371
  have hstable : (prefixWord ++ tailWord_328371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328371).length < 2 ^ (prefixWord ++ tailWord_328371).sum := by decide
  have hdescent : baseEnd_328371 < baseStart_328371 := by decide
  rcases family_descends (prefixWord ++ tailWord_328371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328407 : List Nat := [1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_328407 : Nat := 118140960795 + 328407 * 2 ^ 59
def prefixEnd_328407 : Nat := 4983230072969 + 3 ^ 40 * 328407 * 2
def baseEnd_328407 : Nat := 99929268919230719882779

theorem tailTrace_328407 : CollatzResearch.WordTrace tailWord_328407 prefixEnd_328407 99929268919230719882779 := by
  unfold tailWord_328407
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977987321245001295359475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7985324880830000863572983 11977987321245001295359475)
  ·
    refine ⟨17966980981867501943039213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11977987321245001295359475 17966980981867501943039213)
    ·
      refine ⟨6737617868200313228639705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17966980981867501943039213 6737617868200313228639705)
      ·
        refine ⟨5053213401150234921479779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6737617868200313228639705 5053213401150234921479779)
        ·
          refine ⟨7579820101725352382219669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5053213401150234921479779 7579820101725352382219669)
          ·
            refine ⟨355304067268375892916547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7579820101725352382219669 355304067268375892916547)
            ·
              refine ⟨532956100902563839374821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355304067268375892916547 532956100902563839374821)
              ·
                refine ⟨99929268919230719882779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532956100902563839374821 99929268919230719882779)
                ·
                  rfl

theorem cell19_328407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_328407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328407 prefixEnd_328407 := by exact prefixLift 328407
  have htrace : WordTrace (prefixWord ++ tailWord_328407) baseStart_328407 baseEnd_328407 := by
    simpa [prefixWord, tailWord_328407, baseEnd_328407] using wordTrace_append hprefix tailTrace_328407
  have hstable : (prefixWord ++ tailWord_328407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328407).length < 2 ^ (prefixWord ++ tailWord_328407).sum := by decide
  have hdescent : baseEnd_328407 < baseStart_328407 := by decide
  rcases family_descends (prefixWord ++ tailWord_328407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328424 : List Nat := [2, 1, 4, 1, 4, 1, 3, 3]
def baseStart_328424 : Nat := 118140960795 + 328424 * 2 ^ 59
def prefixEnd_328424 : Nat := 4983230072969 + 3 ^ 40 * 328424 * 2
def baseEnd_328424 : Nat := 99934441761379717504955

theorem tailTrace_328424 : CollatzResearch.WordTrace tailWord_328424 prefixEnd_328424 99934441761379717504955 := by
  unfold tailWord_328424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989303681091706599364163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7985738241455608799152217 5989303681091706599364163)
  ·
    refine ⟨8983955521637559899046245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5989303681091706599364163 8983955521637559899046245)
    ·
      refine ⟨1684491660307042481071171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8983955521637559899046245 1684491660307042481071171)
      ·
        refine ⟨2526737490460563721606757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684491660307042481071171 2526737490460563721606757)
        ·
          refine ⟨473763279461355697801267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2526737490460563721606757 473763279461355697801267)
          ·
            refine ⟨710644919192033546701901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473763279461355697801267 710644919192033546701901)
            ·
              refine ⟨266491844697012580013213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710644919192033546701901 266491844697012580013213)
              ·
                refine ⟨99934441761379717504955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266491844697012580013213 99934441761379717504955)
                ·
                  rfl

theorem cell19_328424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_328424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328424 prefixEnd_328424 := by exact prefixLift 328424
  have htrace : WordTrace (prefixWord ++ tailWord_328424) baseStart_328424 baseEnd_328424 := by
    simpa [prefixWord, tailWord_328424, baseEnd_328424] using wordTrace_append hprefix tailTrace_328424
  have hstable : (prefixWord ++ tailWord_328424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328424).length < 2 ^ (prefixWord ++ tailWord_328424).sum := by decide
  have hdescent : baseEnd_328424 < baseStart_328424 := by decide
  rcases family_descends (prefixWord ++ tailWord_328424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328477 : List Nat := [1, 4, 2, 4, 2, 1, 2, 3]
def baseStart_328477 : Nat := 118140960795 + 328477 * 2 ^ 59
def prefixEnd_328477 : Nat := 4983230072969 + 3 ^ 40 * 328477 * 2
def baseEnd_328477 : Nat := 99950568857491298327033

theorem tailTrace_328477 : CollatzResearch.WordTrace tailWord_328477 prefixEnd_328477 99950568857491298327033 := by
  unfold tailWord_328477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980540430991403250407685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7987026953994268833605123 11980540430991403250407685)
  ·
    refine ⟨2246351330810888109451441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11980540430991403250407685 2246351330810888109451441)
    ·
      refine ⟨1684763498108166082088581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2246351330810888109451441 1684763498108166082088581)
      ·
        refine ⟨315893155895281140391609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1684763498108166082088581 315893155895281140391609)
        ·
          refine ⟨236919866921460855293707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315893155895281140391609 236919866921460855293707)
          ·
            refine ⟨355379800382191282940561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236919866921460855293707 355379800382191282940561)
            ·
              refine ⟨266534850286643462205421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355379800382191282940561 266534850286643462205421)
              ·
                refine ⟨99950568857491298327033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266534850286643462205421 99950568857491298327033)
                ·
                  rfl

theorem cell19_328477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_328477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328477 prefixEnd_328477 := by exact prefixLift 328477
  have htrace : WordTrace (prefixWord ++ tailWord_328477) baseStart_328477 baseEnd_328477 := by
    simpa [prefixWord, tailWord_328477, baseEnd_328477] using wordTrace_append hprefix tailTrace_328477
  have hstable : (prefixWord ++ tailWord_328477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328477).length < 2 ^ (prefixWord ++ tailWord_328477).sum := by decide
  have hdescent : baseEnd_328477 < baseStart_328477 := by decide
  rcases family_descends (prefixWord ++ tailWord_328477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328485 : List Nat := [1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_328485 : Nat := 118140960795 + 328485 * 2 ^ 59
def prefixEnd_328485 : Nat := 4983230072969 + 3 ^ 40 * 328485 * 2
def baseEnd_328485 : Nat := 99953003136149650149233

theorem tailTrace_328485 : CollatzResearch.WordTrace tailWord_328485 prefixEnd_328485 99953003136149650149233 := by
  unfold tailWord_328485
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980832214962420616698909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7987221476641613744465939 11980832214962420616698909)
  ·
    refine ⟨4492812080610907731262091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11980832214962420616698909 4492812080610907731262091)
    ·
      refine ⟨6739218120916361596893137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4492812080610907731262091 6739218120916361596893137)
      ·
        refine ⟨5054413590687271197669853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6739218120916361596893137 5054413590687271197669853)
        ·
          refine ⟨1895405096507726699126195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5054413590687271197669853 1895405096507726699126195)
          ·
            refine ⟨2843107644761590048689293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895405096507726699126195 2843107644761590048689293)
            ·
              refine ⟨1066165366785596268258485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2843107644761590048689293 1066165366785596268258485)
              ·
                refine ⟨99953003136149650149233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1066165366785596268258485 99953003136149650149233)
                ·
                  rfl

theorem cell19_328485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_328485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328485 prefixEnd_328485 := by exact prefixLift 328485
  have htrace : WordTrace (prefixWord ++ tailWord_328485) baseStart_328485 baseEnd_328485 := by
    simpa [prefixWord, tailWord_328485, baseEnd_328485] using wordTrace_append hprefix tailTrace_328485
  have hstable : (prefixWord ++ tailWord_328485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328485).length < 2 ^ (prefixWord ++ tailWord_328485).sum := by decide
  have hdescent : baseEnd_328485 < baseStart_328485 := by decide
  rcases family_descends (prefixWord ++ tailWord_328485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328500 : List Nat := [2, 5, 1, 1, 3, 2, 5]
def baseStart_328500 : Nat := 118140960795 + 328500 * 2 ^ 59
def prefixEnd_328500 : Nat := 4983230072969 + 3 ^ 40 * 328500 * 2
def baseEnd_328500 : Nat := 33319189136211353271953

theorem tailTrace_328500 : CollatzResearch.WordTrace tailWord_328500 prefixEnd_328500 33319189136211353271953 := by
  unfold tailWord_328500
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990689654954039089247477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7987586206605385452329969 5990689654954039089247477)
  ·
    refine ⟨561627155151941164616951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5990689654954039089247477 561627155151941164616951)
    ·
      refine ⟨842440732727911746925427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561627155151941164616951 842440732727911746925427)
      ·
        refine ⟨1263661099091867620388141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842440732727911746925427 1263661099091867620388141)
        ·
          refine ⟨473872912159450357645553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1263661099091867620388141 473872912159450357645553)
          ·
            refine ⟨355404684119587768234165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473872912159450357645553 355404684119587768234165)
            ·
              refine ⟨33319189136211353271953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 355404684119587768234165 33319189136211353271953)
              ·
                rfl

theorem cell19_328500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_328500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328500 prefixEnd_328500 := by exact prefixLift 328500
  have htrace : WordTrace (prefixWord ++ tailWord_328500) baseStart_328500 baseEnd_328500 := by
    simpa [prefixWord, tailWord_328500, baseEnd_328500] using wordTrace_append hprefix tailTrace_328500
  have hstable : (prefixWord ++ tailWord_328500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328500).length < 2 ^ (prefixWord ++ tailWord_328500).sum := by decide
  have hdescent : baseEnd_328500 < baseStart_328500 := by decide
  rcases family_descends (prefixWord ++ tailWord_328500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328540 : List Nat := [2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_328540 : Nat := 118140960795 + 328540 * 2 ^ 59
def prefixEnd_328540 : Nat := 4983230072969 + 3 ^ 40 * 328540 * 2
def baseEnd_328540 : Nat := 99969738801925818926861

theorem tailTrace_328540 : CollatzResearch.WordTrace tailWord_328540 prefixEnd_328540 99969738801925818926861 := by
  unfold tailWord_328540
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991419114881582504975537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7988558819842110006634049 5991419114881582504975537)
  ·
    refine ⟨4493564336161186878731653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5991419114881582504975537 4493564336161186878731653)
    ·
      refine ⟨842543313030222539762185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4493564336161186878731653 842543313030222539762185)
      ·
        refine ⟨631907484772666904821639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 842543313030222539762185 631907484772666904821639)
        ·
          refine ⟨947861227159000357232459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631907484772666904821639 947861227159000357232459)
          ·
            refine ⟨1421791840738500535848689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947861227159000357232459 1421791840738500535848689)
            ·
              refine ⟨1066343880553875401886517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421791840738500535848689 1066343880553875401886517)
              ·
                refine ⟨99969738801925818926861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1066343880553875401886517 99969738801925818926861)
                ·
                  rfl

theorem cell19_328540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_328540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328540 prefixEnd_328540 := by exact prefixLift 328540
  have htrace : WordTrace (prefixWord ++ tailWord_328540) baseStart_328540 baseEnd_328540 := by
    simpa [prefixWord, tailWord_328540, baseEnd_328540] using wordTrace_append hprefix tailTrace_328540
  have hstable : (prefixWord ++ tailWord_328540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328540).length < 2 ^ (prefixWord ++ tailWord_328540).sum := by decide
  have hdescent : baseEnd_328540 < baseStart_328540 := by decide
  rcases family_descends (prefixWord ++ tailWord_328540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328574 : List Nat := [4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_328574 : Nat := 118140960795 + 328574 * 2 ^ 59
def prefixEnd_328574 : Nat := 4983230072969 + 3 ^ 40 * 328574 * 2
def baseEnd_328574 : Nat := 99980084486223814171213

theorem tailTrace_328574 : CollatzResearch.WordTrace tailWord_328574 prefixEnd_328574 99980084486223814171213 := by
  unfold tailWord_328574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498009788954998602086097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7989385541093325877792517 1498009788954998602086097)
  ·
    refine ⟨1123507341716248951564573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1498009788954998602086097 1123507341716248951564573)
    ·
      refine ⟨421315253143593356836715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1123507341716248951564573 421315253143593356836715)
      ·
        refine ⟨631972879715390035255073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421315253143593356836715 631972879715390035255073)
        ·
          refine ⟨473979659786542526441305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631972879715390035255073 473979659786542526441305)
          ·
            refine ⟨355484744839906894830979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473979659786542526441305 355484744839906894830979)
            ·
              refine ⟨533227117259860342246469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355484744839906894830979 533227117259860342246469)
              ·
                refine ⟨99980084486223814171213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533227117259860342246469 99980084486223814171213)
                ·
                  rfl

theorem cell19_328574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_328574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328574 prefixEnd_328574 := by exact prefixLift 328574
  have htrace : WordTrace (prefixWord ++ tailWord_328574) baseStart_328574 baseEnd_328574 := by
    simpa [prefixWord, tailWord_328574, baseEnd_328574] using wordTrace_append hprefix tailTrace_328574
  have hstable : (prefixWord ++ tailWord_328574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328574).length < 2 ^ (prefixWord ++ tailWord_328574).sum := by decide
  have hdescent : baseEnd_328574 < baseStart_328574 := by decide
  rcases family_descends (prefixWord ++ tailWord_328574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328597 : List Nat := [1, 3, 2, 1, 1, 5, 3, 3]
def baseStart_328597 : Nat := 118140960795 + 328597 * 2 ^ 59
def prefixEnd_328597 : Nat := 4983230072969 + 3 ^ 40 * 328597 * 2
def baseEnd_328597 : Nat := 99987083037366575660039

theorem tailTrace_328597 : CollatzResearch.WordTrace tailWord_328597 prefixEnd_328597 99987083037366575660039 := by
  unfold tailWord_328597
  simp only [CollatzResearch.WordTrace]
  refine ⟨11984917190556663744776045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7989944793704442496517363 11984917190556663744776045)
  ·
    refine ⟨4494343946458748904291017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11984917190556663744776045 4494343946458748904291017)
    ·
      refine ⟨3370757959844061678218263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4494343946458748904291017 3370757959844061678218263)
      ·
        refine ⟨5056136939766092517327395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370757959844061678218263 5056136939766092517327395)
        ·
          refine ⟨7584205409649138775991093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056136939766092517327395 7584205409649138775991093)
          ·
            refine ⟨711019257154606760249165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7584205409649138775991093 711019257154606760249165)
            ·
              refine ⟨266632221432977535093437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711019257154606760249165 266632221432977535093437)
              ·
                refine ⟨99987083037366575660039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266632221432977535093437 99987083037366575660039)
                ·
                  rfl

theorem cell19_328597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_328597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328597 prefixEnd_328597 := by exact prefixLift 328597
  have htrace : WordTrace (prefixWord ++ tailWord_328597) baseStart_328597 baseEnd_328597 := by
    simpa [prefixWord, tailWord_328597, baseEnd_328597] using wordTrace_append hprefix tailTrace_328597
  have hstable : (prefixWord ++ tailWord_328597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328597).length < 2 ^ (prefixWord ++ tailWord_328597).sum := by decide
  have hdescent : baseEnd_328597 < baseStart_328597 := by decide
  rcases family_descends (prefixWord ++ tailWord_328597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328654 : List Nat := [4, 1, 1, 1, 2, 3, 4, 3]
def baseStart_328654 : Nat := 118140960795 + 328654 * 2 ^ 59
def prefixEnd_328654 : Nat := 4983230072969 + 3 ^ 40 * 328654 * 2
def baseEnd_328654 : Nat := 100004427272807332393217

theorem tailTrace_328654 : CollatzResearch.WordTrace tailWord_328654 prefixEnd_328654 100004427272807332393217 := by
  unfold tailWord_328654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498374518918770309950127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7991330767566774986400677 1498374518918770309950127)
  ·
    refine ⟨2247561778378155464925191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498374518918770309950127 2247561778378155464925191)
    ·
      refine ⟨3371342667567233197387787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2247561778378155464925191 3371342667567233197387787)
      ·
        refine ⟨5057014001350849796081681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371342667567233197387787 5057014001350849796081681)
        ·
          refine ⟨3792760501013137347061261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5057014001350849796081681 3792760501013137347061261)
          ·
            refine ⟨1422285187879926505147973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3792760501013137347061261 1422285187879926505147973)
            ·
              refine ⟨266678472727486219715245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1422285187879926505147973 266678472727486219715245)
              ·
                refine ⟨100004427272807332393217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266678472727486219715245 100004427272807332393217)
                ·
                  rfl

theorem cell19_328654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_328654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328654 prefixEnd_328654 := by exact prefixLift 328654
  have htrace : WordTrace (prefixWord ++ tailWord_328654) baseStart_328654 baseEnd_328654 := by
    simpa [prefixWord, tailWord_328654, baseEnd_328654] using wordTrace_append hprefix tailTrace_328654
  have hstable : (prefixWord ++ tailWord_328654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328654).length < 2 ^ (prefixWord ++ tailWord_328654).sum := by decide
  have hdescent : baseEnd_328654 < baseStart_328654 := by decide
  rcases family_descends (prefixWord ++ tailWord_328654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328690 : List Nat := [3, 2, 1, 5, 1, 1, 2, 4]
def baseStart_328690 : Nat := 118140960795 + 328690 * 2 ^ 59
def prefixEnd_328690 : Nat := 4983230072969 + 3 ^ 40 * 328690 * 2
def baseEnd_328690 : Nat := 100015381526769915593119

theorem tailTrace_328690 : CollatzResearch.WordTrace tailWord_328690 prefixEnd_328690 100015381526769915593119 := by
  unfold tailWord_328690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997077294804935156977881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7992206119479827085274349 2997077294804935156977881)
  ·
    refine ⟨2247807971103701367733411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2997077294804935156977881 2247807971103701367733411)
    ·
      refine ⟨3371711956655552051600117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2247807971103701367733411 3371711956655552051600117)
      ·
        refine ⟨316097995936458004837511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3371711956655552051600117 316097995936458004837511)
        ·
          refine ⟨474146993904687007256267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316097995936458004837511 474146993904687007256267)
          ·
            refine ⟨711220490857030510884401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474146993904687007256267 711220490857030510884401)
            ·
              refine ⟨533415368142772883163301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711220490857030510884401 533415368142772883163301)
              ·
                refine ⟨100015381526769915593119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533415368142772883163301 100015381526769915593119)
                ·
                  rfl

theorem cell19_328690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_328690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328690 prefixEnd_328690 := by exact prefixLift 328690
  have htrace : WordTrace (prefixWord ++ tailWord_328690) baseStart_328690 baseEnd_328690 := by
    simpa [prefixWord, tailWord_328690, baseEnd_328690] using wordTrace_append hprefix tailTrace_328690
  have hstable : (prefixWord ++ tailWord_328690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328690).length < 2 ^ (prefixWord ++ tailWord_328690).sum := by decide
  have hdescent : baseEnd_328690 < baseStart_328690 := by decide
  rcases family_descends (prefixWord ++ tailWord_328690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328732 : List Nat := [2, 2, 3, 1, 4, 7]
def baseStart_328732 : Nat := 118140960795 + 328732 * 2 ^ 59
def prefixEnd_328732 : Nat := 4983230072969 + 3 ^ 40 * 328732 * 2
def baseEnd_328732 : Nat := 11114240165525140295519

theorem tailTrace_328732 : CollatzResearch.WordTrace tailWord_328732 prefixEnd_328732 11114240165525140295519 := by
  unfold tailWord_328732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994920522533790900470225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7993227363378387867293633 5994920522533790900470225)
  ·
    refine ⟨4496190391900343175352669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5994920522533790900470225 4496190391900343175352669)
    ·
      refine ⟨1686071396962628690757251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4496190391900343175352669 1686071396962628690757251)
      ·
        refine ⟨2529107095443943036135877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686071396962628690757251 2529107095443943036135877)
        ·
          refine ⟨474207580395739319275477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2529107095443943036135877 474207580395739319275477)
          ·
            refine ⟨11114240165525140295519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 474207580395739319275477 11114240165525140295519)
            ·
              rfl

theorem cell19_328732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_328732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328732 prefixEnd_328732 := by exact prefixLift 328732
  have htrace : WordTrace (prefixWord ++ tailWord_328732) baseStart_328732 baseEnd_328732 := by
    simpa [prefixWord, tailWord_328732, baseEnd_328732] using wordTrace_append hprefix tailTrace_328732
  have hstable : (prefixWord ++ tailWord_328732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328732).length < 2 ^ (prefixWord ++ tailWord_328732).sum := by decide
  have hdescent : baseEnd_328732 < baseStart_328732 := by decide
  rcases family_descends (prefixWord ++ tailWord_328732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328766 : List Nat := [4, 2, 1, 3, 1, 2, 3, 3]
def baseStart_328766 : Nat := 118140960795 + 328766 * 2 ^ 59
def prefixEnd_328766 : Nat := 4983230072969 + 3 ^ 40 * 328766 * 2
def baseEnd_328766 : Nat := 100038507174024257904023

theorem tailTrace_328766 : CollatzResearch.WordTrace tailWord_328766 prefixEnd_328766 100038507174024257904023 := by
  unfold tailWord_328766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498885140868050700959769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7994054084629603738452101 1498885140868050700959769)
  ·
    refine ⟨1124163855651038025719827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1498885140868050700959769 1124163855651038025719827)
    ·
      refine ⟨1686245783476557038579741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1124163855651038025719827 1686245783476557038579741)
      ·
        refine ⟨632342168803708889467403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1686245783476557038579741 632342168803708889467403)
        ·
          refine ⟨948513253205563334201105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632342168803708889467403 948513253205563334201105)
          ·
            refine ⟨711384939904172500650829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948513253205563334201105 711384939904172500650829)
            ·
              refine ⟨266769352464064687744061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711384939904172500650829 266769352464064687744061)
              ·
                refine ⟨100038507174024257904023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266769352464064687744061 100038507174024257904023)
                ·
                  rfl

theorem cell19_328766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_328766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328766 prefixEnd_328766 := by exact prefixLift 328766
  have htrace : WordTrace (prefixWord ++ tailWord_328766) baseStart_328766 baseEnd_328766 := by
    simpa [prefixWord, tailWord_328766, baseEnd_328766] using wordTrace_append hprefix tailTrace_328766
  have hstable : (prefixWord ++ tailWord_328766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328766).length < 2 ^ (prefixWord ++ tailWord_328766).sum := by decide
  have hdescent : baseEnd_328766 < baseStart_328766 := by decide
  rcases family_descends (prefixWord ++ tailWord_328766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328821 : List Nat := [1, 3, 4, 3, 1, 2, 2, 3]
def baseStart_328821 : Nat := 118140960795 + 328821 * 2 ^ 59
def prefixEnd_328821 : Nat := 4983230072969 + 3 ^ 40 * 328821 * 2
def baseEnd_328821 : Nat := 100055242839800426681651

theorem tailTrace_328821 : CollatzResearch.WordTrace tailWord_328821 prefixEnd_328821 100055242839800426681651 := by
  unfold tailWord_328821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993087141745150000930317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7995391427830100000620211 11993087141745150000930317)
  ·
    refine ⟨4497407678154431250348869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11993087141745150000930317 4497407678154431250348869)
    ·
      refine ⟨843263939653955859440413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4497407678154431250348869 843263939653955859440413)
      ·
        refine ⟨316223977370233447290155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 843263939653955859440413 316223977370233447290155)
        ·
          refine ⟨474335966055350170935233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316223977370233447290155 474335966055350170935233)
          ·
            refine ⟨355751974541512628201425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474335966055350170935233 355751974541512628201425)
            ·
              refine ⟨266813980906134471151069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355751974541512628201425 266813980906134471151069)
              ·
                refine ⟨100055242839800426681651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266813980906134471151069 100055242839800426681651)
                ·
                  rfl

theorem cell19_328821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_328821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328821 prefixEnd_328821 := by exact prefixLift 328821
  have htrace : WordTrace (prefixWord ++ tailWord_328821) baseStart_328821 baseEnd_328821 := by
    simpa [prefixWord, tailWord_328821, baseEnd_328821] using wordTrace_append hprefix tailTrace_328821
  have hstable : (prefixWord ++ tailWord_328821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328821).length < 2 ^ (prefixWord ++ tailWord_328821).sum := by decide
  have hdescent : baseEnd_328821 < baseStart_328821 := by decide
  rcases family_descends (prefixWord ++ tailWord_328821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328846 : List Nat := [4, 1, 1, 3, 2, 1, 7]
def baseStart_328846 : Nat := 118140960795 + 328846 * 2 ^ 59
def prefixEnd_328846 : Nat := 4983230072969 + 3 ^ 40 * 328846 * 2
def baseEnd_328846 : Nat := 33354283320202592042009

theorem tailTrace_328846 : CollatzResearch.WordTrace tailWord_328846 prefixEnd_328846 33354283320202592042009 := by
  unfold tailWord_328846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499249870831822408823799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7995999311103052847060261 1499249870831822408823799)
  ·
    refine ⟨2248874806247733613235699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1499249870831822408823799 2248874806247733613235699)
    ·
      refine ⟨3373312209371600419853549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248874806247733613235699 3373312209371600419853549)
      ·
        refine ⟨1264992078514350157445081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3373312209371600419853549 1264992078514350157445081)
        ·
          refine ⟨948744058885762618083811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264992078514350157445081 948744058885762618083811)
          ·
            refine ⟨1423116088328643927125717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948744058885762618083811 1423116088328643927125717)
            ·
              refine ⟨33354283320202592042009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1423116088328643927125717 33354283320202592042009)
              ·
                rfl

theorem cell19_328846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_328846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328846 prefixEnd_328846 := by exact prefixLift 328846
  have htrace : WordTrace (prefixWord ++ tailWord_328846) baseStart_328846 baseEnd_328846 := by
    simpa [prefixWord, tailWord_328846, baseEnd_328846] using wordTrace_append hprefix tailTrace_328846
  have hstable : (prefixWord ++ tailWord_328846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328846).length < 2 ^ (prefixWord ++ tailWord_328846).sum := by decide
  have hdescent : baseEnd_328846 < baseStart_328846 := by decide
  rcases family_descends (prefixWord ++ tailWord_328846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328863 : List Nat := [1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_328863 : Nat := 118140960795 + 328863 * 2 ^ 59
def prefixEnd_328863 : Nat := 4983230072969 + 3 ^ 40 * 328863 * 2
def baseEnd_328863 : Nat := 100068022802756773748203

theorem tailTrace_328863 : CollatzResearch.WordTrace tailWord_328863 prefixEnd_328863 100068022802756773748203 := by
  unfold tailWord_328863
  simp only [CollatzResearch.WordTrace]
  refine ⟨11994619007592991173959243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7996412671728660782639495 11994619007592991173959243)
  ·
    refine ⟨17991928511389486760938865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11994619007592991173959243 17991928511389486760938865)
    ·
      refine ⟨13493946383542115070704149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17991928511389486760938865 13493946383542115070704149)
      ·
        refine ⟨632528736728536643939257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13493946383542115070704149 632528736728536643939257)
        ·
          refine ⟨474396552546402482954443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632528736728536643939257 474396552546402482954443)
          ·
            refine ⟨711594828819603724431665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474396552546402482954443 711594828819603724431665)
            ·
              refine ⟨533696121614702793323749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711594828819603724431665 533696121614702793323749)
              ·
                refine ⟨100068022802756773748203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533696121614702793323749 100068022802756773748203)
                ·
                  rfl

theorem cell19_328863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_328863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328863 prefixEnd_328863 := by exact prefixLift 328863
  have htrace : WordTrace (prefixWord ++ tailWord_328863) baseStart_328863 baseEnd_328863 := by
    simpa [prefixWord, tailWord_328863, baseEnd_328863] using wordTrace_append hprefix tailTrace_328863
  have hstable : (prefixWord ++ tailWord_328863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328863).length < 2 ^ (prefixWord ++ tailWord_328863).sum := by decide
  have hdescent : baseEnd_328863 < baseStart_328863 := by decide
  rcases family_descends (prefixWord ++ tailWord_328863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328865 : List Nat := [1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_328865 : Nat := 118140960795 + 328865 * 2 ^ 59
def prefixEnd_328865 : Nat := 4983230072969 + 3 ^ 40 * 328865 * 2
def baseEnd_328865 : Nat := 100068631372421361703753

theorem tailTrace_328865 : CollatzResearch.WordTrace tailWord_328865 prefixEnd_328865 100068631372421361703753 := by
  unfold tailWord_328865
  simp only [CollatzResearch.WordTrace]
  refine ⟨11994691953585745515532049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7996461302390497010354699 11994691953585745515532049)
  ·
    refine ⟨8996018965189309136649037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11994691953585745515532049 8996018965189309136649037)
    ·
      refine ⟨3373507111945990926243389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8996018965189309136649037 3373507111945990926243389)
      ·
        refine ⟨1265065166979746597341271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3373507111945990926243389 1265065166979746597341271)
        ·
          refine ⟨1897597750469619896011907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265065166979746597341271 1897597750469619896011907)
          ·
            refine ⟨2846396625704429844017861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897597750469619896011907 2846396625704429844017861)
            ·
              refine ⟨533699367319580595753349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2846396625704429844017861 533699367319580595753349)
              ·
                refine ⟨100068631372421361703753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533699367319580595753349 100068631372421361703753)
                ·
                  rfl

theorem cell19_328865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_328865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328865 prefixEnd_328865 := by exact prefixLift 328865
  have htrace : WordTrace (prefixWord ++ tailWord_328865) baseStart_328865 baseEnd_328865 := by
    simpa [prefixWord, tailWord_328865, baseEnd_328865] using wordTrace_append hprefix tailTrace_328865
  have hstable : (prefixWord ++ tailWord_328865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328865).length < 2 ^ (prefixWord ++ tailWord_328865).sum := by decide
  have hdescent : baseEnd_328865 < baseStart_328865 := by decide
  rcases family_descends (prefixWord ++ tailWord_328865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328916 : List Nat := [2, 4, 1, 4, 2, 1, 1, 4]
def baseStart_328916 : Nat := 118140960795 + 328916 * 2 ^ 59
def prefixEnd_328916 : Nat := 4983230072969 + 3 ^ 40 * 328916 * 2
def baseEnd_328916 : Nat := 100084149898868354570281

theorem tailTrace_328916 : CollatzResearch.WordTrace tailWord_328916 prefixEnd_328916 100084149898868354570281 := by
  unfold tailWord_328916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5998276038200490612819301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7997701384267320817092401 5998276038200490612819301)
  ·
    refine ⟨1124676757162591989903619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5998276038200490612819301 1124676757162591989903619)
    ·
      refine ⟨1687015135743887984855429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1124676757162591989903619 1687015135743887984855429)
      ·
        refine ⟨316315337951978997160393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1687015135743887984855429 316315337951978997160393)
        ·
          refine ⟨237236503463984247870295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316315337951978997160393 237236503463984247870295)
          ·
            refine ⟨355854755195976371805443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237236503463984247870295 355854755195976371805443)
            ·
              refine ⟨533782132793964557708165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355854755195976371805443 533782132793964557708165)
              ·
                refine ⟨100084149898868354570281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533782132793964557708165 100084149898868354570281)
                ·
                  rfl

theorem cell19_328916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_328916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328916 prefixEnd_328916 := by exact prefixLift 328916
  have htrace : WordTrace (prefixWord ++ tailWord_328916) baseStart_328916 baseEnd_328916 := by
    simpa [prefixWord, tailWord_328916, baseEnd_328916] using wordTrace_append hprefix tailTrace_328916
  have hstable : (prefixWord ++ tailWord_328916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328916).length < 2 ^ (prefixWord ++ tailWord_328916).sum := by decide
  have hdescent : baseEnd_328916 < baseStart_328916 := by decide
  rcases family_descends (prefixWord ++ tailWord_328916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328920 : List Nat := [2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_328920 : Nat := 118140960795 + 328920 * 2 ^ 59
def prefixEnd_328920 : Nat := 4983230072969 + 3 ^ 40 * 328920 * 2
def baseEnd_328920 : Nat := 100085367038197530481381

theorem tailTrace_328920 : CollatzResearch.WordTrace tailWord_328920 prefixEnd_328920 100085367038197530481381 := by
  unfold tailWord_328920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5998348984193244954392107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7997798645590993272522809 5998348984193244954392107)
  ·
    refine ⟨8997523476289867431588161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5998348984193244954392107 8997523476289867431588161)
    ·
      refine ⟨6748142607217400573691121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8997523476289867431588161 6748142607217400573691121)
      ·
        refine ⟨5061106955413050430268341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748142607217400573691121 5061106955413050430268341)
        ·
          refine ⟨474478777069973477837657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5061106955413050430268341 474478777069973477837657)
          ·
            refine ⟨355859082802480108378243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474478777069973477837657 355859082802480108378243)
            ·
              refine ⟨533788624203720162567365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355859082802480108378243 533788624203720162567365)
              ·
                refine ⟨100085367038197530481381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533788624203720162567365 100085367038197530481381)
                ·
                  rfl

theorem cell19_328920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_328920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328920 prefixEnd_328920 := by exact prefixLift 328920
  have htrace : WordTrace (prefixWord ++ tailWord_328920) baseStart_328920 baseEnd_328920 := by
    simpa [prefixWord, tailWord_328920, baseEnd_328920] using wordTrace_append hprefix tailTrace_328920
  have hstable : (prefixWord ++ tailWord_328920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328920).length < 2 ^ (prefixWord ++ tailWord_328920).sum := by decide
  have hdescent : baseEnd_328920 < baseStart_328920 := by decide
  rcases family_descends (prefixWord ++ tailWord_328920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328981 : List Nat := [1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_328981 : Nat := 118140960795 + 328981 * 2 ^ 59
def prefixEnd_328981 : Nat := 4983230072969 + 3 ^ 40 * 328981 * 2
def baseEnd_328981 : Nat := 100103928412967463125659

theorem tailTrace_328981 : CollatzResearch.WordTrace tailWord_328981 prefixEnd_328981 100103928412967463125659 := by
  unfold tailWord_328981
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998922821165497326754797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7999281880776998217836531 11998922821165497326754797)
  ·
    refine ⟨4499596057937061497533049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11998922821165497326754797 4499596057937061497533049)
    ·
      refine ⟨3374697043452796123149787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4499596057937061497533049 3374697043452796123149787)
      ·
        refine ⟨5062045565179194184724681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374697043452796123149787 5062045565179194184724681)
        ·
          refine ⟨3796534173884395638543511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5062045565179194184724681 3796534173884395638543511)
          ·
            refine ⟨5694801260826593457815267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796534173884395638543511 5694801260826593457815267)
            ·
              refine ⟨8542201891239890186722901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5694801260826593457815267 8542201891239890186722901)
              ·
                refine ⟨100103928412967463125659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8542201891239890186722901 100103928412967463125659)
                ·
                  rfl

theorem cell19_328981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_328981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328981 prefixEnd_328981 := by exact prefixLift 328981
  have htrace : WordTrace (prefixWord ++ tailWord_328981) baseStart_328981 baseEnd_328981 := by
    simpa [prefixWord, tailWord_328981, baseEnd_328981] using wordTrace_append hprefix tailTrace_328981
  have hstable : (prefixWord ++ tailWord_328981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328981).length < 2 ^ (prefixWord ++ tailWord_328981).sum := by decide
  have hdescent : baseEnd_328981 < baseStart_328981 := by decide
  rcases family_descends (prefixWord ++ tailWord_328981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328990 : List Nat := [4, 3, 2, 1, 3, 1, 2, 3]
def baseStart_328990 : Nat := 118140960795 + 328990 * 2 ^ 59
def prefixEnd_328990 : Nat := 4983230072969 + 3 ^ 40 * 328990 * 2
def baseEnd_328990 : Nat := 100106666976458108925635

theorem tailTrace_328990 : CollatzResearch.WordTrace tailWord_328990 prefixEnd_328990 100106666976458108925635 := by
  unfold tailWord_328990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499906384766611482979053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7999500718755261242554949 1499906384766611482979053)
  ·
    refine ⟨562464894287479306117145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1499906384766611482979053 562464894287479306117145)
    ·
      refine ⟨421848670715609479587859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562464894287479306117145 421848670715609479587859)
      ·
        refine ⟨632773006073414219381789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421848670715609479587859 632773006073414219381789)
        ·
          refine ⟨237289877277530332268171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632773006073414219381789 237289877277530332268171)
          ·
            refine ⟨355934815916295498402257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237289877277530332268171 355934815916295498402257)
            ·
              refine ⟨266951111937221623801693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355934815916295498402257 266951111937221623801693)
              ·
                refine ⟨100106666976458108925635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266951111937221623801693 100106666976458108925635)
                ·
                  rfl

theorem cell19_328990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_328990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328990 prefixEnd_328990 := by exact prefixLift 328990
  have htrace : WordTrace (prefixWord ++ tailWord_328990) baseStart_328990 baseEnd_328990 := by
    simpa [prefixWord, tailWord_328990, baseEnd_328990] using wordTrace_append hprefix tailTrace_328990
  have hstable : (prefixWord ++ tailWord_328990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328990).length < 2 ^ (prefixWord ++ tailWord_328990).sum := by decide
  have hdescent : baseEnd_328990 < baseStart_328990 := by decide
  rcases family_descends (prefixWord ++ tailWord_328990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328994 : List Nat := [3, 3, 1, 1, 4, 2, 2, 3]
def baseStart_328994 : Nat := 118140960795 + 328994 * 2 ^ 59
def prefixEnd_328994 : Nat := 4983230072969 + 3 ^ 40 * 328994 * 2
def baseEnd_328994 : Nat := 100107884115787284836735

theorem tailTrace_328994 : CollatzResearch.WordTrace tailWord_328994 prefixEnd_328994 100107884115787284836735 := by
  unfold tailWord_328994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999849242529600136744509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7999597980078933697985357 2999849242529600136744509)
  ·
    refine ⟨1124943465948600051279191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2999849242529600136744509 1124943465948600051279191)
    ·
      refine ⟨1687415198922900076918787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1124943465948600051279191 1687415198922900076918787)
      ·
        refine ⟨2531122798384350115378181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687415198922900076918787 2531122798384350115378181)
        ·
          refine ⟨474585524697065646633409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2531122798384350115378181 474585524697065646633409)
          ·
            refine ⟨355939143522799234975057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474585524697065646633409 355939143522799234975057)
            ·
              refine ⟨266954357642099426231293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355939143522799234975057 266954357642099426231293)
              ·
                refine ⟨100107884115787284836735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266954357642099426231293 100107884115787284836735)
                ·
                  rfl

theorem cell19_328994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_328994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_328994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_328994 prefixEnd_328994 := by exact prefixLift 328994
  have htrace : WordTrace (prefixWord ++ tailWord_328994) baseStart_328994 baseEnd_328994 := by
    simpa [prefixWord, tailWord_328994, baseEnd_328994] using wordTrace_append hprefix tailTrace_328994
  have hstable : (prefixWord ++ tailWord_328994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328994).length < 2 ^ (prefixWord ++ tailWord_328994).sum := by decide
  have hdescent : baseEnd_328994 < baseStart_328994 := by decide
  rcases family_descends (prefixWord ++ tailWord_328994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329030 : List Nat := [6, 1, 1, 3, 1, 1, 2, 4]
def baseStart_329030 : Nat := 118140960795 + 329030 * 2 ^ 59
def prefixEnd_329030 : Nat := 4983230072969 + 3 ^ 40 * 329030 * 2
def baseEnd_329030 : Nat := 100118838369749868036637

theorem tailTrace_329030 : CollatzResearch.WordTrace tailWord_329030 prefixEnd_329030 100118838369749868036637 := by
  unfold tailWord_329030
  simp only [CollatzResearch.WordTrace]
  refine ⟨375022187437124334227767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8000473331991985796859029 375022187437124334227767)
  ·
    refine ⟨562533281155686501341651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 375022187437124334227767 562533281155686501341651)
    ·
      refine ⟨843799921733529752012477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562533281155686501341651 843799921733529752012477)
      ·
        refine ⟨316424970650073657004679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 843799921733529752012477 316424970650073657004679)
        ·
          refine ⟨474637455975110485507019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316424970650073657004679 474637455975110485507019)
          ·
            refine ⟨711956183962665728260529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474637455975110485507019 711956183962665728260529)
            ·
              refine ⟨533967137971999296195397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711956183962665728260529 533967137971999296195397)
              ·
                refine ⟨100118838369749868036637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533967137971999296195397 100118838369749868036637)
                ·
                  rfl

theorem cell19_329030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_329030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329030 prefixEnd_329030 := by exact prefixLift 329030
  have htrace : WordTrace (prefixWord ++ tailWord_329030) baseStart_329030 baseEnd_329030 := by
    simpa [prefixWord, tailWord_329030, baseEnd_329030] using wordTrace_append hprefix tailTrace_329030
  have hstable : (prefixWord ++ tailWord_329030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329030).length < 2 ^ (prefixWord ++ tailWord_329030).sum := by decide
  have hdescent : baseEnd_329030 < baseStart_329030 := by decide
  rcases family_descends (prefixWord ++ tailWord_329030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329036 : List Nat := [2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_329036 : Nat := 118140960795 + 329036 * 2 ^ 59
def prefixEnd_329036 : Nat := 4983230072969 + 3 ^ 40 * 329036 * 2
def baseEnd_329036 : Nat := 100120664078743631903287

theorem tailTrace_329036 : CollatzResearch.WordTrace tailWord_329036 prefixEnd_329036 100120664078743631903287 := by
  unfold tailWord_329036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000464417983120860003481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8000619223977494480004641 6000464417983120860003481)
  ·
    refine ⟨4500348313487340645002611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6000464417983120860003481 4500348313487340645002611)
    ·
      refine ⟨6750522470231010967503917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500348313487340645002611 6750522470231010967503917)
      ·
        refine ⟨2531445926336629112813969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6750522470231010967503917 2531445926336629112813969)
        ·
          refine ⟨1898584444752471834610477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2531445926336629112813969 1898584444752471834610477)
          ·
            refine ⟨711969166782176937978929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1898584444752471834610477 711969166782176937978929)
            ·
              refine ⟨533976875086632703484197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711969166782176937978929 533976875086632703484197)
              ·
                refine ⟨100120664078743631903287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533976875086632703484197 100120664078743631903287)
                ·
                  rfl

theorem cell19_329036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_329036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329036 prefixEnd_329036 := by exact prefixLift 329036
  have htrace : WordTrace (prefixWord ++ tailWord_329036) baseStart_329036 baseEnd_329036 := by
    simpa [prefixWord, tailWord_329036, baseEnd_329036] using wordTrace_append hprefix tailTrace_329036
  have hstable : (prefixWord ++ tailWord_329036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329036).length < 2 ^ (prefixWord ++ tailWord_329036).sum := by decide
  have hdescent : baseEnd_329036 < baseStart_329036 := by decide
  rcases family_descends (prefixWord ++ tailWord_329036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329089 : List Nat := [1, 2, 4, 3, 3, 1, 1, 4]
def baseStart_329089 : Nat := 118140960795 + 329089 * 2 ^ 59
def prefixEnd_329089 : Nat := 4983230072969 + 3 ^ 40 * 329089 * 2
def baseEnd_329089 : Nat := 100136791174855212725365

theorem tailTrace_329089 : CollatzResearch.WordTrace tailWord_329089 prefixEnd_329089 100136791174855212725365 := by
  unfold tailWord_329089
  simp only [CollatzResearch.WordTrace]
  refine ⟨12002861904774231771686321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8001907936516154514457547 12002861904774231771686321)
  ·
    refine ⟨9002146428580673828764741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12002861904774231771686321 9002146428580673828764741)
    ·
      refine ⟨1687902455358876342893389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9002146428580673828764741 1687902455358876342893389)
      ·
        refine ⟨632963420759578628585021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1687902455358876342893389 632963420759578628585021)
        ·
          refine ⟨237361282784841985719383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632963420759578628585021 237361282784841985719383)
          ·
            refine ⟨356041924177262978579075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237361282784841985719383 356041924177262978579075)
            ·
              refine ⟨534062886265894467868613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356041924177262978579075 534062886265894467868613)
              ·
                refine ⟨100136791174855212725365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 534062886265894467868613 100136791174855212725365)
                ·
                  rfl

theorem cell19_329089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_329089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329089 prefixEnd_329089 := by exact prefixLift 329089
  have htrace : WordTrace (prefixWord ++ tailWord_329089) baseStart_329089 baseEnd_329089 := by
    simpa [prefixWord, tailWord_329089, baseEnd_329089] using wordTrace_append hprefix tailTrace_329089
  have hstable : (prefixWord ++ tailWord_329089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329089).length < 2 ^ (prefixWord ++ tailWord_329089).sum := by decide
  have hdescent : baseEnd_329089 < baseStart_329089 := by decide
  rcases family_descends (prefixWord ++ tailWord_329089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329205 : List Nat := [1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_329205 : Nat := 118140960795 + 329205 * 2 ^ 59
def prefixEnd_329205 : Nat := 4983230072969 + 3 ^ 40 * 329205 * 2
def baseEnd_329205 : Nat := 100172088215401314147271

theorem tailTrace_329205 : CollatzResearch.WordTrace tailWord_329205 prefixEnd_329205 100172088215401314147271 := by
  unfold tailWord_329205
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007092772353983582909069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8004728514902655721939379 12007092772353983582909069)
  ·
    refine ⟨4502659789632743843590901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12007092772353983582909069 4502659789632743843590901)
    ·
      refine ⟨422124355278069735336647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4502659789632743843590901 422124355278069735336647)
      ·
        refine ⟨633186532917104603004971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422124355278069735336647 633186532917104603004971)
        ·
          refine ⟨949779799375656904507457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633186532917104603004971 949779799375656904507457)
          ·
            refine ⟨712334849531742678380593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 949779799375656904507457 712334849531742678380593)
            ·
              refine ⟨534251137148807008785445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712334849531742678380593 534251137148807008785445)
              ·
                refine ⟨100172088215401314147271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 534251137148807008785445 100172088215401314147271)
                ·
                  rfl

theorem cell19_329205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_329205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329205 prefixEnd_329205 := by exact prefixLift 329205
  have htrace : WordTrace (prefixWord ++ tailWord_329205) baseStart_329205 baseEnd_329205 := by
    simpa [prefixWord, tailWord_329205, baseEnd_329205] using wordTrace_append hprefix tailTrace_329205
  have hstable : (prefixWord ++ tailWord_329205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329205).length < 2 ^ (prefixWord ++ tailWord_329205).sum := by decide
  have hdescent : baseEnd_329205 < baseStart_329205 := by decide
  rcases family_descends (prefixWord ++ tailWord_329205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329262 : List Nat := [4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_329262 : Nat := 118140960795 + 329262 * 2 ^ 59
def prefixEnd_329262 : Nat := 4983230072969 + 3 ^ 40 * 329262 * 2
def baseEnd_329262 : Nat := 100189432450842070880449

theorem tailTrace_329262 : CollatzResearch.WordTrace tailWord_329262 prefixEnd_329262 100189432450842070880449 := by
  unfold tailWord_329262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501146466643435289716755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8006114488764988211822693 1501146466643435289716755)
  ·
    refine ⟨2251719699965152934575133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1501146466643435289716755 2251719699965152934575133)
    ·
      refine ⟨844394887486932350465675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2251719699965152934575133 844394887486932350465675)
      ·
        refine ⟨1266592331230398525698513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844394887486932350465675 1266592331230398525698513)
        ·
          refine ⟨949944248422798894273885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266592331230398525698513 949944248422798894273885)
          ·
            refine ⟨356229093158549585352707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 949944248422798894273885 356229093158549585352707)
            ·
              refine ⟨534343639737824378029061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356229093158549585352707 534343639737824378029061)
              ·
                refine ⟨100189432450842070880449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 534343639737824378029061 100189432450842070880449)
                ·
                  rfl

theorem cell19_329262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_329262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329262 prefixEnd_329262 := by exact prefixLift 329262
  have htrace : WordTrace (prefixWord ++ tailWord_329262) baseStart_329262 baseEnd_329262 := by
    simpa [prefixWord, tailWord_329262, baseEnd_329262] using wordTrace_append hprefix tailTrace_329262
  have hstable : (prefixWord ++ tailWord_329262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329262).length < 2 ^ (prefixWord ++ tailWord_329262).sum := by decide
  have hdescent : baseEnd_329262 < baseStart_329262 := by decide
  rcases family_descends (prefixWord ++ tailWord_329262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329380 : List Nat := [2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_329380 : Nat := 118140960795 + 329380 * 2 ^ 59
def prefixEnd_329380 : Nat := 4983230072969 + 3 ^ 40 * 329380 * 2
def baseEnd_329380 : Nat := 100225338061052760257905

theorem tailTrace_329380 : CollatzResearch.WordTrace tailWord_329380 prefixEnd_329380 100225338061052760257905 := by
  unfold tailWord_329380
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006737773359994235264797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8008983697813325647019729 6006737773359994235264797)
  ·
    refine ⟨2252526665009997838224299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6006737773359994235264797 2252526665009997838224299)
    ·
      refine ⟨3378789997514996757336449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252526665009997838224299 3378789997514996757336449)
      ·
        refine ⟨2534092498136247568002337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3378789997514996757336449 2534092498136247568002337)
        ·
          refine ⟨1900569373602185676001753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2534092498136247568002337 1900569373602185676001753)
          ·
            refine ⟨1425427030201639257001315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1900569373602185676001753 1425427030201639257001315)
            ·
              refine ⟨2138140545302458885501973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425427030201639257001315 2138140545302458885501973)
              ·
                refine ⟨100225338061052760257905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2138140545302458885501973 100225338061052760257905)
                ·
                  rfl

theorem cell19_329380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_329380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329380 prefixEnd_329380 := by exact prefixLift 329380
  have htrace : WordTrace (prefixWord ++ tailWord_329380) baseStart_329380 baseEnd_329380 := by
    simpa [prefixWord, tailWord_329380, baseEnd_329380] using wordTrace_append hprefix tailTrace_329380
  have hstable : (prefixWord ++ tailWord_329380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329380).length < 2 ^ (prefixWord ++ tailWord_329380).sum := by decide
  have hdescent : baseEnd_329380 < baseStart_329380 := by decide
  rcases family_descends (prefixWord ++ tailWord_329380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329399 : List Nat := [1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_329399 : Nat := 118140960795 + 329399 * 2 ^ 59
def prefixEnd_329399 : Nat := 4983230072969 + 3 ^ 40 * 329399 * 2
def baseEnd_329399 : Nat := 100231119472866345835631

theorem tailTrace_329399 : CollatzResearch.WordTrace tailWord_329399 prefixEnd_329399 100231119472866345835631 := by
  unfold tailWord_329399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12014168533651154715471251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8009445689100769810314167 12014168533651154715471251)
  ·
    refine ⟨18021252800476732073206877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12014168533651154715471251 18021252800476732073206877)
    ·
      refine ⟨6757969800178774527452579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18021252800476732073206877 6757969800178774527452579)
      ·
        refine ⟨10136954700268161791178869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6757969800178774527452579 10136954700268161791178869)
        ·
          refine ⟨950339503150140167923019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10136954700268161791178869 950339503150140167923019)
          ·
            refine ⟨1425509254725210251884529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950339503150140167923019 1425509254725210251884529)
            ·
              refine ⟨1069131941043907688913397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425509254725210251884529 1069131941043907688913397)
              ·
                refine ⟨100231119472866345835631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1069131941043907688913397 100231119472866345835631)
                ·
                  rfl

theorem cell19_329399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_329399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329399 prefixEnd_329399 := by exact prefixLift 329399
  have htrace : WordTrace (prefixWord ++ tailWord_329399) baseStart_329399 baseEnd_329399 := by
    simpa [prefixWord, tailWord_329399, baseEnd_329399] using wordTrace_append hprefix tailTrace_329399
  have hstable : (prefixWord ++ tailWord_329399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329399).length < 2 ^ (prefixWord ++ tailWord_329399).sum := by decide
  have hdescent : baseEnd_329399 < baseStart_329399 := by decide
  rcases family_descends (prefixWord ++ tailWord_329399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329414 : List Nat := [6, 1, 2, 1, 1, 8]
def baseStart_329414 : Nat := 118140960795 + 329414 * 2 ^ 59
def prefixEnd_329414 : Nat := 4983230072969 + 3 ^ 40 * 329414 * 2
def baseEnd_329414 : Nat := 11137298193927861722473

theorem tailTrace_329414 : CollatzResearch.WordTrace tailWord_329414 prefixEnd_329414 11137298193927861722473 := by
  unfold tailWord_329414
  simp only [CollatzResearch.WordTrace]
  refine ⟨375459863393650383664603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8009810419064541518178197 375459863393650383664603)
  ·
    refine ⟨563189795090475575496905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 375459863393650383664603 563189795090475575496905)
    ·
      refine ⟨422392346317856681622679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 563189795090475575496905 422392346317856681622679)
      ·
        refine ⟨633588519476785022434019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422392346317856681622679 633588519476785022434019)
        ·
          refine ⟨950382779215177533651029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633588519476785022434019 950382779215177533651029)
          ·
            refine ⟨11137298193927861722473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 950382779215177533651029 11137298193927861722473)
            ·
              rfl

theorem cell19_329414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_329414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329414 prefixEnd_329414 := by exact prefixLift 329414
  have htrace : WordTrace (prefixWord ++ tailWord_329414) baseStart_329414 baseEnd_329414 := by
    simpa [prefixWord, tailWord_329414, baseEnd_329414] using wordTrace_append hprefix tailTrace_329414
  have hstable : (prefixWord ++ tailWord_329414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329414).length < 2 ^ (prefixWord ++ tailWord_329414).sum := by decide
  have hdescent : baseEnd_329414 < baseStart_329414 := by decide
  rcases family_descends (prefixWord ++ tailWord_329414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329418 : List Nat := [3, 1, 2, 1, 5, 7]
def baseStart_329418 : Nat := 118140960795 + 329418 * 2 ^ 59
def prefixEnd_329418 : Nat := 4983230072969 + 3 ^ 40 * 329418 * 2
def baseEnd_329418 : Nat := 11137433431631103490373

theorem tailTrace_329418 : CollatzResearch.WordTrace tailWord_329418 prefixEnd_329418 11137433431631103490373 := by
  unfold tailWord_329418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003715380145580240103227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8009907680388213973608605 3003715380145580240103227)
  ·
    refine ⟨4505573070218370360154841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3003715380145580240103227 4505573070218370360154841)
    ·
      refine ⟨3379179802663777770116131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4505573070218370360154841 3379179802663777770116131)
      ·
        refine ⟨5068769703995666655174197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379179802663777770116131 5068769703995666655174197)
        ·
          refine ⟨475197159749593748922581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5068769703995666655174197 475197159749593748922581)
          ·
            refine ⟨11137433431631103490373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 475197159749593748922581 11137433431631103490373)
            ·
              rfl

theorem cell19_329418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_329418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329418 prefixEnd_329418 := by exact prefixLift 329418
  have htrace : WordTrace (prefixWord ++ tailWord_329418) baseStart_329418 baseEnd_329418 := by
    simpa [prefixWord, tailWord_329418, baseEnd_329418] using wordTrace_append hprefix tailTrace_329418
  have hstable : (prefixWord ++ tailWord_329418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329418).length < 2 ^ (prefixWord ++ tailWord_329418).sum := by decide
  have hdescent : baseEnd_329418 < baseStart_329418 := by decide
  rcases family_descends (prefixWord ++ tailWord_329418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329454 : List Nat := [4, 1, 2, 1, 1, 2, 5, 3]
def baseStart_329454 : Nat := 118140960795 + 329454 * 2 ^ 59
def prefixEnd_329454 : Nat := 4983230072969 + 3 ^ 40 * 329454 * 2
def baseEnd_329454 : Nat := 100247855138642514613259

theorem tailTrace_329454 : CollatzResearch.WordTrace tailWord_329454 prefixEnd_329454 100247855138642514613259 := by
  unfold tailWord_329454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502021818556487388590427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8010783032301266072482277 1502021818556487388590427)
  ·
    refine ⟨2253032727834731082885641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1502021818556487388590427 2253032727834731082885641)
    ·
      refine ⟨1689774545876048312164231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2253032727834731082885641 1689774545876048312164231)
      ·
        refine ⟨2534661818814072468246347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689774545876048312164231 2534661818814072468246347)
        ·
          refine ⟨3801992728221108702369521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534661818814072468246347 3801992728221108702369521)
          ·
            refine ⟨2851494546165831526777141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3801992728221108702369521 2851494546165831526777141)
            ·
              refine ⟨267327613703046705635357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2851494546165831526777141 267327613703046705635357)
              ·
                refine ⟨100247855138642514613259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267327613703046705635357 100247855138642514613259)
                ·
                  rfl

theorem cell19_329454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_329454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329454 prefixEnd_329454 := by exact prefixLift 329454
  have htrace : WordTrace (prefixWord ++ tailWord_329454) baseStart_329454 baseEnd_329454 := by
    simpa [prefixWord, tailWord_329454, baseEnd_329454] using wordTrace_append hprefix tailTrace_329454
  have hstable : (prefixWord ++ tailWord_329454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329454).length < 2 ^ (prefixWord ++ tailWord_329454).sum := by decide
  have hdescent : baseEnd_329454 < baseStart_329454 := by decide
  rcases family_descends (prefixWord ++ tailWord_329454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329549 : List Nat := [1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_329549 : Nat := 118140960795 + 329549 * 2 ^ 59
def prefixEnd_329549 : Nat := 4983230072969 + 3 ^ 40 * 329549 * 2
def baseEnd_329549 : Nat := 100276762197710442501889

theorem tailTrace_329549 : CollatzResearch.WordTrace tailWord_329549 prefixEnd_329549 100276762197710442501889 := by
  unfold tailWord_329549
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019639483107730333431701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8013092988738486888954467 12019639483107730333431701)
  ·
    refine ⟨563420600770674859379611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12019639483107730333431701 563420600770674859379611)
    ·
      refine ⟨845130901156012289069417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563420600770674859379611 845130901156012289069417)
      ·
        refine ⟨633848175867009216802063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 845130901156012289069417 633848175867009216802063)
        ·
          refine ⟨950772263800513825203095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633848175867009216802063 950772263800513825203095)
          ·
            refine ⟨1426158395700770737804643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950772263800513825203095 1426158395700770737804643)
            ·
              refine ⟨2139237593551156106706965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426158395700770737804643 2139237593551156106706965)
              ·
                refine ⟨100276762197710442501889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2139237593551156106706965 100276762197710442501889)
                ·
                  rfl

theorem cell19_329549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_329549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329549 prefixEnd_329549 := by exact prefixLift 329549
  have htrace : WordTrace (prefixWord ++ tailWord_329549) baseStart_329549 baseEnd_329549 := by
    simpa [prefixWord, tailWord_329549, baseEnd_329549] using wordTrace_append hprefix tailTrace_329549
  have hstable : (prefixWord ++ tailWord_329549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329549).length < 2 ^ (prefixWord ++ tailWord_329549).sum := by decide
  have hdescent : baseEnd_329549 < baseStart_329549 := by decide
  rcases family_descends (prefixWord ++ tailWord_329549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329682 : List Nat := [3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_329682 : Nat := 118140960795 + 329682 * 2 ^ 59
def prefixEnd_329682 : Nat := 4983230072969 + 3 ^ 40 * 329682 * 2
def baseEnd_329682 : Nat := 100317232080405541545971

theorem tailTrace_329682 : CollatzResearch.WordTrace tailWord_329682 prefixEnd_329682 100317232080405541545971 := by
  unfold tailWord_329682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006122597906473512005825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8016326927750596032015533 3006122597906473512005825)
  ·
    refine ⟨2254591948429855134004369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3006122597906473512005825 2254591948429855134004369)
    ·
      refine ⟨1690943961322391350503277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2254591948429855134004369 1690943961322391350503277)
      ·
        refine ⟨634103985495896756438729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1690943961322391350503277 634103985495896756438729)
        ·
          refine ⟨475577989121922567329047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634103985495896756438729 475577989121922567329047)
          ·
            refine ⟨713366983682883850993571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475577989121922567329047 713366983682883850993571)
            ·
              refine ⟨1070050475524325776490357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713366983682883850993571 1070050475524325776490357)
              ·
                refine ⟨100317232080405541545971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1070050475524325776490357 100317232080405541545971)
                ·
                  rfl

theorem cell19_329682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_329682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329682 prefixEnd_329682 := by exact prefixLift 329682
  have htrace : WordTrace (prefixWord ++ tailWord_329682) baseStart_329682 baseEnd_329682 := by
    simpa [prefixWord, tailWord_329682, baseEnd_329682] using wordTrace_append hprefix tailTrace_329682
  have hstable : (prefixWord ++ tailWord_329682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329682).length < 2 ^ (prefixWord ++ tailWord_329682).sum := by decide
  have hdescent : baseEnd_329682 < baseStart_329682 := by decide
  rcases family_descends (prefixWord ++ tailWord_329682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329684 : List Nat := [2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_329684 : Nat := 118140960795 + 329684 * 2 ^ 59
def prefixEnd_329684 : Nat := 4983230072969 + 3 ^ 40 * 329684 * 2
def baseEnd_329684 : Nat := 100317840650070129501521

theorem tailTrace_329684 : CollatzResearch.WordTrace tailWord_329684 prefixEnd_329684 100317840650070129501521 := by
  unfold tailWord_329684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012281668809324194798053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8016375558412432259730737 6012281668809324194798053)
  ·
    refine ⟨1127302812901748286524635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6012281668809324194798053 1127302812901748286524635)
    ·
      refine ⟨1690954219352622429786953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127302812901748286524635 1690954219352622429786953)
      ·
        refine ⟨1268215664514466822340215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1690954219352622429786953 1268215664514466822340215)
        ·
          refine ⟨1902323496771700233510323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268215664514466822340215 1902323496771700233510323)
          ·
            refine ⟨2853485245157550350265485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902323496771700233510323 2853485245157550350265485)
            ·
              refine ⟨1070056966934081381349557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2853485245157550350265485 1070056966934081381349557)
              ·
                refine ⟨100317840650070129501521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1070056966934081381349557 100317840650070129501521)
                ·
                  rfl

theorem cell19_329684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_329684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329684 prefixEnd_329684 := by exact prefixLift 329684
  have htrace : WordTrace (prefixWord ++ tailWord_329684) baseStart_329684 baseEnd_329684 := by
    simpa [prefixWord, tailWord_329684, baseEnd_329684] using wordTrace_append hprefix tailTrace_329684
  have hstable : (prefixWord ++ tailWord_329684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329684).length < 2 ^ (prefixWord ++ tailWord_329684).sum := by decide
  have hdescent : baseEnd_329684 < baseStart_329684 := by decide
  rcases family_descends (prefixWord ++ tailWord_329684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329853 : List Nat := [1, 4, 1, 1, 3, 4, 2, 3]
def baseStart_329853 : Nat := 118140960795 + 329853 * 2 ^ 59
def prefixEnd_329853 : Nat := 4983230072969 + 3 ^ 40 * 329853 * 2
def baseEnd_329853 : Nat := 100369264786727811745505

theorem tailTrace_329853 : CollatzResearch.WordTrace tailWord_329853 prefixEnd_329853 100369264786727811745505 := by
  unfold tailWord_329853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030727274006390252498213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8020484849337593501665475 12030727274006390252498213)
  ·
    refine ⟨2255761363876198172343415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12030727274006390252498213 2255761363876198172343415)
    ·
      refine ⟨3383642045814297258515123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255761363876198172343415 3383642045814297258515123)
      ·
        refine ⟨5075463068721445887772685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383642045814297258515123 5075463068721445887772685)
        ·
          refine ⟨1903298650770542207914757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5075463068721445887772685 1903298650770542207914757)
          ·
            refine ⟨356868497019476663984017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1903298650770542207914757 356868497019476663984017)
            ·
              refine ⟨267651372764607497988013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356868497019476663984017 267651372764607497988013)
              ·
                refine ⟨100369264786727811745505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267651372764607497988013 100369264786727811745505)
                ·
                  rfl

theorem cell19_329853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_329853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329853 prefixEnd_329853 := by exact prefixLift 329853
  have htrace : WordTrace (prefixWord ++ tailWord_329853) baseStart_329853 baseEnd_329853 := by
    simpa [prefixWord, tailWord_329853, baseEnd_329853] using wordTrace_append hprefix tailTrace_329853
  have hstable : (prefixWord ++ tailWord_329853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329853).length < 2 ^ (prefixWord ++ tailWord_329853).sum := by decide
  have hdescent : baseEnd_329853 < baseStart_329853 := by decide
  rcases family_descends (prefixWord ++ tailWord_329853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329914 : List Nat := [3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_329914 : Nat := 118140960795 + 329914 * 2 ^ 59
def prefixEnd_329914 : Nat := 4983230072969 + 3 ^ 40 * 329914 * 2
def baseEnd_329914 : Nat := 100387826161497744389783

theorem tailTrace_329914 : CollatzResearch.WordTrace tailWord_329914 prefixEnd_329914 100387826161497744389783 := by
  unfold tailWord_329914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008238031696349417617199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8021968084523598446979197 3008238031696349417617199)
  ·
    refine ⟨4512357047544524126425799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3008238031696349417617199 4512357047544524126425799)
    ·
      refine ⟨6768535571316786189638699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4512357047544524126425799 6768535571316786189638699)
      ·
        refine ⟨10152803356975179284458049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6768535571316786189638699 10152803356975179284458049)
        ·
          refine ⟨7614602517731384463343537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10152803356975179284458049 7614602517731384463343537)
          ·
            refine ⟨5710951888298538347507653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7614602517731384463343537 5710951888298538347507653)
            ·
              refine ⟨1070803479055975940157685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5710951888298538347507653 1070803479055975940157685)
              ·
                refine ⟨100387826161497744389783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1070803479055975940157685 100387826161497744389783)
                ·
                  rfl

theorem cell19_329914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_329914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329914 prefixEnd_329914 := by exact prefixLift 329914
  have htrace : WordTrace (prefixWord ++ tailWord_329914) baseStart_329914 baseEnd_329914 := by
    simpa [prefixWord, tailWord_329914, baseEnd_329914] using wordTrace_append hprefix tailTrace_329914
  have hstable : (prefixWord ++ tailWord_329914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329914).length < 2 ^ (prefixWord ++ tailWord_329914).sum := by decide
  have hdescent : baseEnd_329914 < baseStart_329914 := by decide
  rcases family_descends (prefixWord ++ tailWord_329914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329988 : List Nat := [2, 3, 2, 2, 3, 1, 6]
def baseStart_329988 : Nat := 118140960795 + 329988 * 2 ^ 59
def prefixEnd_329988 : Nat := 4983230072969 + 3 ^ 40 * 329988 * 2
def baseEnd_329988 : Nat := 33470114413029166248379

theorem tailTrace_329988 : CollatzResearch.WordTrace tailWord_329988 prefixEnd_329988 33470114413029166248379 := by
  unfold tailWord_329988
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017825564258654154331309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8023767419011538872441745 6017825564258654154331309)
  ·
    refine ⟨2256684586596995307874241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6017825564258654154331309 2256684586596995307874241)
    ·
      refine ⟨1692513439947746480905681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2256684586596995307874241 1692513439947746480905681)
      ·
        refine ⟨1269385079960809860679261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1692513439947746480905681 1269385079960809860679261)
        ·
          refine ⟨476019404985303697754723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1269385079960809860679261 476019404985303697754723)
          ·
            refine ⟨714029107477955546632085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476019404985303697754723 714029107477955546632085)
            ·
              refine ⟨33470114413029166248379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 714029107477955546632085 33470114413029166248379)
              ·
                rfl

theorem cell19_329988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_329988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_329988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_329988 prefixEnd_329988 := by exact prefixLift 329988
  have htrace : WordTrace (prefixWord ++ tailWord_329988) baseStart_329988 baseEnd_329988 := by
    simpa [prefixWord, tailWord_329988, baseEnd_329988] using wordTrace_append hprefix tailTrace_329988
  have hstable : (prefixWord ++ tailWord_329988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329988).length < 2 ^ (prefixWord ++ tailWord_329988).sum := by decide
  have hdescent : baseEnd_329988 < baseStart_329988 := by decide
  rcases family_descends (prefixWord ++ tailWord_329988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330066 : List Nat := [3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_330066 : Nat := 118140960795 + 330066 * 2 ^ 59
def prefixEnd_330066 : Nat := 4983230072969 + 3 ^ 40 * 330066 * 2
def baseEnd_330066 : Nat := 100434077456006429011591

theorem tailTrace_330066 : CollatzResearch.WordTrace tailWord_330066 prefixEnd_330066 100434077456006429011591 := by
  unfold tailWord_330066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3009624005558681907500513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8025664014823151753334701 3009624005558681907500513)
  ·
    refine ⟨2257218004169011430625385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3009624005558681907500513 2257218004169011430625385)
    ·
      refine ⟨1692913503126758572969039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2257218004169011430625385 1692913503126758572969039)
      ·
        refine ⟨2539370254690137859453559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692913503126758572969039 2539370254690137859453559)
        ·
          refine ⟨3809055382035206789180339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539370254690137859453559 3809055382035206789180339)
          ·
            refine ⟨5713583073052810183770509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809055382035206789180339 5713583073052810183770509)
            ·
              refine ⟨2142593652394803818913941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5713583073052810183770509 2142593652394803818913941)
              ·
                refine ⟨100434077456006429011591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2142593652394803818913941 100434077456006429011591)
                ·
                  rfl

theorem cell19_330066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_330066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330066 prefixEnd_330066 := by exact prefixLift 330066
  have htrace : WordTrace (prefixWord ++ tailWord_330066) baseStart_330066 baseEnd_330066 := by
    simpa [prefixWord, tailWord_330066, baseEnd_330066] using wordTrace_append hprefix tailTrace_330066
  have hstable : (prefixWord ++ tailWord_330066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330066).length < 2 ^ (prefixWord ++ tailWord_330066).sum := by decide
  have hdescent : baseEnd_330066 < baseStart_330066 := by decide
  rcases family_descends (prefixWord ++ tailWord_330066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330085 : List Nat := [1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_330085 : Nat := 118140960795 + 330085 * 2 ^ 59
def prefixEnd_330085 : Nat := 4983230072969 + 3 ^ 40 * 330085 * 2
def baseEnd_330085 : Nat := 100439858867820014589317

theorem tailTrace_330085 : CollatzResearch.WordTrace tailWord_330085 prefixEnd_330085 100439858867820014589317 := by
  unfold tailWord_330085
  simp only [CollatzResearch.WordTrace]
  refine ⟨12039189009165893874943709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8026126006110595916629139 12039189009165893874943709)
  ·
    refine ⟨4514695878437210203103891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12039189009165893874943709 4514695878437210203103891)
    ·
      refine ⟨6772043817655815304655837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4514695878437210203103891 6772043817655815304655837)
      ·
        refine ⟨2539516431620930739245939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6772043817655815304655837 2539516431620930739245939)
        ·
          refine ⟨3809274647431396108868909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539516431620930739245939 3809274647431396108868909)
          ·
            refine ⟨1428477992786773540825841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3809274647431396108868909 1428477992786773540825841)
            ·
              refine ⟨1071358494590080155619381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428477992786773540825841 1071358494590080155619381)
              ·
                refine ⟨100439858867820014589317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1071358494590080155619381 100439858867820014589317)
                ·
                  rfl

theorem cell19_330085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_330085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330085 prefixEnd_330085 := by exact prefixLift 330085
  have htrace : WordTrace (prefixWord ++ tailWord_330085) baseStart_330085 baseEnd_330085 := by
    simpa [prefixWord, tailWord_330085, baseEnd_330085] using wordTrace_append hprefix tailTrace_330085
  have hstable : (prefixWord ++ tailWord_330085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330085).length < 2 ^ (prefixWord ++ tailWord_330085).sum := by decide
  have hdescent : baseEnd_330085 < baseStart_330085 := by decide
  rcases family_descends (prefixWord ++ tailWord_330085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330102 : List Nat := [5, 1, 1, 4, 8]
def baseStart_330102 : Nat := 118140960795 + 330102 * 2 ^ 59
def prefixEnd_330102 : Nat := 4983230072969 + 3 ^ 40 * 330102 * 2
def baseEnd_330102 : Nat := 3720186359628481933759

theorem tailTrace_330102 : CollatzResearch.WordTrace tailWord_330102 prefixEnd_330102 3720186359628481933759 := by
  unfold tailWord_330102
  simp only [CollatzResearch.WordTrace]
  refine ⟨752488065631519111144535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8026539366736203852208373 752488065631519111144535)
  ·
    refine ⟨1128732098447278666716803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 752488065631519111144535 1128732098447278666716803)
    ·
      refine ⟨1693098147670918000075205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128732098447278666716803 1693098147670918000075205)
      ·
        refine ⟨317455902688297125014101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1693098147670918000075205 317455902688297125014101)
        ·
          refine ⟨3720186359628481933759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 317455902688297125014101 3720186359628481933759)
          ·
            rfl

theorem cell19_330102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 8].length) (baseStart_330102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330102 prefixEnd_330102 := by exact prefixLift 330102
  have htrace : WordTrace (prefixWord ++ tailWord_330102) baseStart_330102 baseEnd_330102 := by
    simpa [prefixWord, tailWord_330102, baseEnd_330102] using wordTrace_append hprefix tailTrace_330102
  have hstable : (prefixWord ++ tailWord_330102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330102).length < 2 ^ (prefixWord ++ tailWord_330102).sum := by decide
  have hdescent : baseEnd_330102 < baseStart_330102 := by decide
  rcases family_descends (prefixWord ++ tailWord_330102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330121 : List Nat := [1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_330121 : Nat := 118140960795 + 330121 * 2 ^ 59
def prefixEnd_330121 : Nat := 4983230072969 + 3 ^ 40 * 330121 * 2
def baseEnd_330121 : Nat := 100450813121782597789219

theorem tailTrace_330121 : CollatzResearch.WordTrace tailWord_330121 prefixEnd_330121 100450813121782597789219 := by
  unfold tailWord_330121
  simp only [CollatzResearch.WordTrace]
  refine ⟨12040502037035472023254217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8027001358023648015502811 12040502037035472023254217)
  ·
    refine ⟨9030376527776604017440663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12040502037035472023254217 9030376527776604017440663)
    ·
      refine ⟨13545564791664906026160995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9030376527776604017440663 13545564791664906026160995)
      ·
        refine ⟨20318347187497359039241493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13545564791664906026160995 20318347187497359039241493)
        ·
          refine ⟨952422524413938704964445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20318347187497359039241493 952422524413938704964445)
          ·
            refine ⟨357158446655227014361667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 952422524413938704964445 357158446655227014361667)
            ·
              refine ⟨535737669982840521542501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357158446655227014361667 535737669982840521542501)
              ·
                refine ⟨100450813121782597789219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535737669982840521542501 100450813121782597789219)
                ·
                  rfl

theorem cell19_330121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_330121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330121 prefixEnd_330121 := by exact prefixLift 330121
  have htrace : WordTrace (prefixWord ++ tailWord_330121) baseStart_330121 baseEnd_330121 := by
    simpa [prefixWord, tailWord_330121, baseEnd_330121] using wordTrace_append hprefix tailTrace_330121
  have hstable : (prefixWord ++ tailWord_330121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330121).length < 2 ^ (prefixWord ++ tailWord_330121).sum := by decide
  have hdescent : baseEnd_330121 < baseStart_330121 := by decide
  rcases family_descends (prefixWord ++ tailWord_330121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330123 : List Nat := [1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_330123 : Nat := 118140960795 + 330123 * 2 ^ 59
def prefixEnd_330123 : Nat := 4983230072969 + 3 ^ 40 * 330123 * 2
def baseEnd_330123 : Nat := 100451421691447185744769

theorem tailTrace_330123 : CollatzResearch.WordTrace tailWord_330123 prefixEnd_330123 100451421691447185744769 := by
  unfold tailWord_330123
  simp only [CollatzResearch.WordTrace]
  refine ⟨12040574983028226364827023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8027049988685484243218015 12040574983028226364827023)
  ·
    refine ⟨18060862474542339547240535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12040574983028226364827023 18060862474542339547240535)
    ·
      refine ⟨27091293711813509320860803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18060862474542339547240535 27091293711813509320860803)
      ·
        refine ⟨40636940567720263981291205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27091293711813509320860803 40636940567720263981291205)
        ·
          refine ⟨7619426356447549496492101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40636940567720263981291205 7619426356447549496492101)
          ·
            refine ⟨1428642441833915530592269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7619426356447549496492101 1428642441833915530592269)
            ·
              refine ⟨535740915687718323972101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1428642441833915530592269 535740915687718323972101)
              ·
                refine ⟨100451421691447185744769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535740915687718323972101 100451421691447185744769)
                ·
                  rfl

theorem cell19_330123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_330123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330123 prefixEnd_330123 := by exact prefixLift 330123
  have htrace : WordTrace (prefixWord ++ tailWord_330123) baseStart_330123 baseEnd_330123 := by
    simpa [prefixWord, tailWord_330123, baseEnd_330123] using wordTrace_append hprefix tailTrace_330123
  have hstable : (prefixWord ++ tailWord_330123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330123).length < 2 ^ (prefixWord ++ tailWord_330123).sum := by decide
  have hdescent : baseEnd_330123 < baseStart_330123 := by decide
  rcases family_descends (prefixWord ++ tailWord_330123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330161 : List Nat := [1, 2, 2, 4, 1, 3, 6]
def baseStart_330161 : Nat := 118140960795 + 330161 * 2 ^ 59
def prefixEnd_330161 : Nat := 4983230072969 + 3 ^ 40 * 330161 * 2
def baseEnd_330161 : Nat := 33487661505024785633407

theorem tailTrace_330161 : CollatzResearch.WordTrace tailWord_330161 prefixEnd_330161 33487661505024785633407 := by
  unfold tailWord_330161
  simp only [CollatzResearch.WordTrace]
  refine ⟨12041960956890558854710337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8027973971260372569806891 12041960956890558854710337)
  ·
    refine ⟨9031470717667919141032753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12041960956890558854710337 9031470717667919141032753)
    ·
      refine ⟨6773603038250939355774565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9031470717667919141032753 6773603038250939355774565)
      ·
        refine ⟨1270050569672051129207731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6773603038250939355774565 1270050569672051129207731)
        ·
          refine ⟨1905075854508076693811597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270050569672051129207731 1905075854508076693811597)
          ·
            refine ⟨714403445440528760179349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1905075854508076693811597 714403445440528760179349)
            ·
              refine ⟨33487661505024785633407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 714403445440528760179349 33487661505024785633407)
              ·
                rfl

theorem cell19_330161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_330161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330161 prefixEnd_330161 := by exact prefixLift 330161
  have htrace : WordTrace (prefixWord ++ tailWord_330161) baseStart_330161 baseEnd_330161 := by
    simpa [prefixWord, tailWord_330161, baseEnd_330161] using wordTrace_append hprefix tailTrace_330161
  have hstable : (prefixWord ++ tailWord_330161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330161).length < 2 ^ (prefixWord ++ tailWord_330161).sum := by decide
  have hdescent : baseEnd_330161 < baseStart_330161 := by decide
  rcases family_descends (prefixWord ++ tailWord_330161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330197 : List Nat := [1, 3, 2, 3, 1, 2, 4, 3]
def baseStart_330197 : Nat := 118140960795 + 330197 * 2 ^ 59
def prefixEnd_330197 : Nat := 4983230072969 + 3 ^ 40 * 330197 * 2
def baseEnd_330197 : Nat := 100473938769036940100123

theorem tailTrace_330197 : CollatzResearch.WordTrace tailWord_330197 prefixEnd_330197 100473938769036940100123 := by
  unfold tailWord_330197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043273984760137003020845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8028849323173424668680563 12043273984760137003020845)
  ·
    refine ⟨4516227744285051376132817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12043273984760137003020845 4516227744285051376132817)
    ·
      refine ⟨3387170808213788532099613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4516227744285051376132817 3387170808213788532099613)
      ·
        refine ⟨1270189053080170699537355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3387170808213788532099613 1270189053080170699537355)
        ·
          refine ⟨1905283579620256049306033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270189053080170699537355 1905283579620256049306033)
          ·
            refine ⟨1428962684715192036979525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905283579620256049306033 1428962684715192036979525)
            ·
              refine ⟨267930503384098506933661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1428962684715192036979525 267930503384098506933661)
              ·
                refine ⟨100473938769036940100123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267930503384098506933661 100473938769036940100123)
                ·
                  rfl

theorem cell19_330197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_330197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330197 prefixEnd_330197 := by exact prefixLift 330197
  have htrace : WordTrace (prefixWord ++ tailWord_330197) baseStart_330197 baseEnd_330197 := by
    simpa [prefixWord, tailWord_330197, baseEnd_330197] using wordTrace_append hprefix tailTrace_330197
  have hstable : (prefixWord ++ tailWord_330197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330197).length < 2 ^ (prefixWord ++ tailWord_330197).sum := by decide
  have hdescent : baseEnd_330197 < baseStart_330197 := by decide
  rcases family_descends (prefixWord ++ tailWord_330197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330218 : List Nat := [3, 1, 3, 1, 3, 1, 7]
def baseStart_330218 : Nat := 118140960795 + 330218 * 2 ^ 59
def prefixEnd_330218 : Nat := 4983230072969 + 3 ^ 40 * 330218 * 2
def baseEnd_330218 : Nat := 33493442916838371211133

theorem tailTrace_330218 : CollatzResearch.WordTrace tailWord_330218 prefixEnd_330218 33493442916838371211133 := by
  unfold tailWord_330218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011009979421014397383827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8029359945122705059690205 3011009979421014397383827)
  ·
    refine ⟨4516514969131521596075741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3011009979421014397383827 4516514969131521596075741)
    ·
      refine ⟨1693693113424320598528403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4516514969131521596075741 1693693113424320598528403)
      ·
        refine ⟨2540539670136480897792605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693693113424320598528403 2540539670136480897792605)
        ·
          refine ⟨952702376301180336672227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2540539670136480897792605 952702376301180336672227)
          ·
            refine ⟨1429053564451770505008341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952702376301180336672227 1429053564451770505008341)
            ·
              refine ⟨33493442916838371211133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1429053564451770505008341 33493442916838371211133)
              ·
                rfl

theorem cell19_330218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_330218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330218 prefixEnd_330218 := by exact prefixLift 330218
  have htrace : WordTrace (prefixWord ++ tailWord_330218) baseStart_330218 baseEnd_330218 := by
    simpa [prefixWord, tailWord_330218, baseEnd_330218] using wordTrace_append hprefix tailTrace_330218
  have hstable : (prefixWord ++ tailWord_330218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330218).length < 2 ^ (prefixWord ++ tailWord_330218).sum := by decide
  have hdescent : baseEnd_330218 < baseStart_330218 := by decide
  rcases family_descends (prefixWord ++ tailWord_330218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330237 : List Nat := [1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_330237 : Nat := 118140960795 + 330237 * 2 ^ 59
def prefixEnd_330237 : Nat := 4983230072969 + 3 ^ 40 * 330237 * 2
def baseEnd_330237 : Nat := 100486110162328699211125

theorem tailTrace_330237 : CollatzResearch.WordTrace tailWord_330237 prefixEnd_330237 100486110162328699211125 := by
  unfold tailWord_330237
  simp only [CollatzResearch.WordTrace]
  refine ⟨12044732904615223834476965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8029821936410149222984643 12044732904615223834476965)
  ·
    refine ⟨2258387419615354468964431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12044732904615223834476965 2258387419615354468964431)
    ·
      refine ⟨3387581129423031703446647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258387419615354468964431 3387581129423031703446647)
      ·
        refine ⟨5081371694134547555169971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3387581129423031703446647 5081371694134547555169971)
        ·
          refine ⟨7622057541201821332754957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081371694134547555169971 7622057541201821332754957)
          ·
            refine ⟨2858271577950682999783109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7622057541201821332754957 2858271577950682999783109)
            ·
              refine ⟨535925920865753062459333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2858271577950682999783109 535925920865753062459333)
              ·
                refine ⟨100486110162328699211125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535925920865753062459333 100486110162328699211125)
                ·
                  rfl

theorem cell19_330237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_330237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330237 prefixEnd_330237 := by exact prefixLift 330237
  have htrace : WordTrace (prefixWord ++ tailWord_330237) baseStart_330237 baseEnd_330237 := by
    simpa [prefixWord, tailWord_330237, baseEnd_330237] using wordTrace_append hprefix tailTrace_330237
  have hstable : (prefixWord ++ tailWord_330237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330237).length < 2 ^ (prefixWord ++ tailWord_330237).sum := by decide
  have hdescent : baseEnd_330237 < baseStart_330237 := by decide
  rcases family_descends (prefixWord ++ tailWord_330237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330311 : List Nat := [1, 1, 4, 1, 4, 2, 3, 3]
def baseStart_330311 : Nat := 118140960795 + 330311 * 2 ^ 59
def prefixEnd_330311 : Nat := 4983230072969 + 3 ^ 40 * 330311 * 2
def baseEnd_330311 : Nat := 100508627239918453566479

theorem tailTrace_330311 : CollatzResearch.WordTrace tailWord_330311 prefixEnd_330311 100508627239918453566479 := by
  unfold tailWord_330311
  simp only [CollatzResearch.WordTrace]
  refine ⟨12047431906347134472670787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8031621270898089648447191 12047431906347134472670787)
  ·
    refine ⟨18071147859520701709006181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12047431906347134472670787 18071147859520701709006181)
    ·
      refine ⟨3388340223660131570438659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18071147859520701709006181 3388340223660131570438659)
      ·
        refine ⟨5082510335490197355657989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3388340223660131570438659 5082510335490197355657989)
        ·
          refine ⟨952970687904412004185873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5082510335490197355657989 952970687904412004185873)
          ·
            refine ⟨714728015928309003139405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952970687904412004185873 714728015928309003139405)
            ·
              refine ⟨268023005973115876177277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 714728015928309003139405 268023005973115876177277)
              ·
                refine ⟨100508627239918453566479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268023005973115876177277 100508627239918453566479)
                ·
                  rfl

theorem cell19_330311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_330311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330311 prefixEnd_330311 := by exact prefixLift 330311
  have htrace : WordTrace (prefixWord ++ tailWord_330311) baseStart_330311 baseEnd_330311 := by
    simpa [prefixWord, tailWord_330311, baseEnd_330311] using wordTrace_append hprefix tailTrace_330311
  have hstable : (prefixWord ++ tailWord_330311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330311).length < 2 ^ (prefixWord ++ tailWord_330311).sum := by decide
  have hdescent : baseEnd_330311 < baseStart_330311 := by decide
  rcases family_descends (prefixWord ++ tailWord_330311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330315 : List Nat := [1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_330315 : Nat := 118140960795 + 330315 * 2 ^ 59
def prefixEnd_330315 : Nat := 4983230072969 + 3 ^ 40 * 330315 * 2
def baseEnd_330315 : Nat := 100509844379247629477579

theorem tailTrace_330315 : CollatzResearch.WordTrace tailWord_330315 prefixEnd_330315 100509844379247629477579 := by
  unfold tailWord_330315
  simp only [CollatzResearch.WordTrace]
  refine ⟨12047577798332643155816399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8031718532221762103877599 12047577798332643155816399)
  ·
    refine ⟨18071366697498964733724599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12047577798332643155816399 18071366697498964733724599)
    ·
      refine ⟨27107050046248447100586899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18071366697498964733724599 27107050046248447100586899)
      ·
        refine ⟨40660575069372670650880349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27107050046248447100586899 40660575069372670650880349)
        ·
          refine ⟨15247715651014751494080131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40660575069372670650880349 15247715651014751494080131)
          ·
            refine ⟨22871573476522127241120197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15247715651014751494080131 22871573476522127241120197)
            ·
              refine ⟨4288420026847898857710037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22871573476522127241120197 4288420026847898857710037)
              ·
                refine ⟨100509844379247629477579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4288420026847898857710037 100509844379247629477579)
                ·
                  rfl

theorem cell19_330315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_330315 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330315 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330315 prefixEnd_330315 := by exact prefixLift 330315
  have htrace : WordTrace (prefixWord ++ tailWord_330315) baseStart_330315 baseEnd_330315 := by
    simpa [prefixWord, tailWord_330315, baseEnd_330315] using wordTrace_append hprefix tailTrace_330315
  have hstable : (prefixWord ++ tailWord_330315).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330315).length < 2 ^ (prefixWord ++ tailWord_330315).sum := by decide
  have hdescent : baseEnd_330315 < baseStart_330315 := by decide
  rcases family_descends (prefixWord ++ tailWord_330315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330368 : List Nat := [2, 1, 1, 2, 1, 7, 2, 3]
def baseStart_330368 : Nat := 118140960795 + 330368 * 2 ^ 59
def prefixEnd_330368 : Nat := 4983230072969 + 3 ^ 40 * 330368 * 2
def baseEnd_330368 : Nat := 100525971475359210299657

theorem tailTrace_330368 : CollatzResearch.WordTrace tailWord_330368 prefixEnd_330368 100525971475359210299657 := by
  unfold tailWord_330368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6024755433570316603747879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8033007244760422138330505 6024755433570316603747879)
  ·
    refine ⟨9037133150355474905621819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6024755433570316603747879 9037133150355474905621819)
    ·
      refine ⟨13555699725533212358432729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9037133150355474905621819 13555699725533212358432729)
      ·
        refine ⟨10166774794149909268824547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13555699725533212358432729 10166774794149909268824547)
        ·
          refine ⟨15250162191224863903236821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10166774794149909268824547 15250162191224863903236821)
          ·
            refine ⟨357425676356832747732113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15250162191224863903236821 357425676356832747732113)
            ·
              refine ⟨268069257267624560799085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357425676356832747732113 268069257267624560799085)
              ·
                refine ⟨100525971475359210299657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268069257267624560799085 100525971475359210299657)
                ·
                  rfl

theorem cell19_330368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_330368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330368 prefixEnd_330368 := by exact prefixLift 330368
  have htrace : WordTrace (prefixWord ++ tailWord_330368) baseStart_330368 baseEnd_330368 := by
    simpa [prefixWord, tailWord_330368, baseEnd_330368] using wordTrace_append hprefix tailTrace_330368
  have hstable : (prefixWord ++ tailWord_330368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330368).length < 2 ^ (prefixWord ++ tailWord_330368).sum := by decide
  have hdescent : baseEnd_330368 < baseStart_330368 := by decide
  rcases family_descends (prefixWord ++ tailWord_330368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330465 : List Nat := [1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_330465 : Nat := 118140960795 + 330465 * 2 ^ 59
def prefixEnd_330465 : Nat := 4983230072969 + 3 ^ 40 * 330465 * 2
def baseEnd_330465 : Nat := 100555487104091726143837

theorem tailTrace_330465 : CollatzResearch.WordTrace tailWord_330465 prefixEnd_330465 100555487104091726143837 := by
  unfold tailWord_330465
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053048747789218773776849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8035365831859479182517899 12053048747789218773776849)
  ·
    refine ⟨9039786560841914080332637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12053048747789218773776849 9039786560841914080332637)
    ·
      refine ⟨3389919960315717780124739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9039786560841914080332637 3389919960315717780124739)
      ·
        refine ⟨5084879940473576670187109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389919960315717780124739 5084879940473576670187109)
        ·
          refine ⟨953414988838795625660083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5084879940473576670187109 953414988838795625660083)
          ·
            refine ⟨1430122483258193438490125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953414988838795625660083 1430122483258193438490125)
            ·
              refine ⟨536295931221822539433797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1430122483258193438490125 536295931221822539433797)
              ·
                refine ⟨100555487104091726143837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 536295931221822539433797 100555487104091726143837)
                ·
                  rfl

theorem cell19_330465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_330465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330465 prefixEnd_330465 := by exact prefixLift 330465
  have htrace : WordTrace (prefixWord ++ tailWord_330465) baseStart_330465 baseEnd_330465 := by
    simpa [prefixWord, tailWord_330465, baseEnd_330465] using wordTrace_append hprefix tailTrace_330465
  have hstable : (prefixWord ++ tailWord_330465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330465).length < 2 ^ (prefixWord ++ tailWord_330465).sum := by decide
  have hdescent : baseEnd_330465 < baseStart_330465 := by decide
  rcases family_descends (prefixWord ++ tailWord_330465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330482 : List Nat := [3, 2, 1, 3, 1, 3, 3, 3]
def baseStart_330482 : Nat := 118140960795 + 330482 * 2 ^ 59
def prefixEnd_330482 : Nat := 4983230072969 + 3 ^ 40 * 330482 * 2
def baseEnd_330482 : Nat := 100560659946240723766013

theorem tailTrace_330482 : CollatzResearch.WordTrace tailWord_330482 prefixEnd_330482 100560659946240723766013 := by
  unfold tailWord_330482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013417197181907669286425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8035779192485087118097133 3013417197181907669286425)
  ·
    refine ⟨2260062897886430751964819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3013417197181907669286425 2260062897886430751964819)
    ·
      refine ⟨3390094346829646127947229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260062897886430751964819 3390094346829646127947229)
      ·
        refine ⟨1271285380061117297980211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3390094346829646127947229 1271285380061117297980211)
        ·
          refine ⟨1906928070091675946970317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271285380061117297980211 1906928070091675946970317)
          ·
            refine ⟨715098026284378480113869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1906928070091675946970317 715098026284378480113869)
            ·
              refine ⟨268161759856641930042701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715098026284378480113869 268161759856641930042701)
              ·
                refine ⟨100560659946240723766013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268161759856641930042701 100560659946240723766013)
                ·
                  rfl

theorem cell19_330482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_330482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330482 prefixEnd_330482 := by exact prefixLift 330482
  have htrace : WordTrace (prefixWord ++ tailWord_330482) baseStart_330482 baseEnd_330482 := by
    simpa [prefixWord, tailWord_330482, baseEnd_330482] using wordTrace_append hprefix tailTrace_330482
  have hstable : (prefixWord ++ tailWord_330482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330482).length < 2 ^ (prefixWord ++ tailWord_330482).sum := by decide
  have hdescent : baseEnd_330482 < baseStart_330482 := by decide
  rcases family_descends (prefixWord ++ tailWord_330482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330503 : List Nat := [1, 1, 4, 4, 1, 2, 6]
def baseStart_330503 : Nat := 118140960795 + 330503 * 2 ^ 59
def prefixEnd_330503 : Nat := 4983230072969 + 3 ^ 40 * 330503 * 2
def baseEnd_330503 : Nat := 33522349975906299099763

theorem tailTrace_330503 : CollatzResearch.WordTrace tailWord_330503 prefixEnd_330503 33522349975906299099763 := by
  unfold tailWord_330503
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054434721651551263660163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8036289814434367509106775 12054434721651551263660163)
  ·
    refine ⟨18081652082477326895490245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12054434721651551263660163 18081652082477326895490245)
    ·
      refine ⟨3390309765464498792904421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18081652082477326895490245 3390309765464498792904421)
      ·
        refine ⟨635683081024593523669579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3390309765464498792904421 635683081024593523669579)
        ·
          refine ⟨953524621536890285504369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635683081024593523669579 953524621536890285504369)
          ·
            refine ⟨715143466152667714128277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953524621536890285504369 715143466152667714128277)
            ·
              refine ⟨33522349975906299099763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 715143466152667714128277 33522349975906299099763)
              ·
                rfl

theorem cell19_330503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_330503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330503 prefixEnd_330503 := by exact prefixLift 330503
  have htrace : WordTrace (prefixWord ++ tailWord_330503) baseStart_330503 baseEnd_330503 := by
    simpa [prefixWord, tailWord_330503, baseEnd_330503] using wordTrace_append hprefix tailTrace_330503
  have hstable : (prefixWord ++ tailWord_330503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330503).length < 2 ^ (prefixWord ++ tailWord_330503).sum := by decide
  have hdescent : baseEnd_330503 < baseStart_330503 := by decide
  rcases family_descends (prefixWord ++ tailWord_330503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330558 : List Nat := [4, 2, 1, 2, 3, 2, 5]
def baseStart_330558 : Nat := 118140960795 + 330558 * 2 ^ 59
def prefixEnd_330558 : Nat := 4983230072969 + 3 ^ 40 * 330558 * 2
def baseEnd_330558 : Nat := 33527928531165022025639

theorem tailTrace_330558 : CollatzResearch.WordTrace tailWord_330558 prefixEnd_330558 33527928531165022025639 := by
  unfold tailWord_330558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507055092056536957114041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8037627157634863771274885 1507055092056536957114041)
  ·
    refine ⟨1130291319042402717835531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1507055092056536957114041 1130291319042402717835531)
    ·
      refine ⟨1695436978563604076753297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130291319042402717835531 1695436978563604076753297)
      ·
        refine ⟨1271577733922703057564973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695436978563604076753297 1271577733922703057564973)
        ·
          refine ⟨476841650221013646586865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1271577733922703057564973 476841650221013646586865)
          ·
            refine ⟨357631237665760234940149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476841650221013646586865 357631237665760234940149)
            ·
              refine ⟨33527928531165022025639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 357631237665760234940149 33527928531165022025639)
              ·
                rfl

theorem cell19_330558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_330558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330558 prefixEnd_330558 := by exact prefixLift 330558
  have htrace : WordTrace (prefixWord ++ tailWord_330558) baseStart_330558 baseEnd_330558 := by
    simpa [prefixWord, tailWord_330558, baseEnd_330558] using wordTrace_append hprefix tailTrace_330558
  have hstable : (prefixWord ++ tailWord_330558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330558).length < 2 ^ (prefixWord ++ tailWord_330558).sum := by decide
  have hdescent : baseEnd_330558 < baseStart_330558 := by decide
  rcases family_descends (prefixWord ++ tailWord_330558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330634 : List Nat := [3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_330634 : Nat := 118140960795 + 330634 * 2 ^ 59
def prefixEnd_330634 : Nat := 4983230072969 + 3 ^ 40 * 330634 * 2
def baseEnd_330634 : Nat := 100606911240749408387821

theorem tailTrace_330634 : CollatzResearch.WordTrace tailWord_330634 prefixEnd_330634 100606911240749408387821 := by
  unfold tailWord_330634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014803171044240159169739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8039475122784640424452637 3014803171044240159169739)
  ·
    refine ⟨4522204756566360238754609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3014803171044240159169739 4522204756566360238754609)
    ·
      refine ⟨3391653567424770179065957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4522204756566360238754609 3391653567424770179065957)
      ·
        refine ⟨635935043892144408574867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3391653567424770179065957 635935043892144408574867)
        ·
          refine ⟨953902565838216612862301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635935043892144408574867 953902565838216612862301)
          ·
            refine ⟨357713462189331229823363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 953902565838216612862301 357713462189331229823363)
            ·
              refine ⟨536570193283996844735045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357713462189331229823363 536570193283996844735045)
              ·
                refine ⟨100606911240749408387821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 536570193283996844735045 100606911240749408387821)
                ·
                  rfl

theorem cell19_330634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_330634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330634 prefixEnd_330634 := by exact prefixLift 330634
  have htrace : WordTrace (prefixWord ++ tailWord_330634) baseStart_330634 baseEnd_330634 := by
    simpa [prefixWord, tailWord_330634, baseEnd_330634] using wordTrace_append hprefix tailTrace_330634
  have hstable : (prefixWord ++ tailWord_330634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330634).length < 2 ^ (prefixWord ++ tailWord_330634).sum := by decide
  have hdescent : baseEnd_330634 < baseStart_330634 := by decide
  rcases family_descends (prefixWord ++ tailWord_330634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330710 : List Nat := [5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_330710 : Nat := 118140960795 + 330710 * 2 ^ 59
def prefixEnd_330710 : Nat := 4983230072969 + 3 ^ 40 * 330710 * 2
def baseEnd_330710 : Nat := 100630036888003750698725

theorem tailTrace_330710 : CollatzResearch.WordTrace tailWord_330710 prefixEnd_330710 100630036888003750698725 := by
  unfold tailWord_330710
  simp only [CollatzResearch.WordTrace]
  refine ⟨753874039493851601027849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8041323087934417077630389 753874039493851601027849)
  ·
    refine ⟨565405529620388700770887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 753874039493851601027849 565405529620388700770887)
    ·
      refine ⟨848108294430583051156331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565405529620388700770887 848108294430583051156331)
      ·
        refine ⟨1272162441645874576734497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848108294430583051156331 1272162441645874576734497)
        ·
          refine ⟨954121831234405932550873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272162441645874576734497 954121831234405932550873)
          ·
            refine ⟨715591373425804449413155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954121831234405932550873 715591373425804449413155)
            ·
              refine ⟨1073387060138706674119733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715591373425804449413155 1073387060138706674119733)
              ·
                refine ⟨100630036888003750698725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1073387060138706674119733 100630036888003750698725)
                ·
                  rfl

theorem cell19_330710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_330710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330710 prefixEnd_330710 := by exact prefixLift 330710
  have htrace : WordTrace (prefixWord ++ tailWord_330710) baseStart_330710 baseEnd_330710 := by
    simpa [prefixWord, tailWord_330710, baseEnd_330710] using wordTrace_append hprefix tailTrace_330710
  have hstable : (prefixWord ++ tailWord_330710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330710).length < 2 ^ (prefixWord ++ tailWord_330710).sum := by decide
  have hdescent : baseEnd_330710 < baseStart_330710 := by decide
  rcases family_descends (prefixWord ++ tailWord_330710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330712 : List Nat := [2, 1, 2, 2, 2, 3, 4, 3]
def baseStart_330712 : Nat := 118140960795 + 330712 * 2 ^ 59
def prefixEnd_330712 : Nat := 4983230072969 + 3 ^ 40 * 330712 * 2
def baseEnd_330712 : Nat := 100630645457668338654275

theorem tailTrace_330712 : CollatzResearch.WordTrace tailWord_330712 prefixEnd_330712 100630645457668338654275 := by
  unfold tailWord_330712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031028788947189979009195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8041371718596253305345593 6031028788947189979009195)
  ·
    refine ⟨9046543183420784968513793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6031028788947189979009195 9046543183420784968513793)
    ·
      refine ⟨6784907387565588726385345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9046543183420784968513793 6784907387565588726385345)
      ·
        refine ⟨5088680540674191544789009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6784907387565588726385345 5088680540674191544789009)
        ·
          refine ⟨3816510405505643658591757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5088680540674191544789009 3816510405505643658591757)
          ·
            refine ⟨1431191402064616371971909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3816510405505643658591757 1431191402064616371971909)
            ·
              refine ⟨268348387887115569744733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1431191402064616371971909 268348387887115569744733)
              ·
                refine ⟨100630645457668338654275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268348387887115569744733 100630645457668338654275)
                ·
                  rfl

theorem cell19_330712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_330712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330712 prefixEnd_330712 := by exact prefixLift 330712
  have htrace : WordTrace (prefixWord ++ tailWord_330712) baseStart_330712 baseEnd_330712 := by
    simpa [prefixWord, tailWord_330712, baseEnd_330712] using wordTrace_append hprefix tailTrace_330712
  have hstable : (prefixWord ++ tailWord_330712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330712).length < 2 ^ (prefixWord ++ tailWord_330712).sum := by decide
  have hdescent : baseEnd_330712 < baseStart_330712 := by decide
  rcases family_descends (prefixWord ++ tailWord_330712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330822 : List Nat := [6, 1, 1, 1, 1, 3, 3, 3]
def baseStart_330822 : Nat := 118140960795 + 330822 * 2 ^ 59
def prefixEnd_330822 : Nat := 4983230072969 + 3 ^ 40 * 330822 * 2
def baseEnd_330822 : Nat := 100664116789220676209531

theorem tailTrace_330822 : CollatzResearch.WordTrace tailWord_330822 prefixEnd_330822 100664116789220676209531 := by
  unfold tailWord_330822
  simp only [CollatzResearch.WordTrace]
  refine ⟨377064675234245898266335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8044046404997245829681813 377064675234245898266335)
  ·
    refine ⟨565597012851368847399503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 377064675234245898266335 565597012851368847399503)
    ·
      refine ⟨848395519277053271099255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565597012851368847399503 848395519277053271099255)
      ·
        refine ⟨1272593278915579906648883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848395519277053271099255 1272593278915579906648883)
        ·
          refine ⟨1908889918373369859973325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272593278915579906648883 1908889918373369859973325)
          ·
            refine ⟨715833719390013697489997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1908889918373369859973325 715833719390013697489997)
            ·
              refine ⟨268437644771255136558749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715833719390013697489997 268437644771255136558749)
              ·
                refine ⟨100664116789220676209531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268437644771255136558749 100664116789220676209531)
                ·
                  rfl

theorem cell19_330822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_330822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330822 prefixEnd_330822 := by exact prefixLift 330822
  have htrace : WordTrace (prefixWord ++ tailWord_330822) baseStart_330822 baseEnd_330822 := by
    simpa [prefixWord, tailWord_330822, baseEnd_330822] using wordTrace_append hprefix tailTrace_330822
  have hstable : (prefixWord ++ tailWord_330822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330822).length < 2 ^ (prefixWord ++ tailWord_330822).sum := by decide
  have hdescent : baseEnd_330822 < baseStart_330822 := by decide
  rcases family_descends (prefixWord ++ tailWord_330822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330866 : List Nat := [3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_330866 : Nat := 118140960795 + 330866 * 2 ^ 59
def prefixEnd_330866 : Nat := 4983230072969 + 3 ^ 40 * 330866 * 2
def baseEnd_330866 : Nat := 100677505321841611231633

theorem tailTrace_330866 : CollatzResearch.WordTrace tailWord_330866 prefixEnd_330866 100677505321841611231633 := by
  unfold tailWord_330866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016918604834116064781113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8045116279557642839416301 3016918604834116064781113)
  ·
    refine ⟨2262688953625587048585835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3016918604834116064781113 2262688953625587048585835)
    ·
      refine ⟨3394033430438380572878753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262688953625587048585835 3394033430438380572878753)
      ·
        refine ⟨2545525072828785429659065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3394033430438380572878753 2545525072828785429659065)
        ·
          refine ⟨1909143804621589072244299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2545525072828785429659065 1909143804621589072244299)
          ·
            refine ⟨2863715706932383608366449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909143804621589072244299 2863715706932383608366449)
            ·
              refine ⟨2147786780199287706274837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863715706932383608366449 2147786780199287706274837)
              ·
                refine ⟨100677505321841611231633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2147786780199287706274837 100677505321841611231633)
                ·
                  rfl

theorem cell19_330866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_330866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330866 prefixEnd_330866 := by exact prefixLift 330866
  have htrace : WordTrace (prefixWord ++ tailWord_330866) baseStart_330866 baseEnd_330866 := by
    simpa [prefixWord, tailWord_330866, baseEnd_330866] using wordTrace_append hprefix tailTrace_330866
  have hstable : (prefixWord ++ tailWord_330866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330866).length < 2 ^ (prefixWord ++ tailWord_330866).sum := by decide
  have hdescent : baseEnd_330866 < baseStart_330866 := by decide
  rcases family_descends (prefixWord ++ tailWord_330866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330881 : List Nat := [1, 2, 4, 2, 2, 3, 2, 3]
def baseStart_330881 : Nat := 118140960795 + 330881 * 2 ^ 59
def prefixEnd_330881 : Nat := 4983230072969 + 3 ^ 40 * 330881 * 2
def baseEnd_330881 : Nat := 100682069594326020898259

theorem tailTrace_330881 : CollatzResearch.WordTrace tailWord_330881 prefixEnd_330881 100682069594326020898259 := by
  unfold tailWord_330881
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068221514282121820920497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8045481009521414547280331 12068221514282121820920497)
  ·
    refine ⟨9051166135711591365690373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12068221514282121820920497 9051166135711591365690373)
    ·
      refine ⟨1697093650445923381066945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9051166135711591365690373 1697093650445923381066945)
      ·
        refine ⟨1272820237834442535800209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1697093650445923381066945 1272820237834442535800209)
        ·
          refine ⟨954615178375831901850157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272820237834442535800209 954615178375831901850157)
          ·
            refine ⟨357980691890936963193809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 954615178375831901850157 357980691890936963193809)
            ·
              refine ⟨268485518918202722395357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357980691890936963193809 268485518918202722395357)
              ·
                refine ⟨100682069594326020898259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268485518918202722395357 100682069594326020898259)
                ·
                  rfl

theorem cell19_330881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_330881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330881 prefixEnd_330881 := by exact prefixLift 330881
  have htrace : WordTrace (prefixWord ++ tailWord_330881) baseStart_330881 baseEnd_330881 := by
    simpa [prefixWord, tailWord_330881, baseEnd_330881] using wordTrace_append hprefix tailTrace_330881
  have hstable : (prefixWord ++ tailWord_330881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330881).length < 2 ^ (prefixWord ++ tailWord_330881).sum := by decide
  have hdescent : baseEnd_330881 < baseStart_330881 := by decide
  rcases family_descends (prefixWord ++ tailWord_330881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330904 : List Nat := [2, 1, 2, 4, 2, 1, 7]
def baseStart_330904 : Nat := 118140960795 + 330904 * 2 ^ 59
def prefixEnd_330904 : Nat := 4983230072969 + 3 ^ 40 * 330904 * 2
def baseEnd_330904 : Nat := 33563022715156260795695

theorem tailTrace_330904 : CollatzResearch.WordTrace tailWord_330904 prefixEnd_330904 33563022715156260795695 := by
  unfold tailWord_330904
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034530196599398374503883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8046040262132531166005177 6034530196599398374503883)
  ·
    refine ⟨9051795294899097561755825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6034530196599398374503883 9051795294899097561755825)
    ·
      refine ⟨6788846471174323171316869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9051795294899097561755825 6788846471174323171316869)
      ·
        refine ⟨1272908713345185594621913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6788846471174323171316869 1272908713345185594621913)
        ·
          refine ⟨954681535008889195966435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272908713345185594621913 954681535008889195966435)
          ·
            refine ⟨1432022302513333793949653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954681535008889195966435 1432022302513333793949653)
            ·
              refine ⟨33563022715156260795695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1432022302513333793949653 33563022715156260795695)
              ·
                rfl

theorem cell19_330904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_330904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330904 prefixEnd_330904 := by exact prefixLift 330904
  have htrace : WordTrace (prefixWord ++ tailWord_330904) baseStart_330904 baseEnd_330904 := by
    simpa [prefixWord, tailWord_330904, baseEnd_330904] using wordTrace_append hprefix tailTrace_330904
  have hstable : (prefixWord ++ tailWord_330904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330904).length < 2 ^ (prefixWord ++ tailWord_330904).sum := by decide
  have hdescent : baseEnd_330904 < baseStart_330904 := by decide
  rcases family_descends (prefixWord ++ tailWord_330904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330957 : List Nat := [1, 6, 2, 2, 1, 7]
def baseStart_330957 : Nat := 118140960795 + 330957 * 2 ^ 59
def prefixEnd_330957 : Nat := 4983230072969 + 3 ^ 40 * 330957 * 2
def baseEnd_330957 : Nat := 11189466137953373689907

theorem tailTrace_330957 : CollatzResearch.WordTrace tailWord_330957 prefixEnd_330957 11189466137953373689907 := by
  unfold tailWord_330957
  simp only [CollatzResearch.WordTrace]
  refine ⟨12070993462006786800687125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8047328974671191200458083 12070993462006786800687125)
  ·
    refine ⟨565827818531568131282209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12070993462006786800687125 565827818531568131282209)
    ·
      refine ⟨424370863898676098461657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 565827818531568131282209 424370863898676098461657)
      ·
        refine ⟨318278147924007073846243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424370863898676098461657 318278147924007073846243)
        ·
          refine ⟨477417221886010610769365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318278147924007073846243 477417221886010610769365)
          ·
            refine ⟨11189466137953373689907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 477417221886010610769365 11189466137953373689907)
            ·
              rfl

theorem cell19_330957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 7].length) (baseStart_330957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330957 prefixEnd_330957 := by exact prefixLift 330957
  have htrace : WordTrace (prefixWord ++ tailWord_330957) baseStart_330957 baseEnd_330957 := by
    simpa [prefixWord, tailWord_330957, baseEnd_330957] using wordTrace_append hprefix tailTrace_330957
  have hstable : (prefixWord ++ tailWord_330957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330957).length < 2 ^ (prefixWord ++ tailWord_330957).sum := by decide
  have hdescent : baseEnd_330957 < baseStart_330957 := by decide
  rcases family_descends (prefixWord ++ tailWord_330957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330980 : List Nat := [2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_330980 : Nat := 118140960795 + 330980 * 2 ^ 59
def prefixEnd_330980 : Nat := 4983230072969 + 3 ^ 40 * 330980 * 2
def baseEnd_330980 : Nat := 100712193792723124697989

theorem tailTrace_330980 : CollatzResearch.WordTrace tailWord_330980 prefixEnd_330980 100712193792723124697989 := by
  unfold tailWord_330980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035916170461730864387197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8047888227282307819182929 6035916170461730864387197)
  ·
    refine ⟨2263468563923149074145199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6035916170461730864387197 2263468563923149074145199)
    ·
      refine ⟨3395202845884723611217799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2263468563923149074145199 3395202845884723611217799)
      ·
        refine ⟨5092804268827085416826699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3395202845884723611217799 5092804268827085416826699)
        ·
          refine ⟨7639206403240628125240049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5092804268827085416826699 7639206403240628125240049)
          ·
            refine ⟨5729404802430471093930037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7639206403240628125240049 5729404802430471093930037)
            ·
              refine ⟨537131700227856665055941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5729404802430471093930037 537131700227856665055941)
              ·
                refine ⟨100712193792723124697989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537131700227856665055941 100712193792723124697989)
                ·
                  rfl

theorem cell19_330980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_330980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_330980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_330980 prefixEnd_330980 := by exact prefixLift 330980
  have htrace : WordTrace (prefixWord ++ tailWord_330980) baseStart_330980 baseEnd_330980 := by
    simpa [prefixWord, tailWord_330980, baseEnd_330980] using wordTrace_append hprefix tailTrace_330980
  have hstable : (prefixWord ++ tailWord_330980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330980).length < 2 ^ (prefixWord ++ tailWord_330980).sum := by decide
  have hdescent : baseEnd_330980 < baseStart_330980 := by decide
  rcases family_descends (prefixWord ++ tailWord_330980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331073 : List Nat := [1, 2, 5, 2, 1, 3, 5]
def baseStart_331073 : Nat := 118140960795 + 331073 * 2 ^ 59
def prefixEnd_331073 : Nat := 4983230072969 + 3 ^ 40 * 331073 * 2
def baseEnd_331073 : Nat := 33580164094042154877023

theorem tailTrace_331073 : CollatzResearch.WordTrace tailWord_331073 prefixEnd_331073 33580164094042154877023 := by
  unfold tailWord_331073
  simp only [CollatzResearch.WordTrace]
  refine ⟨12075224329586538611909873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8050149553057692407939915 12075224329586538611909873)
  ·
    refine ⟨9056418247189903958932405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12075224329586538611909873 9056418247189903958932405)
    ·
      refine ⟨849039210674053496149913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9056418247189903958932405 849039210674053496149913)
      ·
        refine ⟨636779408005540122112435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 849039210674053496149913 636779408005540122112435)
        ·
          refine ⟨955169112008310183168653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636779408005540122112435 955169112008310183168653)
          ·
            refine ⟨358188417003116318688245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 955169112008310183168653 358188417003116318688245)
            ·
              refine ⟨33580164094042154877023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 358188417003116318688245 33580164094042154877023)
              ·
                rfl

theorem cell19_331073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_331073 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331073 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331073 prefixEnd_331073 := by exact prefixLift 331073
  have htrace : WordTrace (prefixWord ++ tailWord_331073) baseStart_331073 baseEnd_331073 := by
    simpa [prefixWord, tailWord_331073, baseEnd_331073] using wordTrace_append hprefix tailTrace_331073
  have hstable : (prefixWord ++ tailWord_331073).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331073).length < 2 ^ (prefixWord ++ tailWord_331073).sum := by decide
  have hdescent : baseEnd_331073 < baseStart_331073 := by decide
  rcases family_descends (prefixWord ++ tailWord_331073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331189 : List Nat := [1, 3, 3, 2, 2, 2, 6]
def baseStart_331189 : Nat := 118140960795 + 331189 * 2 ^ 59
def prefixEnd_331189 : Nat := 4983230072969 + 3 ^ 40 * 331189 * 2
def baseEnd_331189 : Nat := 33591929774224188684325

theorem tailTrace_331189 : CollatzResearch.WordTrace tailWord_331189 prefixEnd_331189 33591929774224188684325 := by
  unfold tailWord_331189
  simp only [CollatzResearch.WordTrace]
  refine ⟨12079455197166290423132621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8052970131444193615421747 12079455197166290423132621)
  ·
    refine ⟨4529795698937358908674733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12079455197166290423132621 4529795698937358908674733)
    ·
      refine ⟨1698673387101509590753025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4529795698937358908674733 1698673387101509590753025)
      ·
        refine ⟨1274005040326132193064769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1698673387101509590753025 1274005040326132193064769)
        ·
          refine ⟨955503780244599144798577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274005040326132193064769 955503780244599144798577)
          ·
            refine ⟨716627835183449358598933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955503780244599144798577 716627835183449358598933)
            ·
              refine ⟨33591929774224188684325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 716627835183449358598933 33591929774224188684325)
              ·
                rfl

theorem cell19_331189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_331189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331189 prefixEnd_331189 := by exact prefixLift 331189
  have htrace : WordTrace (prefixWord ++ tailWord_331189) baseStart_331189 baseEnd_331189 := by
    simpa [prefixWord, tailWord_331189, baseEnd_331189] using wordTrace_append hprefix tailTrace_331189
  have hstable : (prefixWord ++ tailWord_331189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331189).length < 2 ^ (prefixWord ++ tailWord_331189).sum := by decide
  have hdescent : baseEnd_331189 < baseStart_331189 := by decide
  rcases family_descends (prefixWord ++ tailWord_331189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331191 : List Nat := [1, 1, 3, 1, 3, 2, 8]
def baseStart_331191 : Nat := 118140960795 + 331191 * 2 ^ 59
def prefixEnd_331191 : Nat := 4983230072969 + 3 ^ 40 * 331191 * 2
def baseEnd_331191 : Nat := 33592132630779051336175

theorem tailTrace_331191 : CollatzResearch.WordTrace tailWord_331191 prefixEnd_331191 33592132630779051336175 := by
  unfold tailWord_331191
  simp only [CollatzResearch.WordTrace]
  refine ⟨12079528143159044764705427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8053018762106029843136951 12079528143159044764705427)
  ·
    refine ⟨18119292214738567147058141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12079528143159044764705427 18119292214738567147058141)
    ·
      refine ⟨6794734580526962680146803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18119292214738567147058141 6794734580526962680146803)
      ·
        refine ⟨10192101870790444020220205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6794734580526962680146803 10192101870790444020220205)
        ·
          refine ⟨3822038201546416507582577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10192101870790444020220205 3822038201546416507582577)
          ·
            refine ⟨2866528651159812380686933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3822038201546416507582577 2866528651159812380686933)
            ·
              refine ⟨33592132630779051336175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2866528651159812380686933 33592132630779051336175)
              ·
                rfl

theorem cell19_331191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_331191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331191 prefixEnd_331191 := by exact prefixLift 331191
  have htrace : WordTrace (prefixWord ++ tailWord_331191) baseStart_331191 baseEnd_331191 := by
    simpa [prefixWord, tailWord_331191, baseEnd_331191] using wordTrace_append hprefix tailTrace_331191
  have hstable : (prefixWord ++ tailWord_331191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331191).length < 2 ^ (prefixWord ++ tailWord_331191).sum := by decide
  have hdescent : baseEnd_331191 < baseStart_331191 := by decide
  rcases family_descends (prefixWord ++ tailWord_331191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331225 : List Nat := [1, 2, 1, 2, 4, 4, 2, 3]
def baseStart_331225 : Nat := 118140960795 + 331225 * 2 ^ 59
def prefixEnd_331225 : Nat := 4983230072969 + 3 ^ 40 * 331225 * 2
def baseEnd_331225 : Nat := 100786743576635149252877

theorem tailTrace_331225 : CollatzResearch.WordTrace tailWord_331225 prefixEnd_331225 100786743576635149252877 := by
  unfold tailWord_331225
  simp only [CollatzResearch.WordTrace]
  refine ⟨12080768225035868571443129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8053845483357245714295419 12080768225035868571443129)
  ·
    refine ⟨9060576168776901428582347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12080768225035868571443129 9060576168776901428582347)
    ·
      refine ⟨13590864253165352142873521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9060576168776901428582347 13590864253165352142873521)
      ·
        refine ⟨10193148189874014107155141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13590864253165352142873521 10193148189874014107155141)
        ·
          refine ⟨1911215285601377645091589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10193148189874014107155141 1911215285601377645091589)
          ·
            refine ⟨358352866050258308454673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1911215285601377645091589 358352866050258308454673)
            ·
              refine ⟨268764649537693731341005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358352866050258308454673 268764649537693731341005)
              ·
                refine ⟨100786743576635149252877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268764649537693731341005 100786743576635149252877)
                ·
                  rfl

theorem cell19_331225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_331225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331225 prefixEnd_331225 := by exact prefixLift 331225
  have htrace : WordTrace (prefixWord ++ tailWord_331225) baseStart_331225 baseEnd_331225 := by
    simpa [prefixWord, tailWord_331225, baseEnd_331225] using wordTrace_append hprefix tailTrace_331225
  have hstable : (prefixWord ++ tailWord_331225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331225).length < 2 ^ (prefixWord ++ tailWord_331225).sum := by decide
  have hdescent : baseEnd_331225 < baseStart_331225 := by decide
  rcases family_descends (prefixWord ++ tailWord_331225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
