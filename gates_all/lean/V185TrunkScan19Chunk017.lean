import V185TrunkScan19Chunk016

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_171304 : List Nat := [2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_171304 : Nat := 118140960795 + 171304 * 2 ^ 59
def prefixEnd_171304 : Nat := 4983230072969 + 3 ^ 40 * 171304 * 2
def baseEnd_171304 : Nat := 52125208911349929488707

theorem tailTrace_171304 : CollatzResearch.WordTrace tailWord_171304 prefixEnd_171304 52125208911349929488707 := by
  unfold tailWord_171304
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123985085701169619544483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4165313447601559492725977 3123985085701169619544483)
  ·
    refine ⟨4685977628551754429316725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3123985085701169619544483 4685977628551754429316725)
    ·
      refine ⟨439310402676726977748443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4685977628551754429316725 439310402676726977748443)
      ·
        refine ⟨658965604015090466622665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439310402676726977748443 658965604015090466622665)
        ·
          refine ⟨494224203011317849966999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658965604015090466622665 494224203011317849966999)
          ·
            refine ⟨741336304516976774950499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494224203011317849966999 741336304516976774950499)
            ·
              refine ⟨1112004456775465162425749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741336304516976774950499 1112004456775465162425749)
              ·
                refine ⟨52125208911349929488707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1112004456775465162425749 52125208911349929488707)
                ·
                  rfl

theorem cell19_171304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_171304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171304 prefixEnd_171304 := by exact prefixLift 171304
  have htrace : WordTrace (prefixWord ++ tailWord_171304) baseStart_171304 baseEnd_171304 := by
    simpa [prefixWord, tailWord_171304, baseEnd_171304] using wordTrace_append hprefix tailTrace_171304
  have hstable : (prefixWord ++ tailWord_171304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171304).length < 2 ^ (prefixWord ++ tailWord_171304).sum := by decide
  have hdescent : baseEnd_171304 < baseStart_171304 := by decide
  rcases family_descends (prefixWord ++ tailWord_171304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171496 : List Nat := [2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_171496 : Nat := 118140960795 + 171496 * 2 ^ 59
def prefixEnd_171496 : Nat := 4983230072969 + 3 ^ 40 * 171496 * 2
def baseEnd_171496 : Nat := 52183631599150373221517

theorem tailTrace_171496 : CollatzResearch.WordTrace tailWord_171496 prefixEnd_171496 52183631599150373221517 := by
  unfold tailWord_171496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3127486493353378015039171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4169981991137837353385561 3127486493353378015039171)
  ·
    refine ⟨4691229740030067022558757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3127486493353378015039171 4691229740030067022558757)
    ·
      refine ⟨879605576255637566729767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4691229740030067022558757 879605576255637566729767)
      ·
        refine ⟨1319408364383456350094651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879605576255637566729767 1319408364383456350094651)
        ·
          refine ⟨1979112546575184525141977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319408364383456350094651 1979112546575184525141977)
          ·
            refine ⟨1484334409931388393856483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1979112546575184525141977 1484334409931388393856483)
            ·
              refine ⟨2226501614897082590784725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484334409931388393856483 2226501614897082590784725)
              ·
                refine ⟨52183631599150373221517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2226501614897082590784725 52183631599150373221517)
                ·
                  rfl

theorem cell19_171496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_171496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171496 prefixEnd_171496 := by exact prefixLift 171496
  have htrace : WordTrace (prefixWord ++ tailWord_171496) baseStart_171496 baseEnd_171496 := by
    simpa [prefixWord, tailWord_171496, baseEnd_171496] using wordTrace_append hprefix tailTrace_171496
  have hstable : (prefixWord ++ tailWord_171496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171496).length < 2 ^ (prefixWord ++ tailWord_171496).sum := by decide
  have hdescent : baseEnd_171496 < baseStart_171496 := by decide
  rcases family_descends (prefixWord ++ tailWord_171496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171648 : List Nat := [2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_171648 : Nat := 118140960795 + 171648 * 2 ^ 59
def prefixEnd_171648 : Nat := 4983230072969 + 3 ^ 40 * 171648 * 2
def baseEnd_171648 : Nat := 52229882893659057843325

theorem tailTrace_171648 : CollatzResearch.WordTrace tailWord_171648 prefixEnd_171648 52229882893659057843325 := by
  unfold tailWord_171648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130258441078042994805799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4173677921437390659741065 3130258441078042994805799)
  ·
    refine ⟨4695387661617064492208699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3130258441078042994805799 4695387661617064492208699)
    ·
      refine ⟨7043081492425596738313049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695387661617064492208699 7043081492425596738313049)
      ·
        refine ⟨5282311119319197553734787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7043081492425596738313049 5282311119319197553734787)
        ·
          refine ⟨7923466678978796330602181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282311119319197553734787 7923466678978796330602181)
          ·
            refine ⟨1485650002308524311987909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7923466678978796330602181 1485650002308524311987909)
            ·
              refine ⟨278559375432848308497733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1485650002308524311987909 278559375432848308497733)
              ·
                refine ⟨52229882893659057843325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278559375432848308497733 52229882893659057843325)
                ·
                  rfl

theorem cell19_171648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_171648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171648 prefixEnd_171648 := by exact prefixLift 171648
  have htrace : WordTrace (prefixWord ++ tailWord_171648) baseStart_171648 baseEnd_171648 := by
    simpa [prefixWord, tailWord_171648, baseEnd_171648] using wordTrace_append hprefix tailTrace_171648
  have hstable : (prefixWord ++ tailWord_171648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171648).length < 2 ^ (prefixWord ++ tailWord_171648).sum := by decide
  have hdescent : baseEnd_171648 < baseStart_171648 := by decide
  rcases family_descends (prefixWord ++ tailWord_171648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171682 : List Nat := [3, 3, 1, 4, 2, 6]
def baseStart_171682 : Nat := 118140960795 + 171682 * 2 ^ 59
def prefixEnd_171682 : Nat := 4983230072969 + 3 ^ 40 * 171682 * 2
def baseEnd_171682 : Nat := 5804469841995228120853

theorem tailTrace_171682 : CollatzResearch.WordTrace tailWord_171682 prefixEnd_171682 5804469841995228120853 := by
  unfold tailWord_171682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565439241008227449087325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4174504642688606530899533 1565439241008227449087325)
  ·
    refine ⟨587039715378085293407747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1565439241008227449087325 587039715378085293407747)
    ·
      refine ⟨880559573067127940111621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587039715378085293407747 880559573067127940111621)
      ·
        refine ⟨165104919950086488770929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 880559573067127940111621 165104919950086488770929)
        ·
          refine ⟨123828689962564866578197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165104919950086488770929 123828689962564866578197)
          ·
            refine ⟨5804469841995228120853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123828689962564866578197 5804469841995228120853)
            ·
              rfl

theorem cell19_171682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 6].length) (baseStart_171682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171682 prefixEnd_171682 := by exact prefixLift 171682
  have htrace : WordTrace (prefixWord ++ tailWord_171682) baseStart_171682 baseEnd_171682 := by
    simpa [prefixWord, tailWord_171682, baseEnd_171682] using wordTrace_append hprefix tailTrace_171682
  have hstable : (prefixWord ++ tailWord_171682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171682).length < 2 ^ (prefixWord ++ tailWord_171682).sum := by decide
  have hdescent : baseEnd_171682 < baseStart_171682 := by decide
  rcases family_descends (prefixWord ++ tailWord_171682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171701 : List Nat := [1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_171701 : Nat := 118140960795 + 171701 * 2 ^ 59
def prefixEnd_171701 : Nat := 4983230072969 + 3 ^ 40 * 171701 * 2
def baseEnd_171701 : Nat := 52246009989770638665403

theorem tailTrace_171701 : CollatzResearch.WordTrace tailWord_171701 prefixEnd_171701 52246009989770638665403 := by
  unfold tailWord_171701
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262449950964076041290957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4174966633976050694193971 6262449950964076041290957)
  ·
    refine ⟨2348418731611528515484109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6262449950964076041290957 2348418731611528515484109)
    ·
      refine ⟨880657024354323193306541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2348418731611528515484109 880657024354323193306541)
      ·
        refine ⟨330246384132871197489953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 880657024354323193306541 330246384132871197489953)
        ·
          refine ⟨247684788099653398117465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330246384132871197489953 247684788099653398117465)
          ·
            refine ⟨185763591074740048588099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247684788099653398117465 185763591074740048588099)
            ·
              refine ⟨278645386612110072882149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185763591074740048588099 278645386612110072882149)
              ·
                refine ⟨52246009989770638665403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278645386612110072882149 52246009989770638665403)
                ·
                  rfl

theorem cell19_171701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_171701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171701 prefixEnd_171701 := by exact prefixLift 171701
  have htrace : WordTrace (prefixWord ++ tailWord_171701) baseStart_171701 baseEnd_171701 := by
    simpa [prefixWord, tailWord_171701, baseEnd_171701] using wordTrace_append hprefix tailTrace_171701
  have hstable : (prefixWord ++ tailWord_171701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171701).length < 2 ^ (prefixWord ++ tailWord_171701).sum := by decide
  have hdescent : baseEnd_171701 < baseStart_171701 := by decide
  rcases family_descends (prefixWord ++ tailWord_171701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171703 : List Nat := [1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_171703 : Nat := 118140960795 + 171703 * 2 ^ 59
def prefixEnd_171703 : Nat := 4983230072969 + 3 ^ 40 * 171703 * 2
def baseEnd_171703 : Nat := 52246618559435226620953

theorem tailTrace_171703 : CollatzResearch.WordTrace tailWord_171703 prefixEnd_171703 52246618559435226620953 := by
  unfold tailWord_171703
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262522896956830382863763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4175015264637886921909175 6262522896956830382863763)
  ·
    refine ⟨9393784345435245574295645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262522896956830382863763 9393784345435245574295645)
    ·
      refine ⟨3522669129538217090360867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9393784345435245574295645 3522669129538217090360867)
      ·
        refine ⟨5284003694307325635541301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3522669129538217090360867 5284003694307325635541301)
        ·
          refine ⟨495375346341311778331997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5284003694307325635541301 495375346341311778331997)
          ·
            refine ⟨185765754877991916874499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 495375346341311778331997 185765754877991916874499)
            ·
              refine ⟨278648632316987875311749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185765754877991916874499 278648632316987875311749)
              ·
                refine ⟨52246618559435226620953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278648632316987875311749 52246618559435226620953)
                ·
                  rfl

theorem cell19_171703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_171703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171703 prefixEnd_171703 := by exact prefixLift 171703
  have htrace : WordTrace (prefixWord ++ tailWord_171703) baseStart_171703 baseEnd_171703 := by
    simpa [prefixWord, tailWord_171703, baseEnd_171703] using wordTrace_append hprefix tailTrace_171703
  have hstable : (prefixWord ++ tailWord_171703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171703).length < 2 ^ (prefixWord ++ tailWord_171703).sum := by decide
  have hdescent : baseEnd_171703 < baseStart_171703 := by decide
  rcases family_descends (prefixWord ++ tailWord_171703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171705 : List Nat := [1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_171705 : Nat := 118140960795 + 171705 * 2 ^ 59
def prefixEnd_171705 : Nat := 4983230072969 + 3 ^ 40 * 171705 * 2
def baseEnd_171705 : Nat := 52247227129099814576503

theorem tailTrace_171705 : CollatzResearch.WordTrace tailWord_171705 prefixEnd_171705 52247227129099814576503 := by
  unfold tailWord_171705
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262595842949584724436569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4175063895299723149624379 6262595842949584724436569)
  ·
    refine ⟨4696946882212188543327427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6262595842949584724436569 4696946882212188543327427)
    ·
      refine ⟨7045420323318282814991141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4696946882212188543327427 7045420323318282814991141)
      ·
        refine ⟨1321016310622178027810839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7045420323318282814991141 1321016310622178027810839)
        ·
          refine ⟨1981524465933267041716259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321016310622178027810839 1981524465933267041716259)
          ·
            refine ⟨2972286698899900562574389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981524465933267041716259 2972286698899900562574389)
            ·
              refine ⟨278651878021865677741349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2972286698899900562574389 278651878021865677741349)
              ·
                refine ⟨52247227129099814576503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278651878021865677741349 52247227129099814576503)
                ·
                  rfl

theorem cell19_171705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_171705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171705 prefixEnd_171705 := by exact prefixLift 171705
  have htrace : WordTrace (prefixWord ++ tailWord_171705) baseStart_171705 baseEnd_171705 := by
    simpa [prefixWord, tailWord_171705, baseEnd_171705] using wordTrace_append hprefix tailTrace_171705
  have hstable : (prefixWord ++ tailWord_171705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171705).length < 2 ^ (prefixWord ++ tailWord_171705).sum := by decide
  have hdescent : baseEnd_171705 < baseStart_171705 := by decide
  rcases family_descends (prefixWord ++ tailWord_171705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171762 : List Nat := [3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_171762 : Nat := 118140960795 + 171762 * 2 ^ 59
def prefixEnd_171762 : Nat := 4983230072969 + 3 ^ 40 * 171762 * 2
def baseEnd_171762 : Nat := 52264571364540571309681

theorem tailTrace_171762 : CollatzResearch.WordTrace tailWord_171762 prefixEnd_171762 52264571364540571309681 := by
  unfold tailWord_171762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566168700935770864815385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4176449869162055639507693 1566168700935770864815385)
  ·
    refine ⟨1174626525701828148611539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1566168700935770864815385 1174626525701828148611539)
    ·
      refine ⟨1761939788552742222917309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174626525701828148611539 1761939788552742222917309)
      ·
        refine ⟨660727420707278333593991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1761939788552742222917309 660727420707278333593991)
        ·
          refine ⟨991091131060917500390987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660727420707278333593991 991091131060917500390987)
          ·
            refine ⟨1486636696591376250586481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991091131060917500390987 1486636696591376250586481)
            ·
              refine ⟨1114977522443532187939861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486636696591376250586481 1114977522443532187939861)
              ·
                refine ⟨52264571364540571309681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1114977522443532187939861 52264571364540571309681)
                ·
                  rfl

theorem cell19_171762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_171762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171762 prefixEnd_171762 := by exact prefixLift 171762
  have htrace : WordTrace (prefixWord ++ tailWord_171762) baseStart_171762 baseEnd_171762 := by
    simpa [prefixWord, tailWord_171762, baseEnd_171762] using wordTrace_append hprefix tailTrace_171762
  have hstable : (prefixWord ++ tailWord_171762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171762).length < 2 ^ (prefixWord ++ tailWord_171762).sum := by decide
  have hdescent : baseEnd_171762 < baseStart_171762 := by decide
  rcases family_descends (prefixWord ++ tailWord_171762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171874 : List Nat := [3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_171874 : Nat := 118140960795 + 171874 * 2 ^ 59
def prefixEnd_171874 : Nat := 4983230072969 + 3 ^ 40 * 171874 * 2
def baseEnd_171874 : Nat := 52298651265757496820487

theorem tailTrace_171874 : CollatzResearch.WordTrace tailWord_171874 prefixEnd_171874 52298651265757496820487 := by
  unfold tailWord_171874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567189944834331646834669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4179173186224884391559117 1567189944834331646834669)
  ·
    refine ⟨587696229312874367563001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1567189944834331646834669 587696229312874367563001)
    ·
      refine ⟨440772171984655775672251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 587696229312874367563001 440772171984655775672251)
      ·
        refine ⟨661158257976983663508377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440772171984655775672251 661158257976983663508377)
        ·
          refine ⟨495868693482737747631283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661158257976983663508377 495868693482737747631283)
          ·
            refine ⟨743803040224106621446925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495868693482737747631283 743803040224106621446925)
            ·
              refine ⟨278926140084039983042597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743803040224106621446925 278926140084039983042597)
              ·
                refine ⟨52298651265757496820487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278926140084039983042597 52298651265757496820487)
                ·
                  rfl

theorem cell19_171874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_171874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171874 prefixEnd_171874 := by exact prefixLift 171874
  have htrace : WordTrace (prefixWord ++ tailWord_171874) baseStart_171874 baseEnd_171874 := by
    simpa [prefixWord, tailWord_171874, baseEnd_171874] using wordTrace_append hprefix tailTrace_171874
  have hstable : (prefixWord ++ tailWord_171874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171874).length < 2 ^ (prefixWord ++ tailWord_171874).sum := by decide
  have hdescent : baseEnd_171874 < baseStart_171874 := by decide
  rcases family_descends (prefixWord ++ tailWord_171874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171893 : List Nat := [1, 3, 4, 1, 1, 1, 5, 3]
def baseStart_171893 : Nat := 118140960795 + 171893 * 2 ^ 59
def prefixEnd_171893 : Nat := 4983230072969 + 3 ^ 40 * 171893 * 2
def baseEnd_171893 : Nat := 52304432677571082398213

theorem tailTrace_171893 : CollatzResearch.WordTrace tailWord_171893 prefixEnd_171893 52304432677571082398213 := by
  unfold tailWord_171893
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269452766268492832280333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4179635177512328554853555 6269452766268492832280333)
  ·
    refine ⟨2351044787350684812105125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6269452766268492832280333 2351044787350684812105125)
    ·
      refine ⟨440820897628253402269711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2351044787350684812105125 440820897628253402269711)
      ·
        refine ⟨661231346442380103404567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440820897628253402269711 661231346442380103404567)
        ·
          refine ⟨991847019663570155106851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661231346442380103404567 991847019663570155106851)
          ·
            refine ⟨1487770529495355232660277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991847019663570155106851 1487770529495355232660277)
            ·
              refine ⟨139478487140189553061901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1487770529495355232660277 139478487140189553061901)
              ·
                refine ⟨52304432677571082398213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139478487140189553061901 52304432677571082398213)
                ·
                  rfl

theorem cell19_171893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_171893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171893 prefixEnd_171893 := by exact prefixLift 171893
  have htrace : WordTrace (prefixWord ++ tailWord_171893) baseStart_171893 baseEnd_171893 := by
    simpa [prefixWord, tailWord_171893, baseEnd_171893] using wordTrace_append hprefix tailTrace_171893
  have hstable : (prefixWord ++ tailWord_171893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171893).length < 2 ^ (prefixWord ++ tailWord_171893).sum := by decide
  have hdescent : baseEnd_171893 < baseStart_171893 := by decide
  rcases family_descends (prefixWord ++ tailWord_171893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171944 : List Nat := [2, 1, 6, 2, 2, 1, 2, 3]
def baseStart_171944 : Nat := 118140960795 + 171944 * 2 ^ 59
def prefixEnd_171944 : Nat := 4983230072969 + 3 ^ 40 * 171944 * 2
def baseEnd_171944 : Nat := 52319951204018075264741

theorem tailTrace_171944 : CollatzResearch.WordTrace tailWord_171944 prefixEnd_171944 52319951204018075264741 := by
  unfold tailWord_171944
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135656444541864271193443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4180875259389152361591257 3135656444541864271193443)
  ·
    refine ⟨4703484666812796406790165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3135656444541864271193443 4703484666812796406790165)
    ·
      refine ⟨220475843756849831568289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4703484666812796406790165 220475843756849831568289)
      ·
        refine ⟨165356882817637373676217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220475843756849831568289 165356882817637373676217)
        ·
          refine ⟨124017662113228030257163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165356882817637373676217 124017662113228030257163)
          ·
            refine ⟨186026493169842045385745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124017662113228030257163 186026493169842045385745)
            ·
              refine ⟨139519869877381534039309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186026493169842045385745 139519869877381534039309)
              ·
                refine ⟨52319951204018075264741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139519869877381534039309 52319951204018075264741)
                ·
                  rfl

theorem cell19_171944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_171944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171944 prefixEnd_171944 := by exact prefixLift 171944
  have htrace : WordTrace (prefixWord ++ tailWord_171944) baseStart_171944 baseEnd_171944 := by
    simpa [prefixWord, tailWord_171944, baseEnd_171944] using wordTrace_append hprefix tailTrace_171944
  have hstable : (prefixWord ++ tailWord_171944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171944).length < 2 ^ (prefixWord ++ tailWord_171944).sum := by decide
  have hdescent : baseEnd_171944 < baseStart_171944 := by decide
  rcases family_descends (prefixWord ++ tailWord_171944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172102 : List Nat := [6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_172102 : Nat := 118140960795 + 172102 * 2 ^ 59
def prefixEnd_172102 : Nat := 4983230072969 + 3 ^ 40 * 172102 * 2
def baseEnd_172102 : Nat := 52368028207520523753199

theorem tailTrace_172102 : CollatzResearch.WordTrace tailWord_172102 prefixEnd_172102 52368028207520523753199 := by
  unfold tailWord_172102
  simp only [CollatzResearch.WordTrace]
  refine ⟨196158613203478797707455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4184717081674214351092373 196158613203478797707455)
  ·
    refine ⟨294237919805218196561183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196158613203478797707455 294237919805218196561183)
    ·
      refine ⟨441356879707827294841775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294237919805218196561183 441356879707827294841775)
      ·
        refine ⟨662035319561740942262663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441356879707827294841775 662035319561740942262663)
        ·
          refine ⟨993052979342611413393995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662035319561740942262663 993052979342611413393995)
          ·
            refine ⟨1489579469013917120090993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993052979342611413393995 1489579469013917120090993)
            ·
              refine ⟨1117184601760437840068245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489579469013917120090993 1117184601760437840068245)
              ·
                refine ⟨52368028207520523753199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1117184601760437840068245 52368028207520523753199)
                ·
                  rfl

theorem cell19_172102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_172102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172102 prefixEnd_172102 := by exact prefixLift 172102
  have htrace : WordTrace (prefixWord ++ tailWord_172102) baseStart_172102 baseEnd_172102 := by
    simpa [prefixWord, tailWord_172102, baseEnd_172102] using wordTrace_append hprefix tailTrace_172102
  have hstable : (prefixWord ++ tailWord_172102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172102).length < 2 ^ (prefixWord ++ tailWord_172102).sum := by decide
  have hdescent : baseEnd_172102 < baseStart_172102 := by decide
  rcases family_descends (prefixWord ++ tailWord_172102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172106 : List Nat := [3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_172106 : Nat := 118140960795 + 172106 * 2 ^ 59
def prefixEnd_172106 : Nat := 4983230072969 + 3 ^ 40 * 172106 * 2
def baseEnd_172106 : Nat := 52369245346849699664299

theorem tailTrace_172106 : CollatzResearch.WordTrace tailWord_172106 prefixEnd_172106 52369245346849699664299 := by
  unfold tailWord_172106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569305378624207552446043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4184814342997886806522781 1569305378624207552446043)
  ·
    refine ⟨2353958067936311328669065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1569305378624207552446043 2353958067936311328669065)
    ·
      refine ⟨1765468550952233496501799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2353958067936311328669065 1765468550952233496501799)
      ·
        refine ⟨2648202826428350244752699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765468550952233496501799 2648202826428350244752699)
        ·
          refine ⟨3972304239642525367129049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648202826428350244752699 3972304239642525367129049)
          ·
            refine ⟨2979228179731894025346787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3972304239642525367129049 2979228179731894025346787)
            ·
              refine ⟨4468842269597841038020181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979228179731894025346787 4468842269597841038020181)
              ·
                refine ⟨52369245346849699664299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4468842269597841038020181 52369245346849699664299)
                ·
                  rfl

theorem cell19_172106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_172106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172106 prefixEnd_172106 := by exact prefixLift 172106
  have htrace : WordTrace (prefixWord ++ tailWord_172106) baseStart_172106 baseEnd_172106 := by
    simpa [prefixWord, tailWord_172106, baseEnd_172106] using wordTrace_append hprefix tailTrace_172106
  have hstable : (prefixWord ++ tailWord_172106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172106).length < 2 ^ (prefixWord ++ tailWord_172106).sum := by decide
  have hdescent : baseEnd_172106 < baseStart_172106 := by decide
  rcases family_descends (prefixWord ++ tailWord_172106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172144 : List Nat := [2, 1, 1, 1, 5, 2, 7]
def baseStart_172144 : Nat := 118140960795 + 172144 * 2 ^ 59
def prefixEnd_172144 : Nat := 4983230072969 + 3 ^ 40 * 172144 * 2
def baseEnd_172144 : Nat := 17460269390158956939917

theorem tailTrace_172144 : CollatzResearch.WordTrace tailWord_172144 prefixEnd_172144 17460269390158956939917 := by
  unfold tailWord_172144
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139303744179581349833743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4185738325572775133111657 3139303744179581349833743)
  ·
    refine ⟨4708955616269372024750615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3139303744179581349833743 4708955616269372024750615)
    ·
      refine ⟨7063433424404058037125923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708955616269372024750615 7063433424404058037125923)
      ·
        refine ⟨10595150136606087055688885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063433424404058037125923 10595150136606087055688885)
        ·
          refine ⟨993295325306820661470833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10595150136606087055688885 993295325306820661470833)
          ·
            refine ⟨744971493980115496103125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 993295325306820661470833 744971493980115496103125)
            ·
              refine ⟨17460269390158956939917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 744971493980115496103125 17460269390158956939917)
              ·
                rfl

theorem cell19_172144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_172144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172144 prefixEnd_172144 := by exact prefixLift 172144
  have htrace : WordTrace (prefixWord ++ tailWord_172144) baseStart_172144 baseEnd_172144 := by
    simpa [prefixWord, tailWord_172144, baseEnd_172144] using wordTrace_append hprefix tailTrace_172144
  have hstable : (prefixWord ++ tailWord_172144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172144).length < 2 ^ (prefixWord ++ tailWord_172144).sum := by decide
  have hdescent : baseEnd_172144 < baseStart_172144 := by decide
  rcases family_descends (prefixWord ++ tailWord_172144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172163 : List Nat := [1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_172163 : Nat := 118140960795 + 172163 * 2 ^ 59
def prefixEnd_172163 : Nat := 4983230072969 + 3 ^ 40 * 172163 * 2
def baseEnd_172163 : Nat := 52386589582290456397477

theorem tailTrace_172163 : CollatzResearch.WordTrace tailWord_172163 prefixEnd_172163 52386589582290456397477 := by
  unfold tailWord_172163
  simp only [CollatzResearch.WordTrace]
  refine ⟨6279300475290328944609143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4186200316860219296406095 6279300475290328944609143)
  ·
    refine ⟨9418950712935493416913715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6279300475290328944609143 9418950712935493416913715)
    ·
      refine ⟨14128426069403240125370573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9418950712935493416913715 14128426069403240125370573)
      ·
        refine ⟨5298159776026215047013965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14128426069403240125370573 5298159776026215047013965)
        ·
          refine ⟨1986809916009830642630237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5298159776026215047013965 1986809916009830642630237)
          ·
            refine ⟨745053718503686490986339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1986809916009830642630237 745053718503686490986339)
            ·
              refine ⟨1117580577755529736479509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745053718503686490986339 1117580577755529736479509)
              ·
                refine ⟨52386589582290456397477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1117580577755529736479509 52386589582290456397477)
                ·
                  rfl

theorem cell19_172163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_172163 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172163 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172163 prefixEnd_172163 := by exact prefixLift 172163
  have htrace : WordTrace (prefixWord ++ tailWord_172163) baseStart_172163 baseEnd_172163 := by
    simpa [prefixWord, tailWord_172163, baseEnd_172163] using wordTrace_append hprefix tailTrace_172163
  have hstable : (prefixWord ++ tailWord_172163).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172163).length < 2 ^ (prefixWord ++ tailWord_172163).sum := by decide
  have hdescent : baseEnd_172163 < baseStart_172163 := by decide
  rcases family_descends (prefixWord ++ tailWord_172163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172199 : List Nat := [1, 1, 6, 2, 2, 7]
def baseStart_172199 : Nat := 118140960795 + 172199 * 2 ^ 59
def prefixEnd_172199 : Nat := 4983230072969 + 3 ^ 40 * 172199 * 2
def baseEnd_172199 : Nat := 5821949315139226621931

theorem tailTrace_172199 : CollatzResearch.WordTrace tailWord_172199 prefixEnd_172199 5821949315139226621931 := by
  unfold tailWord_172199
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280613503159907092919651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4187075668773271395279767 6280613503159907092919651)
  ·
    refine ⟨9420920254739860639379477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6280613503159907092919651 9420920254739860639379477)
    ·
      refine ⟨441605636940930967470913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9420920254739860639379477 441605636940930967470913)
      ·
        refine ⟨331204227705698225603185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441605636940930967470913 331204227705698225603185)
        ·
          refine ⟨248403170779273669202389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331204227705698225603185 248403170779273669202389)
          ·
            refine ⟨5821949315139226621931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 248403170779273669202389 5821949315139226621931)
            ·
              rfl

theorem cell19_172199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_172199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172199 prefixEnd_172199 := by exact prefixLift 172199
  have htrace : WordTrace (prefixWord ++ tailWord_172199) baseStart_172199 baseEnd_172199 := by
    simpa [prefixWord, tailWord_172199, baseEnd_172199] using wordTrace_append hprefix tailTrace_172199
  have hstable : (prefixWord ++ tailWord_172199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172199).length < 2 ^ (prefixWord ++ tailWord_172199).sum := by decide
  have hdescent : baseEnd_172199 < baseStart_172199 := by decide
  rcases family_descends (prefixWord ++ tailWord_172199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172290 : List Nat := [3, 4, 1, 1, 2, 3, 2, 3]
def baseStart_172290 : Nat := 118140960795 + 172290 * 2 ^ 59
def prefixEnd_172290 : Nat := 4983230072969 + 3 ^ 40 * 172290 * 2
def baseEnd_172290 : Nat := 52425233755991791574909

theorem tailTrace_172290 : CollatzResearch.WordTrace tailWord_172290 prefixEnd_172290 52425233755991791574909 := by
  unfold tailWord_172290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570983136457557408620581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4189288363886819756321549 1570983136457557408620581)
  ·
    refine ⟨294559338085792014116359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1570983136457557408620581 294559338085792014116359)
    ·
      refine ⟨441839007128688021174539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294559338085792014116359 441839007128688021174539)
      ·
        refine ⟨662758510693032031761809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441839007128688021174539 662758510693032031761809)
        ·
          refine ⟨497068883019774023821357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662758510693032031761809 497068883019774023821357)
          ·
            refine ⟨186400831132415258933009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 497068883019774023821357 186400831132415258933009)
            ·
              refine ⟨139800623349311444199757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186400831132415258933009 139800623349311444199757)
              ·
                refine ⟨52425233755991791574909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139800623349311444199757 52425233755991791574909)
                ·
                  rfl

theorem cell19_172290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_172290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172290 prefixEnd_172290 := by exact prefixLift 172290
  have htrace : WordTrace (prefixWord ++ tailWord_172290) baseStart_172290 baseEnd_172290 := by
    simpa [prefixWord, tailWord_172290, baseEnd_172290] using wordTrace_append hprefix tailTrace_172290
  have hstable : (prefixWord ++ tailWord_172290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172290).length < 2 ^ (prefixWord ++ tailWord_172290).sum := by decide
  have hdescent : baseEnd_172290 < baseStart_172290 := by decide
  rcases family_descends (prefixWord ++ tailWord_172290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172330 : List Nat := [3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_172330 : Nat := 118140960795 + 172330 * 2 ^ 59
def prefixEnd_172330 : Nat := 4983230072969 + 3 ^ 40 * 172330 * 2
def baseEnd_172330 : Nat := 52437405149283550685911

theorem tailTrace_172330 : CollatzResearch.WordTrace tailWord_172330 prefixEnd_172330 52437405149283550685911 := by
  unfold tailWord_172330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1571347866421329116484611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4190260977123544310625629 1571347866421329116484611)
  ·
    refine ⟨2357021799631993674726917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1571347866421329116484611 2357021799631993674726917)
    ·
      refine ⟨441941587430998814011297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2357021799631993674726917 441941587430998814011297)
      ·
        refine ⟨331456190573249110508473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441941587430998814011297 331456190573249110508473)
        ·
          refine ⟨248592142929936832881355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331456190573249110508473 248592142929936832881355)
          ·
            refine ⟨372888214394905249322033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248592142929936832881355 372888214394905249322033)
            ·
              refine ⟨279666160796178936991525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372888214394905249322033 279666160796178936991525)
              ·
                refine ⟨52437405149283550685911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279666160796178936991525 52437405149283550685911)
                ·
                  rfl

theorem cell19_172330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_172330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172330 prefixEnd_172330 := by exact prefixLift 172330
  have htrace : WordTrace (prefixWord ++ tailWord_172330) baseStart_172330 baseEnd_172330 := by
    simpa [prefixWord, tailWord_172330, baseEnd_172330] using wordTrace_append hprefix tailTrace_172330
  have hstable : (prefixWord ++ tailWord_172330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172330).length < 2 ^ (prefixWord ++ tailWord_172330).sum := by decide
  have hdescent : baseEnd_172330 < baseStart_172330 := by decide
  rcases family_descends (prefixWord ++ tailWord_172330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172372 : List Nat := [2, 4, 1, 1, 2, 9]
def baseStart_172372 : Nat := 118140960795 + 172372 * 2 ^ 59
def prefixEnd_172372 : Nat := 4983230072969 + 3 ^ 40 * 172372 * 2
def baseEnd_172372 : Nat := 5827798345804433083607

theorem tailTrace_172372 : CollatzResearch.WordTrace tailWord_172372 prefixEnd_172372 5827798345804433083607 := by
  unfold tailWord_172372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143461665766578819483685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4191282221022105092644913 3143461665766578819483685)
  ·
    refine ⟨589399062331233528653191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3143461665766578819483685 589399062331233528653191)
    ·
      refine ⟨884098593496850292979787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 589399062331233528653191 884098593496850292979787)
      ·
        refine ⟨1326147890245275439469681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884098593496850292979787 1326147890245275439469681)
        ·
          refine ⟨994610917683956579602261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1326147890245275439469681 994610917683956579602261)
          ·
            refine ⟨5827798345804433083607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 994610917683956579602261 5827798345804433083607)
            ·
              rfl

theorem cell19_172372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_172372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172372 prefixEnd_172372 := by exact prefixLift 172372
  have htrace : WordTrace (prefixWord ++ tailWord_172372) baseStart_172372 baseEnd_172372 := by
    simpa [prefixWord, tailWord_172372, baseEnd_172372] using wordTrace_append hprefix tailTrace_172372
  have hstable : (prefixWord ++ tailWord_172372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172372).length < 2 ^ (prefixWord ++ tailWord_172372).sum := by decide
  have hdescent : baseEnd_172372 < baseStart_172372 := by decide
  rcases family_descends (prefixWord ++ tailWord_172372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172389 : List Nat := [1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_172389 : Nat := 118140960795 + 172389 * 2 ^ 59
def prefixEnd_172389 : Nat := 4983230072969 + 3 ^ 40 * 172389 * 2
def baseEnd_172389 : Nat := 52455357954388895374639

theorem tailTrace_172389 : CollatzResearch.WordTrace tailWord_172389 prefixEnd_172389 52455357954388895374639 := by
  unfold tailWord_172389
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287543372471569542336221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4191695581647713028224147 6287543372471569542336221)
  ·
    refine ⟨2357828764676838578376083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6287543372471569542336221 2357828764676838578376083)
    ·
      refine ⟨3536743147015257867564125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2357828764676838578376083 3536743147015257867564125)
      ·
        refine ⟨1326278680130721700336547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3536743147015257867564125 1326278680130721700336547)
        ·
          refine ⟨1989418020196082550504821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326278680130721700336547 1989418020196082550504821)
          ·
            refine ⟨186507939393382739109827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1989418020196082550504821 186507939393382739109827)
            ·
              refine ⟨279761909090074108664741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186507939393382739109827 279761909090074108664741)
              ·
                refine ⟨52455357954388895374639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279761909090074108664741 52455357954388895374639)
                ·
                  rfl

theorem cell19_172389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_172389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172389 prefixEnd_172389 := by exact prefixLift 172389
  have htrace : WordTrace (prefixWord ++ tailWord_172389) baseStart_172389 baseEnd_172389 := by
    simpa [prefixWord, tailWord_172389, baseEnd_172389] using wordTrace_append hprefix tailTrace_172389
  have hstable : (prefixWord ++ tailWord_172389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172389).length < 2 ^ (prefixWord ++ tailWord_172389).sum := by decide
  have hdescent : baseEnd_172389 < baseStart_172389 := by decide
  rcases family_descends (prefixWord ++ tailWord_172389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172461 : List Nat := [1, 5, 2, 2, 2, 2, 2, 3]
def baseStart_172461 : Nat := 118140960795 + 172461 * 2 ^ 59
def prefixEnd_172461 : Nat := 4983230072969 + 3 ^ 40 * 172461 * 2
def baseEnd_172461 : Nat := 52477266462314061774443

theorem tailTrace_172461 : CollatzResearch.WordTrace tailWord_172461 prefixEnd_172461 52477266462314061774443 := by
  unfold tailWord_172461
  simp only [CollatzResearch.WordTrace]
  refine ⟨6290169428210725838957237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4193446285473817225971491 6290169428210725838957237)
  ·
    refine ⟨589703383894755547402241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6290169428210725838957237 589703383894755547402241)
    ·
      refine ⟨442277537921066660551681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 589703383894755547402241 442277537921066660551681)
      ·
        refine ⟨331708153440799995413761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442277537921066660551681 331708153440799995413761)
        ·
          refine ⟨248781115080599996560321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331708153440799995413761 248781115080599996560321)
          ·
            refine ⟨186585836310449997420241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248781115080599996560321 186585836310449997420241)
            ·
              refine ⟨139939377232837498065181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186585836310449997420241 139939377232837498065181)
              ·
                refine ⟨52477266462314061774443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139939377232837498065181 52477266462314061774443)
                ·
                  rfl

theorem cell19_172461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_172461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172461 prefixEnd_172461 := by exact prefixLift 172461
  have htrace : WordTrace (prefixWord ++ tailWord_172461) baseStart_172461 baseEnd_172461 := by
    simpa [prefixWord, tailWord_172461, baseEnd_172461] using wordTrace_append hprefix tailTrace_172461
  have hstable : (prefixWord ++ tailWord_172461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172461).length < 2 ^ (prefixWord ++ tailWord_172461).sum := by decide
  have hdescent : baseEnd_172461 < baseStart_172461 := by decide
  rcases family_descends (prefixWord ++ tailWord_172461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172465 : List Nat := [1, 2, 2, 4, 1, 2, 4, 3]
def baseStart_172465 : Nat := 118140960795 + 172465 * 2 ^ 59
def prefixEnd_172465 : Nat := 4983230072969 + 3 ^ 40 * 172465 * 2
def baseEnd_172465 : Nat := 52478483601643237685543

theorem tailTrace_172465 : CollatzResearch.WordTrace tailWord_172465 prefixEnd_172465 52478483601643237685543 := by
  unfold tailWord_172465
  simp only [CollatzResearch.WordTrace]
  refine ⟨6290315320196234522102849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4193543546797489681401899 6290315320196234522102849)
  ·
    refine ⟨4717736490147175891577137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6290315320196234522102849 4717736490147175891577137)
    ·
      refine ⟨3538302367610381918682853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4717736490147175891577137 3538302367610381918682853)
      ·
        refine ⟨663431693926946609753035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3538302367610381918682853 663431693926946609753035)
        ·
          refine ⟨995147540890419914629553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663431693926946609753035 995147540890419914629553)
          ·
            refine ⟨746360655667814935972165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995147540890419914629553 746360655667814935972165)
            ·
              refine ⟨139942622937715300494781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 746360655667814935972165 139942622937715300494781)
              ·
                refine ⟨52478483601643237685543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139942622937715300494781 52478483601643237685543)
                ·
                  rfl

theorem cell19_172465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_172465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172465 prefixEnd_172465 := by exact prefixLift 172465
  have htrace : WordTrace (prefixWord ++ tailWord_172465) baseStart_172465 baseEnd_172465 := by
    simpa [prefixWord, tailWord_172465, baseEnd_172465] using wordTrace_append hprefix tailTrace_172465
  have hstable : (prefixWord ++ tailWord_172465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172465).length < 2 ^ (prefixWord ++ tailWord_172465).sum := by decide
  have hdescent : baseEnd_172465 < baseStart_172465 := by decide
  rcases family_descends (prefixWord ++ tailWord_172465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172505 : List Nat := [1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_172505 : Nat := 118140960795 + 172505 * 2 ^ 59
def prefixEnd_172505 : Nat := 4983230072969 + 3 ^ 40 * 172505 * 2
def baseEnd_172505 : Nat := 52490654994934996796545

theorem tailTrace_172505 : CollatzResearch.WordTrace tailWord_172505 prefixEnd_172505 52490654994934996796545 := by
  unfold tailWord_172505
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291774240051321353558969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4194516160034214235705979 6291774240051321353558969)
  ·
    refine ⟨4718830680038491015169227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6291774240051321353558969 4718830680038491015169227)
    ·
      refine ⟨7078246020057736522753841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4718830680038491015169227 7078246020057736522753841)
      ·
        refine ⟨5308684515043302392065381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7078246020057736522753841 5308684515043302392065381)
        ·
          refine ⟨995378346570619198512259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5308684515043302392065381 995378346570619198512259)
          ·
            refine ⟨1493067519855928797768389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995378346570619198512259 1493067519855928797768389)
            ·
              refine ⟨279950159972986649581573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1493067519855928797768389 279950159972986649581573)
              ·
                refine ⟨52490654994934996796545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279950159972986649581573 52490654994934996796545)
                ·
                  rfl

theorem cell19_172505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_172505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172505 prefixEnd_172505 := by exact prefixLift 172505
  have htrace : WordTrace (prefixWord ++ tailWord_172505) baseStart_172505 baseEnd_172505 := by
    simpa [prefixWord, tailWord_172505, baseEnd_172505] using wordTrace_append hprefix tailTrace_172505
  have hstable : (prefixWord ++ tailWord_172505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172505).length < 2 ^ (prefixWord ++ tailWord_172505).sum := by decide
  have hdescent : baseEnd_172505 < baseStart_172505 := by decide
  rcases family_descends (prefixWord ++ tailWord_172505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172579 : List Nat := [1, 1, 1, 4, 4, 2, 3, 3]
def baseStart_172579 : Nat := 118140960795 + 172579 * 2 ^ 59
def prefixEnd_172579 : Nat := 4983230072969 + 3 ^ 40 * 172579 * 2
def baseEnd_172579 : Nat := 52513172072524751151899

theorem tailTrace_172579 : CollatzResearch.WordTrace tailWord_172579 prefixEnd_172579 52513172072524751151899 := by
  unfold tailWord_172579
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294473241783231991752791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4196315494522154661168527 6294473241783231991752791)
  ·
    refine ⟨9441709862674847987629187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6294473241783231991752791 9441709862674847987629187)
    ·
      refine ⟨14162564794012271981443781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9441709862674847987629187 14162564794012271981443781)
      ·
        refine ⟨2655480898877300996520709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14162564794012271981443781 2655480898877300996520709)
        ·
          refine ⟨497902668539493936847633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2655480898877300996520709 497902668539493936847633)
          ·
            refine ⟨373427001404620452635725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497902668539493936847633 373427001404620452635725)
            ·
              refine ⟨140035125526732669738397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373427001404620452635725 140035125526732669738397)
              ·
                refine ⟨52513172072524751151899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140035125526732669738397 52513172072524751151899)
                ·
                  rfl

theorem cell19_172579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_172579 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172579 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172579 prefixEnd_172579 := by exact prefixLift 172579
  have htrace : WordTrace (prefixWord ++ tailWord_172579) baseStart_172579 baseEnd_172579 := by
    simpa [prefixWord, tailWord_172579, baseEnd_172579] using wordTrace_append hprefix tailTrace_172579
  have hstable : (prefixWord ++ tailWord_172579).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172579).length < 2 ^ (prefixWord ++ tailWord_172579).sum := by decide
  have hdescent : baseEnd_172579 < baseStart_172579 := by decide
  rcases family_descends (prefixWord ++ tailWord_172579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172596 : List Nat := [2, 5, 1, 3, 1, 1, 6]
def baseStart_172596 : Nat := 118140960795 + 172596 * 2 ^ 59
def prefixEnd_172596 : Nat := 4983230072969 + 3 ^ 40 * 172596 * 2
def baseEnd_172596 : Nat := 17506114971557916258025

theorem tailTrace_172596 : CollatzResearch.WordTrace tailWord_172596 prefixEnd_172596 17506114971557916258025 := by
  unfold tailWord_172596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147546641360821947560821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4196728855147762596747761 3147546641360821947560821)
  ·
    refine ⟨295082497627577057583827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3147546641360821947560821 295082497627577057583827)
    ·
      refine ⟨442623746441365586375741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295082497627577057583827 442623746441365586375741)
      ·
        refine ⟨165983904915512094890903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442623746441365586375741 165983904915512094890903)
        ·
          refine ⟨248975857373268142336355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165983904915512094890903 248975857373268142336355)
          ·
            refine ⟨373463786059902213504533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248975857373268142336355 373463786059902213504533)
            ·
              refine ⟨17506114971557916258025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 373463786059902213504533 17506114971557916258025)
              ·
                rfl

theorem cell19_172596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_172596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172596 prefixEnd_172596 := by exact prefixLift 172596
  have htrace : WordTrace (prefixWord ++ tailWord_172596) baseStart_172596 baseEnd_172596 := by
    simpa [prefixWord, tailWord_172596, baseEnd_172596] using wordTrace_append hprefix tailTrace_172596
  have hstable : (prefixWord ++ tailWord_172596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172596).length < 2 ^ (prefixWord ++ tailWord_172596).sum := by decide
  have hdescent : baseEnd_172596 < baseStart_172596 := by decide
  rcases family_descends (prefixWord ++ tailWord_172596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172598 : List Nat := [5, 1, 2, 1, 2, 2, 6]
def baseStart_172598 : Nat := 118140960795 + 172598 * 2 ^ 59
def prefixEnd_172598 : Nat := 4983230072969 + 3 ^ 40 * 172598 * 2
def baseEnd_172598 : Nat := 17506317828112778909875

theorem tailTrace_172598 : CollatzResearch.WordTrace tailWord_172598 prefixEnd_172598 17506317828112778909875 := by
  unfold tailWord_172598
  simp only [CollatzResearch.WordTrace]
  refine ⟨393447889294649889793403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4196777485809598824462965 393447889294649889793403)
  ·
    refine ⟨590171833941974834690105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393447889294649889793403 590171833941974834690105)
    ·
      refine ⟨442628875456481126017579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 590171833941974834690105 442628875456481126017579)
      ·
        refine ⟨663943313184721689026369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442628875456481126017579 663943313184721689026369)
        ·
          refine ⟨497957484888541266769777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663943313184721689026369 497957484888541266769777)
          ·
            refine ⟨373468113666405950077333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497957484888541266769777 373468113666405950077333)
            ·
              refine ⟨17506317828112778909875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 373468113666405950077333 17506317828112778909875)
              ·
                rfl

theorem cell19_172598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_172598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172598 prefixEnd_172598 := by exact prefixLift 172598
  have htrace : WordTrace (prefixWord ++ tailWord_172598) baseStart_172598 baseEnd_172598 := by
    simpa [prefixWord, tailWord_172598, baseEnd_172598] using wordTrace_append hprefix tailTrace_172598
  have hstable : (prefixWord ++ tailWord_172598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172598).length < 2 ^ (prefixWord ++ tailWord_172598).sum := by decide
  have hdescent : baseEnd_172598 < baseStart_172598 := by decide
  rcases family_descends (prefixWord ++ tailWord_172598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172636 : List Nat := [2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_172636 : Nat := 118140960795 + 172636 * 2 ^ 59
def prefixEnd_172636 : Nat := 4983230072969 + 3 ^ 40 * 172636 * 2
def baseEnd_172636 : Nat := 52530516307965507885077

theorem tailTrace_172636 : CollatzResearch.WordTrace tailWord_172636 prefixEnd_172636 52530516307965507885077 := by
  unfold tailWord_172636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148276101288365363288881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4197701468384487151051841 3148276101288365363288881)
  ·
    refine ⟨2361207075966274022466661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3148276101288365363288881 2361207075966274022466661)
    ·
      refine ⟨442726326743676379212499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2361207075966274022466661 442726326743676379212499)
      ·
        refine ⟨664089490115514568818749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442726326743676379212499 664089490115514568818749)
        ·
          refine ⟨249033558793317963307031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664089490115514568818749 249033558793317963307031)
          ·
            refine ⟨373550338189976944960547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249033558793317963307031 373550338189976944960547)
            ·
              refine ⟨560325507284965417440821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373550338189976944960547 560325507284965417440821)
              ·
                refine ⟨52530516307965507885077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 560325507284965417440821 52530516307965507885077)
                ·
                  rfl

theorem cell19_172636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_172636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172636 prefixEnd_172636 := by exact prefixLift 172636
  have htrace : WordTrace (prefixWord ++ tailWord_172636) baseStart_172636 baseEnd_172636 := by
    simpa [prefixWord, tailWord_172636, baseEnd_172636] using wordTrace_append hprefix tailTrace_172636
  have hstable : (prefixWord ++ tailWord_172636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172636).length < 2 ^ (prefixWord ++ tailWord_172636).sum := by decide
  have hdescent : baseEnd_172636 < baseStart_172636 := by decide
  rcases family_descends (prefixWord ++ tailWord_172636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172676 : List Nat := [2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_172676 : Nat := 118140960795 + 172676 * 2 ^ 59
def prefixEnd_172676 : Nat := 4983230072969 + 3 ^ 40 * 172676 * 2
def baseEnd_172676 : Nat := 52542687701257266996079

theorem tailTrace_172676 : CollatzResearch.WordTrace tailWord_172676 prefixEnd_172676 52542687701257266996079 := by
  unfold tailWord_172676
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149005561215908779016941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4198674081621211705355921 3149005561215908779016941)
  ·
    refine ⟨1180877085455965792131353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3149005561215908779016941 1180877085455965792131353)
    ·
      refine ⟨885657814091974344098515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1180877085455965792131353 885657814091974344098515)
      ·
        refine ⟨1328486721137961516147773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885657814091974344098515 1328486721137961516147773)
        ·
          refine ⟨498182520426735568555415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1328486721137961516147773 498182520426735568555415)
          ·
            refine ⟨747273780640103352833123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498182520426735568555415 747273780640103352833123)
            ·
              refine ⟨1120910670960155029249685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747273780640103352833123 1120910670960155029249685)
              ·
                refine ⟨52542687701257266996079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1120910670960155029249685 52542687701257266996079)
                ·
                  rfl

theorem cell19_172676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_172676 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172676 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172676 prefixEnd_172676 := by exact prefixLift 172676
  have htrace : WordTrace (prefixWord ++ tailWord_172676) baseStart_172676 baseEnd_172676 := by
    simpa [prefixWord, tailWord_172676, baseEnd_172676] using wordTrace_append hprefix tailTrace_172676
  have hstable : (prefixWord ++ tailWord_172676).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172676).length < 2 ^ (prefixWord ++ tailWord_172676).sum := by decide
  have hdescent : baseEnd_172676 < baseStart_172676 := by decide
  rcases family_descends (prefixWord ++ tailWord_172676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172697 : List Nat := [1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_172697 : Nat := 118140960795 + 172697 * 2 ^ 59
def prefixEnd_172697 : Nat := 4983230072969 + 3 ^ 40 * 172697 * 2
def baseEnd_172697 : Nat := 52549077682735440529355

theorem tailTrace_172697 : CollatzResearch.WordTrace tailWord_172697 prefixEnd_172697 52549077682735440529355 := by
  unfold tailWord_172697
  simp only [CollatzResearch.WordTrace]
  refine ⟨6298777055355738144548345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4199184703570492096365563 6298777055355738144548345)
  ·
    refine ⟨4724082791516803608411259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6298777055355738144548345 4724082791516803608411259)
    ·
      refine ⟨7086124187275205412616889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4724082791516803608411259 7086124187275205412616889)
      ·
        refine ⟨5314593140456404059462667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7086124187275205412616889 5314593140456404059462667)
        ·
          refine ⟨7971889710684606089194001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5314593140456404059462667 7971889710684606089194001)
          ·
            refine ⟨5978917283013454566895501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7971889710684606089194001 5978917283013454566895501)
            ·
              refine ⟨2242093981130045462585813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5978917283013454566895501 2242093981130045462585813)
              ·
                refine ⟨52549077682735440529355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2242093981130045462585813 52549077682735440529355)
                ·
                  rfl

theorem cell19_172697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_172697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172697 prefixEnd_172697 := by exact prefixLift 172697
  have htrace : WordTrace (prefixWord ++ tailWord_172697) baseStart_172697 baseEnd_172697 := by
    simpa [prefixWord, tailWord_172697, baseEnd_172697] using wordTrace_append hprefix tailTrace_172697
  have hstable : (prefixWord ++ tailWord_172697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172697).length < 2 ^ (prefixWord ++ tailWord_172697).sum := by decide
  have hdescent : baseEnd_172697 < baseStart_172697 := by decide
  rcases family_descends (prefixWord ++ tailWord_172697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172733 : List Nat := [1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_172733 : Nat := 118140960795 + 172733 * 2 ^ 59
def prefixEnd_172733 : Nat := 4983230072969 + 3 ^ 40 * 172733 * 2
def baseEnd_172733 : Nat := 52560031936698023729257

theorem tailTrace_172733 : CollatzResearch.WordTrace tailWord_172733 prefixEnd_172733 52560031936698023729257 := by
  unfold tailWord_172733
  simp only [CollatzResearch.WordTrace]
  refine ⟨6300090083225316292858853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4200060055483544195239235 6300090083225316292858853)
  ·
    refine ⟨1181266890604746804911035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6300090083225316292858853 1181266890604746804911035)
    ·
      refine ⟨1771900335907120207366553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181266890604746804911035 1771900335907120207366553)
      ·
        refine ⟨1328925251930340155524915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1771900335907120207366553 1328925251930340155524915)
        ·
          refine ⟨1993387877895510233287373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328925251930340155524915 1993387877895510233287373)
          ·
            refine ⟨747520454210816337482765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1993387877895510233287373 747520454210816337482765)
            ·
              refine ⟨280320170329056126556037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 747520454210816337482765 280320170329056126556037)
              ·
                refine ⟨52560031936698023729257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280320170329056126556037 52560031936698023729257)
                ·
                  rfl

theorem cell19_172733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_172733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172733 prefixEnd_172733 := by exact prefixLift 172733
  have htrace : WordTrace (prefixWord ++ tailWord_172733) baseStart_172733 baseEnd_172733 := by
    simpa [prefixWord, tailWord_172733, baseEnd_172733] using wordTrace_append hprefix tailTrace_172733
  have hstable : (prefixWord ++ tailWord_172733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172733).length < 2 ^ (prefixWord ++ tailWord_172733).sum := by decide
  have hdescent : baseEnd_172733 < baseStart_172733 := by decide
  rcases family_descends (prefixWord ++ tailWord_172733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172750 : List Nat := [4, 1, 1, 1, 3, 3, 3, 3]
def baseStart_172750 : Nat := 118140960795 + 172750 * 2 ^ 59
def prefixEnd_172750 : Nat := 4983230072969 + 3 ^ 40 * 172750 * 2
def baseEnd_172750 : Nat := 52565204778847021351433

theorem tailTrace_172750 : CollatzResearch.WordTrace tailWord_172750 prefixEnd_172750 52565204778847021351433 := by
  unfold tailWord_172750
  simp only [CollatzResearch.WordTrace]
  refine ⟨787588765520466024528463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4200473416109152130818469 787588765520466024528463)
  ·
    refine ⟨1181383148280699036792695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 787588765520466024528463 1181383148280699036792695)
    ·
      refine ⟨1772074722421048555189043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181383148280699036792695 1772074722421048555189043)
      ·
        refine ⟨2658112083631572832783565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772074722421048555189043 2658112083631572832783565)
        ·
          refine ⟨996792031361839812293837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2658112083631572832783565 996792031361839812293837)
          ·
            refine ⟨373797011760689929610189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 996792031361839812293837 373797011760689929610189)
            ·
              refine ⟨140173879410258723603821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373797011760689929610189 140173879410258723603821)
              ·
                refine ⟨52565204778847021351433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140173879410258723603821 52565204778847021351433)
                ·
                  rfl

theorem cell19_172750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_172750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172750 prefixEnd_172750 := by exact prefixLift 172750
  have htrace : WordTrace (prefixWord ++ tailWord_172750) baseStart_172750 baseEnd_172750 := by
    simpa [prefixWord, tailWord_172750, baseEnd_172750] using wordTrace_append hprefix tailTrace_172750
  have hstable : (prefixWord ++ tailWord_172750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172750).length < 2 ^ (prefixWord ++ tailWord_172750).sum := by decide
  have hdescent : baseEnd_172750 < baseStart_172750 := by decide
  rcases family_descends (prefixWord ++ tailWord_172750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172771 : List Nat := [1, 1, 1, 7, 1, 2, 6]
def baseStart_172771 : Nat := 118140960795 + 172771 * 2 ^ 59
def prefixEnd_172771 : Nat := 4983230072969 + 3 ^ 40 * 172771 * 2
def baseEnd_172771 : Nat := 17523864920108398294903

theorem tailTrace_172771 : CollatzResearch.WordTrace tailWord_172771 prefixEnd_172771 17523864920108398294903 := by
  unfold tailWord_172771
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301476057087648782742167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4200984038058432521828111 6301476057087648782742167)
  ·
    refine ⟨9452214085631473174113251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6301476057087648782742167 9452214085631473174113251)
    ·
      refine ⟨14178321128447209761169877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9452214085631473174113251 14178321128447209761169877)
      ·
        refine ⟨332304401447981478777419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14178321128447209761169877 332304401447981478777419)
        ·
          refine ⟨498456602171972218166129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332304401447981478777419 498456602171972218166129)
          ·
            refine ⟨373842451628979163624597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498456602171972218166129 373842451628979163624597)
            ·
              refine ⟨17523864920108398294903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 373842451628979163624597 17523864920108398294903)
              ·
                rfl

theorem cell19_172771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_172771 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172771 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172771 prefixEnd_172771 := by exact prefixLift 172771
  have htrace : WordTrace (prefixWord ++ tailWord_172771) baseStart_172771 baseEnd_172771 := by
    simpa [prefixWord, tailWord_172771, baseEnd_172771] using wordTrace_append hprefix tailTrace_172771
  have hstable : (prefixWord ++ tailWord_172771).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172771).length < 2 ^ (prefixWord ++ tailWord_172771).sum := by decide
  have hdescent : baseEnd_172771 < baseStart_172771 := by decide
  rcases family_descends (prefixWord ++ tailWord_172771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172790 : List Nat := [5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_172790 : Nat := 118140960795 + 172790 * 2 ^ 59
def prefixEnd_172790 : Nat := 4983230072969 + 3 ^ 40 * 172790 * 2
def baseEnd_172790 : Nat := 52577376172138780462435

theorem tailTrace_172790 : CollatzResearch.WordTrace tailWord_172790 prefixEnd_172790 52577376172138780462435 := by
  unfold tailWord_172790
  simp only [CollatzResearch.WordTrace]
  refine ⟨393885565251175939230239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4201446029345876685122549 393885565251175939230239)
  ·
    refine ⟨590828347876763908845359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393885565251175939230239 590828347876763908845359)
    ·
      refine ⟨886242521815145863268039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590828347876763908845359 886242521815145863268039)
      ·
        refine ⟨1329363782722718794902059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886242521815145863268039 1329363782722718794902059)
        ·
          refine ⟨1994045674084078192353089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329363782722718794902059 1994045674084078192353089)
          ·
            refine ⟨1495534255563058644264817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994045674084078192353089 1495534255563058644264817)
            ·
              refine ⟨1121650691672293983198613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495534255563058644264817 1121650691672293983198613)
              ·
                refine ⟨52577376172138780462435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1121650691672293983198613 52577376172138780462435)
                ·
                  rfl

theorem cell19_172790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_172790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172790 prefixEnd_172790 := by exact prefixLift 172790
  have htrace : WordTrace (prefixWord ++ tailWord_172790) baseStart_172790 baseEnd_172790 := by
    simpa [prefixWord, tailWord_172790, baseEnd_172790] using wordTrace_append hprefix tailTrace_172790
  have hstable : (prefixWord ++ tailWord_172790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172790).length < 2 ^ (prefixWord ++ tailWord_172790).sum := by decide
  have hdescent : baseEnd_172790 < baseStart_172790 := by decide
  rcases family_descends (prefixWord ++ tailWord_172790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172792 : List Nat := [2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_172792 : Nat := 118140960795 + 172792 * 2 ^ 59
def prefixEnd_172792 : Nat := 4983230072969 + 3 ^ 40 * 172792 * 2
def baseEnd_172792 : Nat := 52577984741803368417985

theorem tailTrace_172792 : CollatzResearch.WordTrace tailWord_172792 prefixEnd_172792 52577984741803368417985 := by
  unfold tailWord_172792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151120995005784684628315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4201494660007712912837753 3151120995005784684628315)
  ·
    refine ⟨4726681492508677026942473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3151120995005784684628315 4726681492508677026942473)
    ·
      refine ⟨3545011119381507770206855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4726681492508677026942473 3545011119381507770206855)
      ·
        refine ⟨5317516679072261655310283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545011119381507770206855 5317516679072261655310283)
        ·
          refine ⟨7976275018608392482965425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5317516679072261655310283 7976275018608392482965425)
          ·
            refine ⟨5982206263956294362224069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7976275018608392482965425 5982206263956294362224069)
            ·
              refine ⟨1121663674491805192917013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5982206263956294362224069 1121663674491805192917013)
              ·
                refine ⟨52577984741803368417985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1121663674491805192917013 52577984741803368417985)
                ·
                  rfl

theorem cell19_172792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_172792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172792 prefixEnd_172792 := by exact prefixLift 172792
  have htrace : WordTrace (prefixWord ++ tailWord_172792) baseStart_172792 baseEnd_172792 := by
    simpa [prefixWord, tailWord_172792, baseEnd_172792] using wordTrace_append hprefix tailTrace_172792
  have hstable : (prefixWord ++ tailWord_172792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172792).length < 2 ^ (prefixWord ++ tailWord_172792).sum := by decide
  have hdescent : baseEnd_172792 < baseStart_172792 := by decide
  rcases family_descends (prefixWord ++ tailWord_172792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172807 : List Nat := [1, 1, 4, 4, 1, 1, 4, 3]
def baseStart_172807 : Nat := 118140960795 + 172807 * 2 ^ 59
def prefixEnd_172807 : Nat := 4983230072969 + 3 ^ 40 * 172807 * 2
def baseEnd_172807 : Nat := 52582549014287778084611

theorem tailTrace_172807 : CollatzResearch.WordTrace tailWord_172807 prefixEnd_172807 52582549014287778084611 := by
  unfold tailWord_172807
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302789084957226931052675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4201859389971484620701783 6302789084957226931052675)
  ·
    refine ⟨9454183627435840396579013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6302789084957226931052675 9454183627435840396579013)
    ·
      refine ⟨1772659430144220074358565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9454183627435840396579013 1772659430144220074358565)
      ·
        refine ⟨332373643152041263942231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1772659430144220074358565 332373643152041263942231)
        ·
          refine ⟨498560464728061895913347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332373643152041263942231 498560464728061895913347)
          ·
            refine ⟨747840697092092843870021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498560464728061895913347 747840697092092843870021)
            ·
              refine ⟨140220130704767408225629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 747840697092092843870021 140220130704767408225629)
              ·
                refine ⟨52582549014287778084611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140220130704767408225629 52582549014287778084611)
                ·
                  rfl

theorem cell19_172807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_172807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172807 prefixEnd_172807 := by exact prefixLift 172807
  have htrace : WordTrace (prefixWord ++ tailWord_172807) baseStart_172807 baseEnd_172807 := by
    simpa [prefixWord, tailWord_172807, baseEnd_172807] using wordTrace_append hprefix tailTrace_172807
  have hstable : (prefixWord ++ tailWord_172807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172807).length < 2 ^ (prefixWord ++ tailWord_172807).sum := by decide
  have hdescent : baseEnd_172807 < baseStart_172807 := by decide
  rcases family_descends (prefixWord ++ tailWord_172807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172809 : List Nat := [1, 2, 1, 1, 3, 2, 6, 3]
def baseStart_172809 : Nat := 118140960795 + 172809 * 2 ^ 59
def prefixEnd_172809 : Nat := 4983230072969 + 3 ^ 40 * 172809 * 2
def baseEnd_172809 : Nat := 52583157583952366040161

theorem tailTrace_172809 : CollatzResearch.WordTrace tailWord_172809 prefixEnd_172809 52583157583952366040161 := by
  unfold tailWord_172809
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302862030949981272625481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4201908020633320848416987 6302862030949981272625481)
  ·
    refine ⟨4727146523212485954469111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6302862030949981272625481 4727146523212485954469111)
    ·
      refine ⟨7090719784818728931703667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4727146523212485954469111 7090719784818728931703667)
      ·
        refine ⟨10636079677228093397555501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090719784818728931703667 10636079677228093397555501)
        ·
          refine ⟨3988529878960535024083313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10636079677228093397555501 3988529878960535024083313)
          ·
            refine ⟨2991397409220401268062485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3988529878960535024083313 2991397409220401268062485)
            ·
              refine ⟨140221753557206309440429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2991397409220401268062485 140221753557206309440429)
              ·
                refine ⟨52583157583952366040161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140221753557206309440429 52583157583952366040161)
                ·
                  rfl

theorem cell19_172809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_172809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172809 prefixEnd_172809 := by exact prefixLift 172809
  have htrace : WordTrace (prefixWord ++ tailWord_172809) baseStart_172809 baseEnd_172809 := by
    simpa [prefixWord, tailWord_172809, baseEnd_172809] using wordTrace_append hprefix tailTrace_172809
  have hstable : (prefixWord ++ tailWord_172809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172809).length < 2 ^ (prefixWord ++ tailWord_172809).sum := by decide
  have hdescent : baseEnd_172809 < baseStart_172809 := by decide
  rcases family_descends (prefixWord ++ tailWord_172809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172828 : List Nat := [2, 2, 3, 1, 1, 5, 5]
def baseStart_172828 : Nat := 118140960795 + 172828 * 2 ^ 59
def prefixEnd_172828 : Nat := 4983230072969 + 3 ^ 40 * 172828 * 2
def baseEnd_172828 : Nat := 17529646331921983872629

theorem tailTrace_172828 : CollatzResearch.WordTrace tailWord_172828 prefixEnd_172828 17529646331921983872629 := by
  unfold tailWord_172828
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151777508940573758783569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4202370011920765011711425 3151777508940573758783569)
  ·
    refine ⟨2363833131705430319087677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3151777508940573758783569 2363833131705430319087677)
    ·
      refine ⟨886437424389536369657879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2363833131705430319087677 886437424389536369657879)
      ·
        refine ⟨1329656136584304554486819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886437424389536369657879 1329656136584304554486819)
        ·
          refine ⟨1994484204876456831730229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329656136584304554486819 1994484204876456831730229)
          ·
            refine ⟨186982894207167827974709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1994484204876456831730229 186982894207167827974709)
            ·
              refine ⟨17529646331921983872629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186982894207167827974709 17529646331921983872629)
              ·
                rfl

theorem cell19_172828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_172828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172828 prefixEnd_172828 := by exact prefixLift 172828
  have htrace : WordTrace (prefixWord ++ tailWord_172828) baseStart_172828 baseEnd_172828 := by
    simpa [prefixWord, tailWord_172828, baseEnd_172828] using wordTrace_append hprefix tailTrace_172828
  have hstable : (prefixWord ++ tailWord_172828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172828).length < 2 ^ (prefixWord ++ tailWord_172828).sum := by decide
  have hdescent : baseEnd_172828 < baseStart_172828 := by decide
  rcases family_descends (prefixWord ++ tailWord_172828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172887 : List Nat := [1, 1, 3, 2, 4, 8]
def baseStart_172887 : Nat := 118140960795 + 172887 * 2 ^ 59
def prefixEnd_172887 : Nat := 4983230072969 + 3 ^ 40 * 172887 * 2
def baseEnd_172887 : Nat := 5845210200096810700735

theorem tailTrace_172887 : CollatzResearch.WordTrace tailWord_172887 prefixEnd_172887 5845210200096810700735 := by
  unfold tailWord_172887
  simp only [CollatzResearch.WordTrace]
  refine ⟨6305706924667400593964915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4203804616444933729309943 6305706924667400593964915)
  ·
    refine ⟨9458560387001100890947373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6305706924667400593964915 9458560387001100890947373)
    ·
      refine ⟨3546960145125412834105265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9458560387001100890947373 3546960145125412834105265)
      ·
        refine ⟨2660220108844059625578949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3546960145125412834105265 2660220108844059625578949)
        ·
          refine ⟨498791270408261179796053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2660220108844059625578949 498791270408261179796053)
          ·
            refine ⟨5845210200096810700735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 498791270408261179796053 5845210200096810700735)
            ·
              rfl

theorem cell19_172887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_172887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172887 prefixEnd_172887 := by exact prefixLift 172887
  have htrace : WordTrace (prefixWord ++ tailWord_172887) baseStart_172887 baseEnd_172887 := by
    simpa [prefixWord, tailWord_172887, baseEnd_172887] using wordTrace_append hprefix tailTrace_172887
  have hstable : (prefixWord ++ tailWord_172887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172887).length < 2 ^ (prefixWord ++ tailWord_172887).sum := by decide
  have hdescent : baseEnd_172887 < baseStart_172887 := by decide
  rcases family_descends (prefixWord ++ tailWord_172887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172904 : List Nat := [2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_172904 : Nat := 118140960795 + 172904 * 2 ^ 59
def prefixEnd_172904 : Nat := 4983230072969 + 3 ^ 40 * 172904 * 2
def baseEnd_172904 : Nat := 52612064643020293928791

theorem tailTrace_172904 : CollatzResearch.WordTrace tailWord_172904 prefixEnd_172904 52612064643020293928791 := by
  unfold tailWord_172904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153163482802906248666883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4204217977070541664889177 3153163482802906248666883)
  ·
    refine ⟨4729745224204359373000325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3153163482802906248666883 4729745224204359373000325)
    ·
      refine ⟨886827229538317382437561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4729745224204359373000325 886827229538317382437561)
      ·
        refine ⟨665120422153738036828171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 886827229538317382437561 665120422153738036828171)
        ·
          refine ⟨997680633230607055242257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665120422153738036828171 997680633230607055242257)
          ·
            refine ⟨748260474922955291431693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997680633230607055242257 748260474922955291431693)
            ·
              refine ⟨280597678096108234286885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 748260474922955291431693 280597678096108234286885)
              ·
                refine ⟨52612064643020293928791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280597678096108234286885 52612064643020293928791)
                ·
                  rfl

theorem cell19_172904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_172904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172904 prefixEnd_172904 := by exact prefixLift 172904
  have htrace : WordTrace (prefixWord ++ tailWord_172904) baseStart_172904 baseEnd_172904 := by
    simpa [prefixWord, tailWord_172904, baseEnd_172904] using wordTrace_append hprefix tailTrace_172904
  have hstable : (prefixWord ++ tailWord_172904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172904).length < 2 ^ (prefixWord ++ tailWord_172904).sum := by decide
  have hdescent : baseEnd_172904 < baseStart_172904 := by decide
  rcases family_descends (prefixWord ++ tailWord_172904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172925 : List Nat := [1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_172925 : Nat := 118140960795 + 172925 * 2 ^ 59
def prefixEnd_172925 : Nat := 4983230072969 + 3 ^ 40 * 172925 * 2
def baseEnd_172925 : Nat := 52618454624498467462067

theorem tailTrace_172925 : CollatzResearch.WordTrace tailWord_172925 prefixEnd_172925 52618454624498467462067 := by
  unfold tailWord_172925
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307092898529733083848229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4204728599019822055898819 6307092898529733083848229)
  ·
    refine ⟨1182579918474324953221543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6307092898529733083848229 1182579918474324953221543)
    ·
      refine ⟨1773869877711487429832315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182579918474324953221543 1773869877711487429832315)
      ·
        refine ⟨2660804816567231144748473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773869877711487429832315 2660804816567231144748473)
        ·
          refine ⟨1995603612425423358561355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2660804816567231144748473 1995603612425423358561355)
          ·
            refine ⟨2993405418638135037842033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995603612425423358561355 2993405418638135037842033)
            ·
              refine ⟨2245054063978601278381525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993405418638135037842033 2245054063978601278381525)
              ·
                refine ⟨52618454624498467462067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2245054063978601278381525 52618454624498467462067)
                ·
                  rfl

theorem cell19_172925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_172925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_172925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_172925 prefixEnd_172925 := by exact prefixLift 172925
  have htrace : WordTrace (prefixWord ++ tailWord_172925) baseStart_172925 baseEnd_172925 := by
    simpa [prefixWord, tailWord_172925, baseEnd_172925] using wordTrace_append hprefix tailTrace_172925
  have hstable : (prefixWord ++ tailWord_172925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172925).length < 2 ^ (prefixWord ++ tailWord_172925).sum := by decide
  have hdescent : baseEnd_172925 < baseStart_172925 := by decide
  rcases family_descends (prefixWord ++ tailWord_172925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173018 : List Nat := [3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_173018 : Nat := 118140960795 + 173018 * 2 ^ 59
def prefixEnd_173018 : Nat := 4983230072969 + 3 ^ 40 * 173018 * 2
def baseEnd_173018 : Nat := 52646753113901807395147

theorem tailTrace_173018 : CollatzResearch.WordTrace tailWord_173018 prefixEnd_173018 52646753113901807395147 := by
  unfold tailWord_173018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577621221798202491745927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4206989924795206644655805 1577621221798202491745927)
  ·
    refine ⟨2366431832697303737618891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1577621221798202491745927 2366431832697303737618891)
    ·
      refine ⟨3549647749045955606428337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366431832697303737618891 3549647749045955606428337)
      ·
        refine ⟨2662235811784466704821253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3549647749045955606428337 2662235811784466704821253)
        ·
          refine ⟨499169214709587507153985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2662235811784466704821253 499169214709587507153985)
          ·
            refine ⟨374376911032190630365489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499169214709587507153985 374376911032190630365489)
            ·
              refine ⟨280782683274142972774117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374376911032190630365489 280782683274142972774117)
              ·
                refine ⟨52646753113901807395147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280782683274142972774117 52646753113901807395147)
                ·
                  rfl

theorem cell19_173018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_173018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173018 prefixEnd_173018 := by exact prefixLift 173018
  have htrace : WordTrace (prefixWord ++ tailWord_173018) baseStart_173018 baseEnd_173018 := by
    simpa [prefixWord, tailWord_173018, baseEnd_173018] using wordTrace_append hprefix tailTrace_173018
  have hstable : (prefixWord ++ tailWord_173018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173018).length < 2 ^ (prefixWord ++ tailWord_173018).sum := by decide
  have hdescent : baseEnd_173018 < baseStart_173018 := by decide
  rcases family_descends (prefixWord ++ tailWord_173018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173039 : List Nat := [1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_173039 : Nat := 118140960795 + 173039 * 2 ^ 59
def prefixEnd_173039 : Nat := 4983230072969 + 3 ^ 40 * 173039 * 2
def baseEnd_173039 : Nat := 52653143095379980928423

theorem tailTrace_173039 : CollatzResearch.WordTrace tailWord_173039 prefixEnd_173039 52653143095379980928423 := by
  unfold tailWord_173039
  simp only [CollatzResearch.WordTrace]
  refine ⟨6311250820116730553498171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4207500546744487035665447 6311250820116730553498171)
  ·
    refine ⟨9466876230175095830247257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6311250820116730553498171 9466876230175095830247257)
    ·
      refine ⟨7100157172631321872685443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9466876230175095830247257 7100157172631321872685443)
      ·
        refine ⟨10650235758946982809028165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7100157172631321872685443 10650235758946982809028165)
        ·
          refine ⟨1996919204802559276692781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10650235758946982809028165 1996919204802559276692781)
          ·
            refine ⟨748844701800959728759793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1996919204802559276692781 748844701800959728759793)
            ·
              refine ⟨561633526350719796569845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748844701800959728759793 561633526350719796569845)
              ·
                refine ⟨52653143095379980928423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 561633526350719796569845 52653143095379980928423)
                ·
                  rfl

theorem cell19_173039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_173039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173039 prefixEnd_173039 := by exact prefixLift 173039
  have htrace : WordTrace (prefixWord ++ tailWord_173039) baseStart_173039 baseEnd_173039 := by
    simpa [prefixWord, tailWord_173039, baseEnd_173039] using wordTrace_append hprefix tailTrace_173039
  have hstable : (prefixWord ++ tailWord_173039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173039).length < 2 ^ (prefixWord ++ tailWord_173039).sum := by decide
  have hdescent : baseEnd_173039 < baseStart_173039 := by decide
  rcases family_descends (prefixWord ++ tailWord_173039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173054 : List Nat := [4, 2, 2, 2, 3, 6]
def baseStart_173054 : Nat := 118140960795 + 173054 * 2 ^ 59
def prefixEnd_173054 : Nat := 4983230072969 + 3 ^ 40 * 173054 * 2
def baseEnd_173054 : Nat := 5850856374207154510561

theorem tailTrace_173054 : CollatzResearch.WordTrace tailWord_173054 prefixEnd_173054 5850856374207154510561 := by
  unfold tailWord_173054
  simp only [CollatzResearch.WordTrace]
  refine ⟨788974739382798514411777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4207865276708258743529477 788974739382798514411777)
  ·
    refine ⟨591731054537098885808833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 788974739382798514411777 591731054537098885808833)
    ·
      refine ⟨443798290902824164356625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591731054537098885808833 443798290902824164356625)
      ·
        refine ⟨332848718177118123267469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443798290902824164356625 332848718177118123267469)
        ·
          refine ⟨124818269316419296225301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332848718177118123267469 124818269316419296225301)
          ·
            refine ⟨5850856374207154510561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124818269316419296225301 5850856374207154510561)
            ·
              rfl

theorem cell19_173054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 6].length) (baseStart_173054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173054 prefixEnd_173054 := by exact prefixLift 173054
  have htrace : WordTrace (prefixWord ++ tailWord_173054) baseStart_173054 baseEnd_173054 := by
    simpa [prefixWord, tailWord_173054, baseEnd_173054] using wordTrace_append hprefix tailTrace_173054
  have hstable : (prefixWord ++ tailWord_173054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173054).length < 2 ^ (prefixWord ++ tailWord_173054).sum := by decide
  have hdescent : baseEnd_173054 < baseStart_173054 := by decide
  rcases family_descends (prefixWord ++ tailWord_173054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173092 : List Nat := [2, 3, 1, 4, 1, 2, 3, 3]
def baseStart_173092 : Nat := 118140960795 + 173092 * 2 ^ 59
def prefixEnd_173092 : Nat := 4983230072969 + 3 ^ 40 * 173092 * 2
def baseEnd_173092 : Nat := 52669270191491561750501

theorem tailTrace_173092 : CollatzResearch.WordTrace tailWord_173092 prefixEnd_173092 52669270191491561750501 := by
  unfold tailWord_173092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156591944462360302588765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4208789259283147070118353 3156591944462360302588765)
  ·
    refine ⟨1183721979173385113470787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3156591944462360302588765 1183721979173385113470787)
    ·
      refine ⟨1775582968760077670206181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183721979173385113470787 1775582968760077670206181)
      ·
        refine ⟨332921806642514563163659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1775582968760077670206181 332921806642514563163659)
        ·
          refine ⟨499382709963771844745489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332921806642514563163659 499382709963771844745489)
          ·
            refine ⟨374537032472828883559117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499382709963771844745489 374537032472828883559117)
            ·
              refine ⟨140451387177310831334669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374537032472828883559117 140451387177310831334669)
              ·
                refine ⟨52669270191491561750501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140451387177310831334669 52669270191491561750501)
                ·
                  rfl

theorem cell19_173092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_173092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173092 prefixEnd_173092 := by exact prefixLift 173092
  have htrace : WordTrace (prefixWord ++ tailWord_173092) baseStart_173092 baseEnd_173092 := by
    simpa [prefixWord, tailWord_173092, baseEnd_173092] using wordTrace_append hprefix tailTrace_173092
  have hstable : (prefixWord ++ tailWord_173092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173092).length < 2 ^ (prefixWord ++ tailWord_173092).sum := by decide
  have hdescent : baseEnd_173092 < baseStart_173092 := by decide
  rcases family_descends (prefixWord ++ tailWord_173092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173134 : List Nat := [4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_173134 : Nat := 118140960795 + 173134 * 2 ^ 59
def prefixEnd_173134 : Nat := 4983230072969 + 3 ^ 40 * 173134 * 2
def baseEnd_173134 : Nat := 52682050154447908817053

theorem tailTrace_173134 : CollatzResearch.WordTrace tailWord_173134 prefixEnd_173134 52682050154447908817053 := by
  unfold tailWord_173134
  simp only [CollatzResearch.WordTrace]
  refine ⟨789339469346570222275807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4209810503181707852137637 789339469346570222275807)
  ·
    refine ⟨1184009204019855333413711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 789339469346570222275807 1184009204019855333413711)
    ·
      refine ⟨1776013806029783000120567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1184009204019855333413711 1776013806029783000120567)
      ·
        refine ⟨2664020709044674500180851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776013806029783000120567 2664020709044674500180851)
        ·
          refine ⟨3996031063567011750271277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664020709044674500180851 3996031063567011750271277)
          ·
            refine ⟨1498511648837629406351729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3996031063567011750271277 1498511648837629406351729)
            ·
              refine ⟨1123883736628222054763797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498511648837629406351729 1123883736628222054763797)
              ·
                refine ⟨52682050154447908817053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1123883736628222054763797 52682050154447908817053)
                ·
                  rfl

theorem cell19_173134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_173134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173134 prefixEnd_173134 := by exact prefixLift 173134
  have htrace : WordTrace (prefixWord ++ tailWord_173134) baseStart_173134 baseEnd_173134 := by
    simpa [prefixWord, tailWord_173134, baseEnd_173134] using wordTrace_append hprefix tailTrace_173134
  have hstable : (prefixWord ++ tailWord_173134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173134).length < 2 ^ (prefixWord ++ tailWord_173134).sum := by decide
  have hdescent : baseEnd_173134 < baseStart_173134 := by decide
  rcases family_descends (prefixWord ++ tailWord_173134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173149 : List Nat := [1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_173149 : Nat := 118140960795 + 173149 * 2 ^ 59
def prefixEnd_173149 : Nat := 4983230072969 + 3 ^ 40 * 173149 * 2
def baseEnd_173149 : Nat := 52686614426932318483679

theorem tailTrace_173149 : CollatzResearch.WordTrace tailWord_173149 prefixEnd_173149 52686614426932318483679 := by
  unfold tailWord_173149
  simp only [CollatzResearch.WordTrace]
  refine ⟨6315262849718219340002501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4210175233145479560001667 6315262849718219340002501)
  ·
    refine ⟨1184111784322166126250469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6315262849718219340002501 1184111784322166126250469)
    ·
      refine ⟨222020959560406148671963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1184111784322166126250469 222020959560406148671963)
      ·
        refine ⟨333031439340609223007945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222020959560406148671963 333031439340609223007945)
        ·
          refine ⟨249773579505456917255959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333031439340609223007945 249773579505456917255959)
          ·
            refine ⟨374660369258185375883939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249773579505456917255959 374660369258185375883939)
            ·
              refine ⟨561990553887278063825909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374660369258185375883939 561990553887278063825909)
              ·
                refine ⟨52686614426932318483679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 561990553887278063825909 52686614426932318483679)
                ·
                  rfl

theorem cell19_173149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_173149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173149 prefixEnd_173149 := by exact prefixLift 173149
  have htrace : WordTrace (prefixWord ++ tailWord_173149) baseStart_173149 baseEnd_173149 := by
    simpa [prefixWord, tailWord_173149, baseEnd_173149] using wordTrace_append hprefix tailTrace_173149
  have hstable : (prefixWord ++ tailWord_173149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173149).length < 2 ^ (prefixWord ++ tailWord_173149).sum := by decide
  have hdescent : baseEnd_173149 < baseStart_173149 := by decide
  rcases family_descends (prefixWord ++ tailWord_173149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173189 : List Nat := [1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_173189 : Nat := 118140960795 + 173189 * 2 ^ 59
def prefixEnd_173189 : Nat := 4983230072969 + 3 ^ 40 * 173189 * 2
def baseEnd_173189 : Nat := 52698785820224077594681

theorem tailTrace_173189 : CollatzResearch.WordTrace tailWord_173189 prefixEnd_173189 52698785820224077594681 := by
  unfold tailWord_173189
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316721769573306171458621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4211147846382204114305747 6316721769573306171458621)
  ·
    refine ⟨2368770663589989814296983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6316721769573306171458621 2368770663589989814296983)
    ·
      refine ⟨3553155995384984721445475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368770663589989814296983 3553155995384984721445475)
      ·
        refine ⟨5329733993077477082168213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553155995384984721445475 5329733993077477082168213)
        ·
          refine ⟨249831280925506738226635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5329733993077477082168213 249831280925506738226635)
          ·
            refine ⟨374746921388260107339953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249831280925506738226635 374746921388260107339953)
            ·
              refine ⟨281060191041195080504965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374746921388260107339953 281060191041195080504965)
              ·
                refine ⟨52698785820224077594681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281060191041195080504965 52698785820224077594681)
                ·
                  rfl

theorem cell19_173189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_173189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173189 prefixEnd_173189 := by exact prefixLift 173189
  have htrace : WordTrace (prefixWord ++ tailWord_173189) baseStart_173189 baseEnd_173189 := by
    simpa [prefixWord, tailWord_173189, baseEnd_173189] using wordTrace_append hprefix tailTrace_173189
  have hstable : (prefixWord ++ tailWord_173189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173189).length < 2 ^ (prefixWord ++ tailWord_173189).sum := by decide
  have hdescent : baseEnd_173189 < baseStart_173189 := by decide
  rcases family_descends (prefixWord ++ tailWord_173189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173229 : List Nat := [1, 5, 2, 1, 10]
def baseStart_173229 : Nat := 118140960795 + 173229 * 2 ^ 59
def prefixEnd_173229 : Nat := 4983230072969 + 3 ^ 40 * 173229 * 2
def baseEnd_173229 : Nat := 1952257674574660618729

theorem tailTrace_173229 : CollatzResearch.WordTrace tailWord_173229 prefixEnd_173229 1952257674574660618729 := by
  unfold tailWord_173229
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318180689428393002914741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4212120459618928668609827 6318180689428393002914741)
  ·
    refine ⟨592329439633911844023257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6318180689428393002914741 592329439633911844023257)
    ·
      refine ⟨444247079725433883017443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 592329439633911844023257 444247079725433883017443)
      ·
        refine ⟨666370619588150824526165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444247079725433883017443 666370619588150824526165)
        ·
          refine ⟨1952257674574660618729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 666370619588150824526165 1952257674574660618729)
          ·
            rfl

theorem cell19_173229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 10].length) (baseStart_173229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173229 prefixEnd_173229 := by exact prefixLift 173229
  have htrace : WordTrace (prefixWord ++ tailWord_173229) baseStart_173229 baseEnd_173229 := by
    simpa [prefixWord, tailWord_173229, baseEnd_173229] using wordTrace_append hprefix tailTrace_173229
  have hstable : (prefixWord ++ tailWord_173229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173229).length < 2 ^ (prefixWord ++ tailWord_173229).sum := by decide
  have hdescent : baseEnd_173229 < baseStart_173229 := by decide
  rcases family_descends (prefixWord ++ tailWord_173229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173246 : List Nat := [4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_173246 : Nat := 118140960795 + 173246 * 2 ^ 59
def prefixEnd_173246 : Nat := 4983230072969 + 3 ^ 40 * 173246 * 2
def baseEnd_173246 : Nat := 52716130055664834327859

theorem tailTrace_173246 : CollatzResearch.WordTrace tailWord_173246 prefixEnd_173246 52716130055664834327859 := by
  unfold tailWord_173246
  simp only [CollatzResearch.WordTrace]
  refine ⟨789850091295850613285449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4212533820244536604189061 789850091295850613285449)
  ·
    refine ⟨592387568471887959964087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 789850091295850613285449 592387568471887959964087)
    ·
      refine ⟨888581352707831939946131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592387568471887959964087 888581352707831939946131)
      ·
        refine ⟨1332872029061747909919197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888581352707831939946131 1332872029061747909919197)
        ·
          refine ⟨499827010898155466219699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1332872029061747909919197 499827010898155466219699)
          ·
            refine ⟨749740516347233199329549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499827010898155466219699 749740516347233199329549)
            ·
              refine ⟨281152693630212449748581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749740516347233199329549 281152693630212449748581)
              ·
                refine ⟨52716130055664834327859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281152693630212449748581 52716130055664834327859)
                ·
                  rfl

theorem cell19_173246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_173246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173246 prefixEnd_173246 := by exact prefixLift 173246
  have htrace : WordTrace (prefixWord ++ tailWord_173246) baseStart_173246 baseEnd_173246 := by
    simpa [prefixWord, tailWord_173246, baseEnd_173246] using wordTrace_append hprefix tailTrace_173246
  have hstable : (prefixWord ++ tailWord_173246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173246).length < 2 ^ (prefixWord ++ tailWord_173246).sum := by decide
  have hdescent : baseEnd_173246 < baseStart_173246 := by decide
  rcases family_descends (prefixWord ++ tailWord_173246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173320 : List Nat := [2, 1, 3, 2, 4, 2, 2, 3]
def baseStart_173320 : Nat := 118140960795 + 173320 * 2 ^ 59
def prefixEnd_173320 : Nat := 4983230072969 + 3 ^ 40 * 173320 * 2
def baseEnd_173320 : Nat := 52738647133254588683213

theorem tailTrace_173320 : CollatzResearch.WordTrace tailWord_173320 prefixEnd_173320 52738647133254588683213 := by
  unfold tailWord_173320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160749866049357772238707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4214333154732477029651609 3160749866049357772238707)
  ·
    refine ⟨4741124799074036658358061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3160749866049357772238707 4741124799074036658358061)
    ·
      refine ⟨1777921799652763746884273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4741124799074036658358061 1777921799652763746884273)
      ·
        refine ⟨1333441349739572810163205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1777921799652763746884273 1333441349739572810163205)
        ·
          refine ⟨250020253076169901905601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1333441349739572810163205 250020253076169901905601)
          ·
            refine ⟨187515189807127426429201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250020253076169901905601 187515189807127426429201)
            ·
              refine ⟨140636392355345569821901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187515189807127426429201 140636392355345569821901)
              ·
                refine ⟨52738647133254588683213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140636392355345569821901 52738647133254588683213)
                ·
                  rfl

theorem cell19_173320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_173320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173320 prefixEnd_173320 := by exact prefixLift 173320
  have htrace : WordTrace (prefixWord ++ tailWord_173320) baseStart_173320 baseEnd_173320 := by
    simpa [prefixWord, tailWord_173320, baseEnd_173320] using wordTrace_append hprefix tailTrace_173320
  have hstable : (prefixWord ++ tailWord_173320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173320).length < 2 ^ (prefixWord ++ tailWord_173320).sum := by decide
  have hdescent : baseEnd_173320 < baseStart_173320 := by decide
  rcases family_descends (prefixWord ++ tailWord_173320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173324 : List Nat := [2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_173324 : Nat := 118140960795 + 173324 * 2 ^ 59
def prefixEnd_173324 : Nat := 4983230072969 + 3 ^ 40 * 173324 * 2
def baseEnd_173324 : Nat := 52739864272583764594313

theorem tailTrace_173324 : CollatzResearch.WordTrace tailWord_173324 prefixEnd_173324 52739864272583764594313 := by
  unfold tailWord_173324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160822812042112113811513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4214430416056149485082017 3160822812042112113811513)
  ·
    refine ⟨2370617109031584085358635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3160822812042112113811513 2370617109031584085358635)
    ·
      refine ⟨3555925663547376128037953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370617109031584085358635 3555925663547376128037953)
      ·
        refine ⟨2666944247660532096028465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3555925663547376128037953 2666944247660532096028465)
        ·
          refine ⟨2000208185745399072021349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2666944247660532096028465 2000208185745399072021349)
          ·
            refine ⟨375039034827262326004003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2000208185745399072021349 375039034827262326004003)
            ·
              refine ⟨562558552240893489006005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375039034827262326004003 562558552240893489006005)
              ·
                refine ⟨52739864272583764594313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 562558552240893489006005 52739864272583764594313)
                ·
                  rfl

theorem cell19_173324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_173324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173324 prefixEnd_173324 := by exact prefixLift 173324
  have htrace : WordTrace (prefixWord ++ tailWord_173324) baseStart_173324 baseEnd_173324 := by
    simpa [prefixWord, tailWord_173324, baseEnd_173324] using wordTrace_append hprefix tailTrace_173324
  have hstable : (prefixWord ++ tailWord_173324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173324).length < 2 ^ (prefixWord ++ tailWord_173324).sum := by decide
  have hdescent : baseEnd_173324 < baseStart_173324 := by decide
  rcases family_descends (prefixWord ++ tailWord_173324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173341 : List Nat := [1, 4, 2, 3, 1, 3, 5]
def baseStart_173341 : Nat := 118140960795 + 173341 * 2 ^ 59
def prefixEnd_173341 : Nat := 4983230072969 + 3 ^ 40 * 173341 * 2
def baseEnd_173341 : Nat := 17581679038244254072163

theorem tailTrace_173341 : CollatzResearch.WordTrace tailWord_173341 prefixEnd_173341 17581679038244254072163 := by
  unfold tailWord_173341
  simp only [CollatzResearch.WordTrace]
  refine ⟨6322265665022636130991877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4214843776681757420661251 6322265665022636130991877)
  ·
    refine ⟨1185424812191744274560977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6322265665022636130991877 1185424812191744274560977)
    ·
      refine ⟨889068609143808205920733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1185424812191744274560977 889068609143808205920733)
      ·
        refine ⟨333400728428928077220275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 889068609143808205920733 333400728428928077220275)
        ·
          refine ⟨500101092643392115830413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333400728428928077220275 500101092643392115830413)
          ·
            refine ⟨187537909741272043436405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500101092643392115830413 187537909741272043436405)
            ·
              refine ⟨17581679038244254072163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187537909741272043436405 17581679038244254072163)
              ·
                rfl

theorem cell19_173341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_173341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173341 prefixEnd_173341 := by exact prefixLift 173341
  have htrace : WordTrace (prefixWord ++ tailWord_173341) baseStart_173341 baseEnd_173341 := by
    simpa [prefixWord, tailWord_173341, baseEnd_173341] using wordTrace_append hprefix tailTrace_173341
  have hstable : (prefixWord ++ tailWord_173341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173341).length < 2 ^ (prefixWord ++ tailWord_173341).sum := by decide
  have hdescent : baseEnd_173341 < baseStart_173341 := by decide
  rcases family_descends (prefixWord ++ tailWord_173341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173362 : List Nat := [3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_173362 : Nat := 118140960795 + 173362 * 2 ^ 59
def prefixEnd_173362 : Nat := 4983230072969 + 3 ^ 40 * 173362 * 2
def baseEnd_173362 : Nat := 52751427096210935749765

theorem tailTrace_173362 : CollatzResearch.WordTrace tailWord_173362 prefixEnd_173362 52751427096210935749765 := by
  unfold tailWord_173362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580757899486639179376585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4215354398631037811670893 1580757899486639179376585)
  ·
    refine ⟨1185568424614979384532439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1580757899486639179376585 1185568424614979384532439)
    ·
      refine ⟨1778352636922469076798659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1185568424614979384532439 1778352636922469076798659)
      ·
        refine ⟨2667528955383703615197989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778352636922469076798659 2667528955383703615197989)
        ·
          refine ⟨500161679134444427849623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2667528955383703615197989 500161679134444427849623)
          ·
            refine ⟨750242518701666641774435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500161679134444427849623 750242518701666641774435)
            ·
              refine ⟨1125363778052499962661653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750242518701666641774435 1125363778052499962661653)
              ·
                refine ⟨52751427096210935749765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1125363778052499962661653 52751427096210935749765)
                ·
                  rfl

theorem cell19_173362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_173362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173362 prefixEnd_173362 := by exact prefixLift 173362
  have htrace : WordTrace (prefixWord ++ tailWord_173362) baseStart_173362 baseEnd_173362 := by
    simpa [prefixWord, tailWord_173362, baseEnd_173362] using wordTrace_append hprefix tailTrace_173362
  have hstable : (prefixWord ++ tailWord_173362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173362).length < 2 ^ (prefixWord ++ tailWord_173362).sum := by decide
  have hdescent : baseEnd_173362 < baseStart_173362 := by decide
  rcases family_descends (prefixWord ++ tailWord_173362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173415 : List Nat := [1, 1, 5, 1, 5, 1, 1, 4]
def baseStart_173415 : Nat := 118140960795 + 173415 * 2 ^ 59
def prefixEnd_173415 : Nat := 4983230072969 + 3 ^ 40 * 173415 * 2
def baseEnd_173415 : Nat := 52767554192322516571843

theorem tailTrace_173415 : CollatzResearch.WordTrace tailWord_173415 prefixEnd_173415 52767554192322516571843 := by
  unfold tailWord_173415
  simp only [CollatzResearch.WordTrace]
  refine ⟨6324964666754546769185699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4216643111169697846123799 6324964666754546769185699)
  ·
    refine ⟨9487447000131820153778549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6324964666754546769185699 9487447000131820153778549)
    ·
      refine ⟨889448156262358139416739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9487447000131820153778549 889448156262358139416739)
      ·
        refine ⟨1334172234393537209125109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889448156262358139416739 1334172234393537209125109)
        ·
          refine ⟨125078646974394113355479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1334172234393537209125109 125078646974394113355479)
          ·
            refine ⟨187617970461591170033219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125078646974394113355479 187617970461591170033219)
            ·
              refine ⟨281426955692386755049829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187617970461591170033219 281426955692386755049829)
              ·
                refine ⟨52767554192322516571843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281426955692386755049829 52767554192322516571843)
                ·
                  rfl

theorem cell19_173415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_173415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173415 prefixEnd_173415 := by exact prefixLift 173415
  have htrace : WordTrace (prefixWord ++ tailWord_173415) baseStart_173415 baseEnd_173415 := by
    simpa [prefixWord, tailWord_173415, baseEnd_173415] using wordTrace_append hprefix tailTrace_173415
  have hstable : (prefixWord ++ tailWord_173415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173415).length < 2 ^ (prefixWord ++ tailWord_173415).sum := by decide
  have hdescent : baseEnd_173415 < baseStart_173415 := by decide
  rcases family_descends (prefixWord ++ tailWord_173415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173440 : List Nat := [2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_173440 : Nat := 118140960795 + 173440 * 2 ^ 59
def prefixEnd_173440 : Nat := 4983230072969 + 3 ^ 40 * 173440 * 2
def baseEnd_173440 : Nat := 52775161313129866016219

theorem tailTrace_173440 : CollatzResearch.WordTrace tailWord_173440 prefixEnd_173440 52775161313129866016219 := by
  unfold tailWord_173440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162938245831988019422887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4217250994442650692563849 3162938245831988019422887)
  ·
    refine ⟨4744407368747982029134331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162938245831988019422887 4744407368747982029134331)
    ·
      refine ⟨7116611053121973043701497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4744407368747982029134331 7116611053121973043701497)
      ·
        refine ⟨5337458289841479782776123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7116611053121973043701497 5337458289841479782776123)
        ·
          refine ⟨8006187434762219674164185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337458289841479782776123 8006187434762219674164185)
          ·
            refine ⟨6004640576071664755623139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8006187434762219674164185 6004640576071664755623139)
            ·
              refine ⟨9006960864107497133434709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004640576071664755623139 9006960864107497133434709)
              ·
                refine ⟨52775161313129866016219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9006960864107497133434709 52775161313129866016219)
                ·
                  rfl

theorem cell19_173440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_173440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173440 prefixEnd_173440 := by exact prefixLift 173440
  have htrace : WordTrace (prefixWord ++ tailWord_173440) baseStart_173440 baseEnd_173440 := by
    simpa [prefixWord, tailWord_173440, baseEnd_173440] using wordTrace_append hprefix tailTrace_173440
  have hstable : (prefixWord ++ tailWord_173440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173440).length < 2 ^ (prefixWord ++ tailWord_173440).sum := by decide
  have hdescent : baseEnd_173440 < baseStart_173440 := by decide
  rcases family_descends (prefixWord ++ tailWord_173440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173493 : List Nat := [1, 3, 3, 2, 2, 1, 4, 3]
def baseStart_173493 : Nat := 118140960795 + 173493 * 2 ^ 59
def prefixEnd_173493 : Nat := 4983230072969 + 3 ^ 40 * 173493 * 2
def baseEnd_173493 : Nat := 52791288409241446838297

theorem tailTrace_173493 : CollatzResearch.WordTrace tailWord_173493 prefixEnd_173493 52791288409241446838297 := by
  unfold tailWord_173493
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327809560471966090525133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4218539706981310727016755 6327809560471966090525133)
  ·
    refine ⟨2372928585176987283946925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6327809560471966090525133 2372928585176987283946925)
    ·
      refine ⟨889848219441370231480097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2372928585176987283946925 889848219441370231480097)
      ·
        refine ⟨667386164581027673610073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889848219441370231480097 667386164581027673610073)
        ·
          refine ⟨500539623435770755207555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667386164581027673610073 500539623435770755207555)
          ·
            refine ⟨750809435153656132811333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500539623435770755207555 750809435153656132811333)
            ·
              refine ⟨140776769091310524902125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 750809435153656132811333 140776769091310524902125)
              ·
                refine ⟨52791288409241446838297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140776769091310524902125 52791288409241446838297)
                ·
                  rfl

theorem cell19_173493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_173493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173493 prefixEnd_173493 := by exact prefixLift 173493
  have htrace : WordTrace (prefixWord ++ tailWord_173493) baseStart_173493 baseEnd_173493 := by
    simpa [prefixWord, tailWord_173493, baseEnd_173493] using wordTrace_append hprefix tailTrace_173493
  have hstable : (prefixWord ++ tailWord_173493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173493).length < 2 ^ (prefixWord ++ tailWord_173493).sum := by decide
  have hdescent : baseEnd_173493 < baseStart_173493 := by decide
  rcases family_descends (prefixWord ++ tailWord_173493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173506 : List Nat := [3, 5, 2, 1, 1, 2, 5]
def baseStart_173506 : Nat := 118140960795 + 173506 * 2 ^ 59
def prefixEnd_173506 : Nat := 4983230072969 + 3 ^ 40 * 173506 * 2
def baseEnd_173506 : Nat := 17598414704020422849791

theorem tailTrace_173506 : CollatzResearch.WordTrace tailWord_173506 prefixEnd_173506 17598414704020422849791 := by
  unfold tailWord_173506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582070927356217327687093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4218855806283246207165581 1582070927356217327687093)
  ·
    refine ⟨148319149439645374470665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1582070927356217327687093 148319149439645374470665)
    ·
      refine ⟨111239362079734030852999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148319149439645374470665 111239362079734030852999)
      ·
        refine ⟨166859043119601046279499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111239362079734030852999 166859043119601046279499)
        ·
          refine ⟨250288564679401569419249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166859043119601046279499 250288564679401569419249)
          ·
            refine ⟨187716423509551177064437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250288564679401569419249 187716423509551177064437)
            ·
              refine ⟨17598414704020422849791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187716423509551177064437 17598414704020422849791)
              ·
                rfl

theorem cell19_173506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_173506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173506 prefixEnd_173506 := by exact prefixLift 173506
  have htrace : WordTrace (prefixWord ++ tailWord_173506) baseStart_173506 baseEnd_173506 := by
    simpa [prefixWord, tailWord_173506, baseEnd_173506] using wordTrace_append hprefix tailTrace_173506
  have hstable : (prefixWord ++ tailWord_173506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173506).length < 2 ^ (prefixWord ++ tailWord_173506).sum := by decide
  have hdescent : baseEnd_173506 < baseStart_173506 := by decide
  rcases family_descends (prefixWord ++ tailWord_173506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173514 : List Nat := [3, 1, 2, 1, 2, 5, 5]
def baseStart_173514 : Nat := 118140960795 + 173514 * 2 ^ 59
def prefixEnd_173514 : Nat := 4983230072969 + 3 ^ 40 * 173514 * 2
def baseEnd_173514 : Nat := 17599226130239873457191

theorem tailTrace_173514 : CollatzResearch.WordTrace tailWord_173514 prefixEnd_173514 17599226130239873457191 := by
  unfold tailWord_173514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582143873348971669259899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4219050328930591118026397 1582143873348971669259899)
  ·
    refine ⟨2373215810023457503889849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582143873348971669259899 2373215810023457503889849)
    ·
      refine ⟨1779911857517593127917387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2373215810023457503889849 1779911857517593127917387)
      ·
        refine ⟨2669867786276389691876081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779911857517593127917387 2669867786276389691876081)
        ·
          refine ⟨2002400839707292268907061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669867786276389691876081 2002400839707292268907061)
          ·
            refine ⟨187725078722558650210037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2002400839707292268907061 187725078722558650210037)
            ·
              refine ⟨17599226130239873457191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187725078722558650210037 17599226130239873457191)
              ·
                rfl

theorem cell19_173514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_173514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173514 prefixEnd_173514 := by exact prefixLift 173514
  have htrace : WordTrace (prefixWord ++ tailWord_173514) baseStart_173514 baseEnd_173514 := by
    simpa [prefixWord, tailWord_173514, baseEnd_173514] using wordTrace_append hprefix tailTrace_173514
  have hstable : (prefixWord ++ tailWord_173514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173514).length < 2 ^ (prefixWord ++ tailWord_173514).sum := by decide
  have hdescent : baseEnd_173514 < baseStart_173514 := by decide
  rcases family_descends (prefixWord ++ tailWord_173514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173533 : List Nat := [1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_173533 : Nat := 118140960795 + 173533 * 2 ^ 59
def prefixEnd_173533 : Nat := 4983230072969 + 3 ^ 40 * 173533 * 2
def baseEnd_173533 : Nat := 52803459802533205949299

theorem tailTrace_173533 : CollatzResearch.WordTrace tailWord_173533 prefixEnd_173533 52803459802533205949299 := by
  unfold tailWord_173533
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329268480327052921981253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4219512320218035281320835 6329268480327052921981253)
  ·
    refine ⟨1186737840061322422871485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6329268480327052921981253 1186737840061322422871485)
    ·
      refine ⟨445026690022995908576807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1186737840061322422871485 445026690022995908576807)
      ·
        refine ⟨667540035034493862865211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445026690022995908576807 667540035034493862865211)
        ·
          refine ⟨1001310052551740794297817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667540035034493862865211 1001310052551740794297817)
          ·
            refine ⟨750982539413805595723363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001310052551740794297817 750982539413805595723363)
            ·
              refine ⟨1126473809120708393585045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750982539413805595723363 1126473809120708393585045)
              ·
                refine ⟨52803459802533205949299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1126473809120708393585045 52803459802533205949299)
                ·
                  rfl

theorem cell19_173533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_173533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173533 prefixEnd_173533 := by exact prefixLift 173533
  have htrace : WordTrace (prefixWord ++ tailWord_173533) baseStart_173533 baseEnd_173533 := by
    simpa [prefixWord, tailWord_173533, baseEnd_173533] using wordTrace_append hprefix tailTrace_173533
  have hstable : (prefixWord ++ tailWord_173533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173533).length < 2 ^ (prefixWord ++ tailWord_173533).sum := by decide
  have hdescent : baseEnd_173533 < baseStart_173533 := by decide
  rcases family_descends (prefixWord ++ tailWord_173533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173628 : List Nat := [2, 2, 2, 2, 4, 1, 6]
def baseStart_173628 : Nat := 118140960795 + 173628 * 2 ^ 59
def prefixEnd_173628 : Nat := 4983230072969 + 3 ^ 40 * 173628 * 2
def baseEnd_173628 : Nat := 17610788953867044612643

theorem tailTrace_173628 : CollatzResearch.WordTrace tailWord_173628 prefixEnd_173628 17610788953867044612643 := by
  unfold tailWord_173628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3166366707491442073344769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4221822276655256097793025 3166366707491442073344769)
  ·
    refine ⟨2374775030618581555008577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3166366707491442073344769 2374775030618581555008577)
    ·
      refine ⟨1781081272963936166256433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2374775030618581555008577 1781081272963936166256433)
      ·
        refine ⟨1335810954722952124692325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781081272963936166256433 1335810954722952124692325)
        ·
          refine ⟨250464554010553523379811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1335810954722952124692325 250464554010553523379811)
          ·
            refine ⟨375696831015830285069717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250464554010553523379811 375696831015830285069717)
            ·
              refine ⟨17610788953867044612643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 375696831015830285069717 17610788953867044612643)
              ·
                rfl

theorem cell19_173628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_173628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173628 prefixEnd_173628 := by exact prefixLift 173628
  have htrace : WordTrace (prefixWord ++ tailWord_173628) baseStart_173628 baseEnd_173628 := by
    simpa [prefixWord, tailWord_173628, baseEnd_173628] using wordTrace_append hprefix tailTrace_173628
  have hstable : (prefixWord ++ tailWord_173628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173628).length < 2 ^ (prefixWord ++ tailWord_173628).sum := by decide
  have hdescent : baseEnd_173628 < baseStart_173628 := by decide
  rcases family_descends (prefixWord ++ tailWord_173628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173649 : List Nat := [1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_173649 : Nat := 118140960795 + 173649 * 2 ^ 59
def prefixEnd_173649 : Nat := 4983230072969 + 3 ^ 40 * 173649 * 2
def baseEnd_173649 : Nat := 52838756843079307371205

theorem tailTrace_173649 : CollatzResearch.WordTrace tailWord_173649 prefixEnd_173649 52838756843079307371205 := by
  unfold tailWord_173649
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333499347906804733204001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4222332898604536488802667 6333499347906804733204001)
  ·
    refine ⟨4750124510930103549903001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6333499347906804733204001 4750124510930103549903001)
    ·
      refine ⟨3562593383197577662427251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4750124510930103549903001 3562593383197577662427251)
      ·
        refine ⟨5343890074796366493640877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562593383197577662427251 5343890074796366493640877)
        ·
          refine ⟨2003958778048637435115329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5343890074796366493640877 2003958778048637435115329)
          ·
            refine ⟨1502969083536478076336497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003958778048637435115329 1502969083536478076336497)
            ·
              refine ⟨1127226812652358557252373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502969083536478076336497 1127226812652358557252373)
              ·
                refine ⟨52838756843079307371205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1127226812652358557252373 52838756843079307371205)
                ·
                  rfl

theorem cell19_173649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_173649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173649 prefixEnd_173649 := by exact prefixLift 173649
  have htrace : WordTrace (prefixWord ++ tailWord_173649) baseStart_173649 baseEnd_173649 := by
    simpa [prefixWord, tailWord_173649, baseEnd_173649] using wordTrace_append hprefix tailTrace_173649
  have hstable : (prefixWord ++ tailWord_173649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173649).length < 2 ^ (prefixWord ++ tailWord_173649).sum := by decide
  have hdescent : baseEnd_173649 < baseStart_173649 := by decide
  rcases family_descends (prefixWord ++ tailWord_173649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173685 : List Nat := [1, 3, 4, 2, 1, 1, 7]
def baseStart_173685 : Nat := 118140960795 + 173685 * 2 ^ 59
def prefixEnd_173685 : Nat := 4983230072969 + 3 ^ 40 * 173685 * 2
def baseEnd_173685 : Nat := 17616570365680630190369

theorem tailTrace_173685 : CollatzResearch.WordTrace tailWord_173685 prefixEnd_173685 17616570365680630190369 := by
  unfold tailWord_173685
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334812375776382881514509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4223208250517588587676339 6334812375776382881514509)
  ·
    refine ⟨2375554640916143580567941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6334812375776382881514509 2375554640916143580567941)
    ·
      refine ⟨445416495171776921356489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2375554640916143580567941 445416495171776921356489)
      ·
        refine ⟨334062371378832691017367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445416495171776921356489 334062371378832691017367)
        ·
          refine ⟨501093557068249036526051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334062371378832691017367 501093557068249036526051)
          ·
            refine ⟨751640335602373554789077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501093557068249036526051 751640335602373554789077)
            ·
              refine ⟨17616570365680630190369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 751640335602373554789077 17616570365680630190369)
              ·
                rfl

theorem cell19_173685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_173685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173685 prefixEnd_173685 := by exact prefixLift 173685
  have htrace : WordTrace (prefixWord ++ tailWord_173685) baseStart_173685 baseEnd_173685 := by
    simpa [prefixWord, tailWord_173685, baseEnd_173685] using wordTrace_append hprefix tailTrace_173685
  have hstable : (prefixWord ++ tailWord_173685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173685).length < 2 ^ (prefixWord ++ tailWord_173685).sum := by decide
  have hdescent : baseEnd_173685 < baseStart_173685 := by decide
  rcases family_descends (prefixWord ++ tailWord_173685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173742 : List Nat := [4, 1, 4, 1, 9]
def baseStart_173742 : Nat := 118140960795 + 173742 * 2 ^ 59
def prefixEnd_173742 : Nat := 4983230072969 + 3 ^ 40 * 173742 * 2
def baseEnd_173742 : Nat := 1958039086388246196455

theorem tailTrace_173742 : CollatzResearch.WordTrace tailWord_173742 prefixEnd_173742 1958039086388246196455 := by
  unfold tailWord_173742
  simp only [CollatzResearch.WordTrace]
  refine ⟨792111417071235202042435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4224594224379921077559653 792111417071235202042435)
  ·
    refine ⟨1188167125606852803063653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 792111417071235202042435 1188167125606852803063653)
    ·
      refine ⟨222781336051284900574435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1188167125606852803063653 222781336051284900574435)
      ·
        refine ⟨334172004076927350861653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222781336051284900574435 334172004076927350861653)
        ·
          refine ⟨1958039086388246196455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 334172004076927350861653 1958039086388246196455)
          ·
            rfl

theorem cell19_173742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 9].length) (baseStart_173742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173742 prefixEnd_173742 := by exact prefixLift 173742
  have htrace : WordTrace (prefixWord ++ tailWord_173742) baseStart_173742 baseEnd_173742 := by
    simpa [prefixWord, tailWord_173742, baseEnd_173742] using wordTrace_append hprefix tailTrace_173742
  have hstable : (prefixWord ++ tailWord_173742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173742).length < 2 ^ (prefixWord ++ tailWord_173742).sum := by decide
  have hdescent : baseEnd_173742 < baseStart_173742 := by decide
  rcases family_descends (prefixWord ++ tailWord_173742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173778 : List Nat := [3, 2, 2, 2, 2, 2, 3, 3]
def baseStart_173778 : Nat := 118140960795 + 173778 * 2 ^ 59
def prefixEnd_173778 : Nat := 4983230072969 + 3 ^ 40 * 173778 * 2
def baseEnd_173778 : Nat := 52878009586445230504187

theorem tailTrace_173778 : CollatzResearch.WordTrace tailWord_173778 prefixEnd_173778 52878009586445230504187 := by
  unfold tailWord_173778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584551091109864941162497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4225469576292973176433325 1584551091109864941162497)
  ·
    refine ⟨1188413318332398705871873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1584551091109864941162497 1188413318332398705871873)
    ·
      refine ⟨891309988749299029403905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1188413318332398705871873 891309988749299029403905)
      ·
        refine ⟨668482491561974272052929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 891309988749299029403905 668482491561974272052929)
        ·
          refine ⟨501361868671480704039697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668482491561974272052929 501361868671480704039697)
          ·
            refine ⟨376021401503610528029773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501361868671480704039697 376021401503610528029773)
            ·
              refine ⟨141008025563853948011165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376021401503610528029773 141008025563853948011165)
              ·
                refine ⟨52878009586445230504187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141008025563853948011165 52878009586445230504187)
                ·
                  rfl

theorem cell19_173778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_173778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173778 prefixEnd_173778 := by exact prefixLift 173778
  have htrace : WordTrace (prefixWord ++ tailWord_173778) baseStart_173778 baseEnd_173778 := by
    simpa [prefixWord, tailWord_173778, baseEnd_173778] using wordTrace_append hprefix tailTrace_173778
  have hstable : (prefixWord ++ tailWord_173778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173778).length < 2 ^ (prefixWord ++ tailWord_173778).sum := by decide
  have hdescent : baseEnd_173778 < baseStart_173778 := by decide
  rcases family_descends (prefixWord ++ tailWord_173778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173820 : List Nat := [2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_173820 : Nat := 118140960795 + 173820 * 2 ^ 59
def prefixEnd_173820 : Nat := 4983230072969 + 3 ^ 40 * 173820 * 2
def baseEnd_173820 : Nat := 52890789549401577570739

theorem tailTrace_173820 : CollatzResearch.WordTrace tailWord_173820 prefixEnd_173820 52890789549401577570739 := by
  unfold tailWord_173820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169868115143650468839457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4226490820191533958452609 3169868115143650468839457)
  ·
    refine ⟨2377401086357737851629593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3169868115143650468839457 2377401086357737851629593)
    ·
      refine ⟨1783050814768303388722195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2377401086357737851629593 1783050814768303388722195)
      ·
        refine ⟨2674576222152455083083293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783050814768303388722195 2674576222152455083083293)
        ·
          refine ⟨1002966083307170656156235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2674576222152455083083293 1002966083307170656156235)
          ·
            refine ⟨1504449124960755984234353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002966083307170656156235 1504449124960755984234353)
            ·
              refine ⟨1128336843720566988175765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504449124960755984234353 1128336843720566988175765)
              ·
                refine ⟨52890789549401577570739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1128336843720566988175765 52890789549401577570739)
                ·
                  rfl

theorem cell19_173820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_173820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173820 prefixEnd_173820 := by exact prefixLift 173820
  have htrace : WordTrace (prefixWord ++ tailWord_173820) baseStart_173820 baseEnd_173820 := by
    simpa [prefixWord, tailWord_173820, baseEnd_173820] using wordTrace_append hprefix tailTrace_173820
  have hstable : (prefixWord ++ tailWord_173820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173820).length < 2 ^ (prefixWord ++ tailWord_173820).sum := by decide
  have hdescent : baseEnd_173820 < baseStart_173820 := by decide
  rcases family_descends (prefixWord ++ tailWord_173820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173875 : List Nat := [1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_173875 : Nat := 118140960795 + 173875 * 2 ^ 59
def prefixEnd_173875 : Nat := 4983230072969 + 3 ^ 40 * 173875 * 2
def baseEnd_173875 : Nat := 52907525215177746348367

theorem tailTrace_173875 : CollatzResearch.WordTrace tailWord_173875 prefixEnd_173875 52907525215177746348367 := by
  unfold tailWord_173875
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341742245088045330931079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4227828163392030220620719 6341742245088045330931079)
  ·
    refine ⟨9512613367632067996396619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6341742245088045330931079 9512613367632067996396619)
    ·
      refine ⟨14268920051448101994594929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9512613367632067996396619 14268920051448101994594929)
      ·
        refine ⟨10701690038586076495946197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14268920051448101994594929 10701690038586076495946197)
        ·
          refine ⟨250820860279361167873739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10701690038586076495946197 250820860279361167873739)
          ·
            refine ⟨376231290419041751810609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250820860279361167873739 376231290419041751810609)
            ·
              refine ⟨282173467814281313857957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376231290419041751810609 282173467814281313857957)
              ·
                refine ⟨52907525215177746348367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282173467814281313857957 52907525215177746348367)
                ·
                  rfl

theorem cell19_173875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_173875 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173875 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173875 prefixEnd_173875 := by exact prefixLift 173875
  have htrace : WordTrace (prefixWord ++ tailWord_173875) baseStart_173875 baseEnd_173875 := by
    simpa [prefixWord, tailWord_173875, baseEnd_173875] using wordTrace_append hprefix tailTrace_173875
  have hstable : (prefixWord ++ tailWord_173875).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173875).length < 2 ^ (prefixWord ++ tailWord_173875).sum := by decide
  have hdescent : baseEnd_173875 < baseStart_173875 := by decide
  rcases family_descends (prefixWord ++ tailWord_173875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173896 : List Nat := [2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_173896 : Nat := 118140960795 + 173896 * 2 ^ 59
def prefixEnd_173896 : Nat := 4983230072969 + 3 ^ 40 * 173896 * 2
def baseEnd_173896 : Nat := 52913915196655919881643

theorem tailTrace_173896 : CollatzResearch.WordTrace tailWord_173896 prefixEnd_173896 52913915196655919881643 := by
  unfold tailWord_173896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3171254089005982958722771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4228338785341310611630361 3171254089005982958722771)
  ·
    refine ⟨4756881133508974438084157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3171254089005982958722771 4756881133508974438084157)
    ·
      refine ⟨1783830425065865414281559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4756881133508974438084157 1783830425065865414281559)
      ·
        refine ⟨2675745637598798121422339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783830425065865414281559 2675745637598798121422339)
        ·
          refine ⟨4013618456398197182133509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675745637598798121422339 4013618456398197182133509)
          ·
            refine ⟨752553460574661971650033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4013618456398197182133509 752553460574661971650033)
            ·
              refine ⟨564415095430996478737525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752553460574661971650033 564415095430996478737525)
              ·
                refine ⟨52913915196655919881643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 564415095430996478737525 52913915196655919881643)
                ·
                  rfl

theorem cell19_173896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_173896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173896 prefixEnd_173896 := by exact prefixLift 173896
  have htrace : WordTrace (prefixWord ++ tailWord_173896) baseStart_173896 baseEnd_173896 := by
    simpa [prefixWord, tailWord_173896, baseEnd_173896] using wordTrace_append hprefix tailTrace_173896
  have hstable : (prefixWord ++ tailWord_173896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173896).length < 2 ^ (prefixWord ++ tailWord_173896).sum := by decide
  have hdescent : baseEnd_173896 < baseStart_173896 := by decide
  rcases family_descends (prefixWord ++ tailWord_173896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173932 : List Nat := [2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_173932 : Nat := 118140960795 + 173932 * 2 ^ 59
def prefixEnd_173932 : Nat := 4983230072969 + 3 ^ 40 * 173932 * 2
def baseEnd_173932 : Nat := 52924869450618503081545

theorem tailTrace_173932 : CollatzResearch.WordTrace tailWord_173932 prefixEnd_173932 52924869450618503081545 := by
  unfold tailWord_173932
  simp only [CollatzResearch.WordTrace]
  refine ⟨3171910602940772032878025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4229214137254362710504033 3171910602940772032878025)
  ·
    refine ⟨2378932952205579024658519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3171910602940772032878025 2378932952205579024658519)
    ·
      refine ⟨3568399428308368536987779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2378932952205579024658519 3568399428308368536987779)
      ·
        refine ⟨5352599142462552805481669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3568399428308368536987779 5352599142462552805481669)
        ·
          refine ⟨1003612339211728651027813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5352599142462552805481669 1003612339211728651027813)
          ·
            refine ⟨188177313602199122067715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1003612339211728651027813 188177313602199122067715)
            ·
              refine ⟨282265970403298683101573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188177313602199122067715 282265970403298683101573)
              ·
                refine ⟨52924869450618503081545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282265970403298683101573 52924869450618503081545)
                ·
                  rfl

theorem cell19_173932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_173932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173932 prefixEnd_173932 := by exact prefixLift 173932
  have htrace : WordTrace (prefixWord ++ tailWord_173932) baseStart_173932 baseEnd_173932 := by
    simpa [prefixWord, tailWord_173932, baseEnd_173932] using wordTrace_append hprefix tailTrace_173932
  have hstable : (prefixWord ++ tailWord_173932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173932).length < 2 ^ (prefixWord ++ tailWord_173932).sum := by decide
  have hdescent : baseEnd_173932 < baseStart_173932 := by decide
  rcases family_descends (prefixWord ++ tailWord_173932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173970 : List Nat := [3, 2, 3, 2, 1, 2, 6]
def baseStart_173970 : Nat := 118140960795 + 173970 * 2 ^ 59
def prefixEnd_173970 : Nat := 4983230072969 + 3 ^ 40 * 173970 * 2
def baseEnd_173970 : Nat := 17645477424748558078999

theorem tailTrace_173970 : CollatzResearch.WordTrace tailWord_173970 prefixEnd_173970 17645477424748558078999 := by
  unfold tailWord_173970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586301794935969138909841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4230138119829251037092909 1586301794935969138909841)
  ·
    refine ⟨1189726346201976854182381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1586301794935969138909841 1189726346201976854182381)
    ·
      refine ⟨446147379825741320318393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1189726346201976854182381 446147379825741320318393)
      ·
        refine ⟨334610534869305990238795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446147379825741320318393 334610534869305990238795)
        ·
          refine ⟨501915802303958985358193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334610534869305990238795 501915802303958985358193)
          ·
            refine ⟨376436851727969239018645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501915802303958985358193 376436851727969239018645)
            ·
              refine ⟨17645477424748558078999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 376436851727969239018645 17645477424748558078999)
              ·
                rfl

theorem cell19_173970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_173970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_173970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_173970 prefixEnd_173970 := by exact prefixLift 173970
  have htrace : WordTrace (prefixWord ++ tailWord_173970) baseStart_173970 baseEnd_173970 := by
    simpa [prefixWord, tailWord_173970, baseEnd_173970] using wordTrace_append hprefix tailTrace_173970
  have hstable : (prefixWord ++ tailWord_173970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173970).length < 2 ^ (prefixWord ++ tailWord_173970).sum := by decide
  have hdescent : baseEnd_173970 < baseStart_173970 := by decide
  rcases family_descends (prefixWord ++ tailWord_173970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174084 : List Nat := [2, 3, 2, 4, 1, 7]
def baseStart_174084 : Nat := 118140960795 + 174084 * 2 ^ 59
def prefixEnd_174084 : Nat := 4983230072969 + 3 ^ 40 * 174084 * 2
def baseEnd_174084 : Nat := 5885680082791909744817

theorem tailTrace_174084 : CollatzResearch.WordTrace tailWord_174084 prefixEnd_174084 5885680082791909744817 := by
  unfold tailWord_174084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3174682550665437012644653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4232910067553916016859537 3174682550665437012644653)
  ·
    refine ⟨1190505956499538879741745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3174682550665437012644653 1190505956499538879741745)
    ·
      refine ⟨892879467374654159806309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190505956499538879741745 892879467374654159806309)
      ·
        refine ⟨167414900132747654963683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 892879467374654159806309 167414900132747654963683)
        ·
          refine ⟨251122350199121482445525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167414900132747654963683 251122350199121482445525)
          ·
            refine ⟨5885680082791909744817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 251122350199121482445525 5885680082791909744817)
            ·
              rfl

theorem cell19_174084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 7].length) (baseStart_174084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174084 prefixEnd_174084 := by exact prefixLift 174084
  have htrace : WordTrace (prefixWord ++ tailWord_174084) baseStart_174084 baseEnd_174084 := by
    simpa [prefixWord, tailWord_174084, baseEnd_174084] using wordTrace_append hprefix tailTrace_174084
  have hstable : (prefixWord ++ tailWord_174084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174084).length < 2 ^ (prefixWord ++ tailWord_174084).sum := by decide
  have hdescent : baseEnd_174084 < baseStart_174084 := by decide
  rcases family_descends (prefixWord ++ tailWord_174084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174101 : List Nat := [1, 3, 2, 1, 6, 1, 1, 4]
def baseStart_174101 : Nat := 118140960795 + 174101 * 2 ^ 59
def prefixEnd_174101 : Nat := 4983230072969 + 3 ^ 40 * 174101 * 2
def baseEnd_174101 : Nat := 52976293587276185325529

theorem tailTrace_174101 : CollatzResearch.WordTrace tailWord_174101 prefixEnd_174101 52976293587276185325529 := by
  unfold tailWord_174101
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349985142269285928658157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4233323428179523952438771 6349985142269285928658157)
  ·
    refine ⟨2381244428350982223246809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6349985142269285928658157 2381244428350982223246809)
    ·
      refine ⟨1785933321263236667435107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2381244428350982223246809 1785933321263236667435107)
      ·
        refine ⟨2678899981894855001152661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785933321263236667435107 2678899981894855001152661)
        ·
          refine ⟨125573436651321328179031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2678899981894855001152661 125573436651321328179031)
          ·
            refine ⟨188360154976981992268547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125573436651321328179031 188360154976981992268547)
            ·
              refine ⟨282540232465472988402821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188360154976981992268547 282540232465472988402821)
              ·
                refine ⟨52976293587276185325529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282540232465472988402821 52976293587276185325529)
                ·
                  rfl

theorem cell19_174101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_174101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174101 prefixEnd_174101 := by exact prefixLift 174101
  have htrace : WordTrace (prefixWord ++ tailWord_174101) baseStart_174101 baseEnd_174101 := by
    simpa [prefixWord, tailWord_174101, baseEnd_174101] using wordTrace_append hprefix tailTrace_174101
  have hstable : (prefixWord ++ tailWord_174101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174101).length < 2 ^ (prefixWord ++ tailWord_174101).sum := by decide
  have hdescent : baseEnd_174101 < baseStart_174101 := by decide
  rcases family_descends (prefixWord ++ tailWord_174101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174107 : List Nat := [1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_174107 : Nat := 118140960795 + 174107 * 2 ^ 59
def prefixEnd_174107 : Nat := 4983230072969 + 3 ^ 40 * 174107 * 2
def baseEnd_174107 : Nat := 52978119296269949192179

theorem tailTrace_174107 : CollatzResearch.WordTrace tailWord_174107 prefixEnd_174107 52978119296269949192179 := by
  unfold tailWord_174107
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350203980247548953376575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4233469320165032635584383 6350203980247548953376575)
  ·
    refine ⟨9525305970371323430064863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6350203980247548953376575 9525305970371323430064863)
    ·
      refine ⟨14287958955556985145097295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9525305970371323430064863 14287958955556985145097295)
      ·
        refine ⟨21431938433335477717645943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14287958955556985145097295 21431938433335477717645943)
        ·
          refine ⟨32147907650003216576468915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21431938433335477717645943 32147907650003216576468915)
          ·
            refine ⟨48221861475004824864703373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32147907650003216576468915 48221861475004824864703373)
            ·
              refine ⟨18083198053126809324263765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48221861475004824864703373 18083198053126809324263765)
              ·
                refine ⟨52978119296269949192179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18083198053126809324263765 52978119296269949192179)
                ·
                  rfl

theorem cell19_174107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_174107 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174107 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174107 prefixEnd_174107 := by exact prefixLift 174107
  have htrace : WordTrace (prefixWord ++ tailWord_174107) baseStart_174107 baseEnd_174107 := by
    simpa [prefixWord, tailWord_174107, baseEnd_174107] using wordTrace_append hprefix tailTrace_174107
  have hstable : (prefixWord ++ tailWord_174107).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174107).length < 2 ^ (prefixWord ++ tailWord_174107).sum := by decide
  have hdescent : baseEnd_174107 < baseStart_174107 := by decide
  rcases family_descends (prefixWord ++ tailWord_174107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174181 : List Nat := [1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_174181 : Nat := 118140960795 + 174181 * 2 ^ 59
def prefixEnd_174181 : Nat := 4983230072969 + 3 ^ 40 * 174181 * 2
def baseEnd_174181 : Nat := 53000636373859703547533

theorem tailTrace_174181 : CollatzResearch.WordTrace tailWord_174181 prefixEnd_174181 53000636373859703547533 := by
  unfold tailWord_174181
  simp only [CollatzResearch.WordTrace]
  refine ⟨6352902981979459591570397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4235268654652973061046931 6352902981979459591570397)
  ·
    refine ⟨2382338618242297346838899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6352902981979459591570397 2382338618242297346838899)
    ·
      refine ⟨3573507927363446020258349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2382338618242297346838899 3573507927363446020258349)
      ·
        refine ⟨1340065472761292257596881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3573507927363446020258349 1340065472761292257596881)
        ·
          refine ⟨1005049104570969193197661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1340065472761292257596881 1005049104570969193197661)
          ·
            refine ⟨376893414214113447449123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1005049104570969193197661 376893414214113447449123)
            ·
              refine ⟨565340121321170171173685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376893414214113447449123 565340121321170171173685)
              ·
                refine ⟨53000636373859703547533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565340121321170171173685 53000636373859703547533)
                ·
                  rfl

theorem cell19_174181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_174181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174181 prefixEnd_174181 := by exact prefixLift 174181
  have htrace : WordTrace (prefixWord ++ tailWord_174181) baseStart_174181 baseEnd_174181 := by
    simpa [prefixWord, tailWord_174181, baseEnd_174181] using wordTrace_append hprefix tailTrace_174181
  have hstable : (prefixWord ++ tailWord_174181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174181).length < 2 ^ (prefixWord ++ tailWord_174181).sum := by decide
  have hdescent : baseEnd_174181 < baseStart_174181 := by decide
  rcases family_descends (prefixWord ++ tailWord_174181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174198 : List Nat := [5, 1, 1, 2, 1, 4, 5]
def baseStart_174198 : Nat := 118140960795 + 174198 * 2 ^ 59
def prefixEnd_174198 : Nat := 4983230072969 + 3 ^ 40 * 174198 * 2
def baseEnd_174198 : Nat := 17668603072002900389903

theorem tailTrace_174198 : CollatzResearch.WordTrace tailWord_174198 prefixEnd_174198 17668603072002900389903 := by
  unfold tailWord_174198
  simp only [CollatzResearch.WordTrace]
  refine ⟨397095188932366968433703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4235682015278580996626165 397095188932366968433703)
  ·
    refine ⟨595642783398550452650555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397095188932366968433703 595642783398550452650555)
    ·
      refine ⟨893464175097825678975833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595642783398550452650555 893464175097825678975833)
      ·
        refine ⟨670098131323369259231875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893464175097825678975833 670098131323369259231875)
        ·
          refine ⟨1005147196985053888847813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670098131323369259231875 1005147196985053888847813)
          ·
            refine ⟨188465099434697604158965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1005147196985053888847813 188465099434697604158965)
            ·
              refine ⟨17668603072002900389903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188465099434697604158965 17668603072002900389903)
              ·
                rfl

theorem cell19_174198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_174198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174198 prefixEnd_174198 := by exact prefixLift 174198
  have htrace : WordTrace (prefixWord ++ tailWord_174198) baseStart_174198 baseEnd_174198 := by
    simpa [prefixWord, tailWord_174198, baseEnd_174198] using wordTrace_append hprefix tailTrace_174198
  have hstable : (prefixWord ++ tailWord_174198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174198).length < 2 ^ (prefixWord ++ tailWord_174198).sum := by decide
  have hdescent : baseEnd_174198 < baseStart_174198 := by decide
  rcases family_descends (prefixWord ++ tailWord_174198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174257 : List Nat := [1, 2, 2, 5, 2, 7]
def baseStart_174257 : Nat := 118140960795 + 174257 * 2 ^ 59
def prefixEnd_174257 : Nat := 4983230072969 + 3 ^ 40 * 174257 * 2
def baseEnd_174257 : Nat := 5891529113457116206493

theorem tailTrace_174257 : CollatzResearch.WordTrace tailWord_174257 prefixEnd_174257 5891529113457116206493 := by
  unfold tailWord_174257
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355674929704124571337025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4237116619802749714224683 6355674929704124571337025)
  ·
    refine ⟨4766756197278093428502769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6355674929704124571337025 4766756197278093428502769)
    ·
      refine ⟨3575067147958570071377077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4766756197278093428502769 3575067147958570071377077)
      ·
        refine ⟨335162545121115944191601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3575067147958570071377077 335162545121115944191601)
        ·
          refine ⟨251371908840836958143701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335162545121115944191601 251371908840836958143701)
          ·
            refine ⟨5891529113457116206493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 251371908840836958143701 5891529113457116206493)
            ·
              rfl

theorem cell19_174257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_174257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174257 prefixEnd_174257 := by exact prefixLift 174257
  have htrace : WordTrace (prefixWord ++ tailWord_174257) baseStart_174257 baseEnd_174257 := by
    simpa [prefixWord, tailWord_174257, baseEnd_174257] using wordTrace_append hprefix tailTrace_174257
  have hstable : (prefixWord ++ tailWord_174257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174257).length < 2 ^ (prefixWord ++ tailWord_174257).sum := by decide
  have hdescent : baseEnd_174257 < baseStart_174257 := by decide
  rcases family_descends (prefixWord ++ tailWord_174257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174297 : List Nat := [1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_174297 : Nat := 118140960795 + 174297 * 2 ^ 59
def prefixEnd_174297 : Nat := 4983230072969 + 3 ^ 40 * 174297 * 2
def baseEnd_174297 : Nat := 53035933414405804969439

theorem tailTrace_174297 : CollatzResearch.WordTrace tailWord_174297 prefixEnd_174297 53035933414405804969439 := by
  unfold tailWord_174297
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357133849559211402793145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4238089233039474268528763 6357133849559211402793145)
  ·
    refine ⟨4767850387169408552094859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6357133849559211402793145 4767850387169408552094859)
    ·
      refine ⟨7151775580754112828142289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4767850387169408552094859 7151775580754112828142289)
      ·
        refine ⟨5363831685565584621106717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151775580754112828142289 5363831685565584621106717)
        ·
          refine ⟨2011436882087094232915019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5363831685565584621106717 2011436882087094232915019)
          ·
            refine ⟨3017155323130641349372529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011436882087094232915019 3017155323130641349372529)
            ·
              refine ⟨2262866492347981012029397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017155323130641349372529 2262866492347981012029397)
              ·
                refine ⟨53035933414405804969439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2262866492347981012029397 53035933414405804969439)
                ·
                  rfl

theorem cell19_174297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_174297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174297 prefixEnd_174297 := by exact prefixLift 174297
  have htrace : WordTrace (prefixWord ++ tailWord_174297) baseStart_174297 baseEnd_174297 := by
    simpa [prefixWord, tailWord_174297, baseEnd_174297] using wordTrace_append hprefix tailTrace_174297
  have hstable : (prefixWord ++ tailWord_174297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174297).length < 2 ^ (prefixWord ++ tailWord_174297).sum := by decide
  have hdescent : baseEnd_174297 < baseStart_174297 := by decide
  rcases family_descends (prefixWord ++ tailWord_174297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174316 : List Nat := [2, 2, 1, 1, 2, 3, 8]
def baseStart_174316 : Nat := 118140960795 + 174316 * 2 ^ 59
def prefixEnd_174316 : Nat := 4983230072969 + 3 ^ 40 * 174316 * 2
def baseEnd_174316 : Nat := 17680571608739796849055

theorem tailTrace_174316 : CollatzResearch.WordTrace tailWord_174316 prefixEnd_174316 17680571608739796849055 := by
  unfold tailWord_174316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178913418245188823867401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4238551224326918431823201 3178913418245188823867401)
  ·
    refine ⟨2384185063683891617900551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3178913418245188823867401 2384185063683891617900551)
    ·
      refine ⟨3576277595525837426850827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2384185063683891617900551 3576277595525837426850827)
      ·
        refine ⟨5364416393288756140276241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3576277595525837426850827 5364416393288756140276241)
        ·
          refine ⟨4023312294966567105207181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5364416393288756140276241 4023312294966567105207181)
          ·
            refine ⟨1508742110612462664452693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4023312294966567105207181 1508742110612462664452693)
            ·
              refine ⟨17680571608739796849055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1508742110612462664452693 17680571608739796849055)
              ·
                rfl

theorem cell19_174316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_174316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174316 prefixEnd_174316 := by exact prefixLift 174316
  have htrace : WordTrace (prefixWord ++ tailWord_174316) baseStart_174316 baseEnd_174316 := by
    simpa [prefixWord, tailWord_174316, baseEnd_174316] using wordTrace_append hprefix tailTrace_174316
  have hstable : (prefixWord ++ tailWord_174316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174316).length < 2 ^ (prefixWord ++ tailWord_174316).sum := by decide
  have hdescent : baseEnd_174316 < baseStart_174316 := by decide
  rcases family_descends (prefixWord ++ tailWord_174316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174335 : List Nat := [1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_174335 : Nat := 118140960795 + 174335 * 2 ^ 59
def prefixEnd_174335 : Nat := 4983230072969 + 3 ^ 40 * 174335 * 2
def baseEnd_174335 : Nat := 53047496238032976124891

theorem tailTrace_174335 : CollatzResearch.WordTrace tailWord_174335 prefixEnd_174335 53047496238032976124891 := by
  unfold tailWord_174335
  simp only [CollatzResearch.WordTrace]
  refine ⟨6358519823421543892676459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4239013215614362595117639 6358519823421543892676459)
  ·
    refine ⟨9537779735132315839014689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6358519823421543892676459 9537779735132315839014689)
    ·
      refine ⟨7153334801349236879261017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9537779735132315839014689 7153334801349236879261017)
      ·
        refine ⟨5365001101011927659445763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7153334801349236879261017 5365001101011927659445763)
        ·
          refine ⟨8047501651517891489168645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365001101011927659445763 8047501651517891489168645)
          ·
            refine ⟨1508906559659604654219121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8047501651517891489168645 1508906559659604654219121)
            ·
              refine ⟨1131679919744703490664341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508906559659604654219121 1131679919744703490664341)
              ·
                refine ⟨53047496238032976124891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1131679919744703490664341 53047496238032976124891)
                ·
                  rfl

theorem cell19_174335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_174335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174335 prefixEnd_174335 := by exact prefixLift 174335
  have htrace : WordTrace (prefixWord ++ tailWord_174335) baseStart_174335 baseEnd_174335 := by
    simpa [prefixWord, tailWord_174335, baseEnd_174335] using wordTrace_append hprefix tailTrace_174335
  have hstable : (prefixWord ++ tailWord_174335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174335).length < 2 ^ (prefixWord ++ tailWord_174335).sum := by decide
  have hdescent : baseEnd_174335 < baseStart_174335 := by decide
  rcases family_descends (prefixWord ++ tailWord_174335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174388 : List Nat := [2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_174388 : Nat := 118140960795 + 174388 * 2 ^ 59
def prefixEnd_174388 : Nat := 4983230072969 + 3 ^ 40 * 174388 * 2
def baseEnd_174388 : Nat := 53063623334144556946969

theorem tailTrace_174388 : CollatzResearch.WordTrace tailWord_174388 prefixEnd_174388 53063623334144556946969 := by
  unfold tailWord_174388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180226446114766972177909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4240301928153022629570545 3180226446114766972177909)
  ·
    refine ⟨298146229323259403641679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3180226446114766972177909 298146229323259403641679)
    ·
      refine ⟨447219343984889105462519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298146229323259403641679 447219343984889105462519)
      ·
        refine ⟨670829015977333658193779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447219343984889105462519 670829015977333658193779)
        ·
          refine ⟨1006243523966000487290669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670829015977333658193779 1006243523966000487290669)
          ·
            refine ⟨377341321487250182734001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1006243523966000487290669 377341321487250182734001)
            ·
              refine ⟨283005991115437637050501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377341321487250182734001 283005991115437637050501)
              ·
                refine ⟨53063623334144556946969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283005991115437637050501 53063623334144556946969)
                ·
                  rfl

theorem cell19_174388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_174388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174388 prefixEnd_174388 := by exact prefixLift 174388
  have htrace : WordTrace (prefixWord ++ tailWord_174388) baseStart_174388 baseEnd_174388 := by
    simpa [prefixWord, tailWord_174388, baseEnd_174388] using wordTrace_append hprefix tailTrace_174388
  have hstable : (prefixWord ++ tailWord_174388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174388).length < 2 ^ (prefixWord ++ tailWord_174388).sum := by decide
  have hdescent : baseEnd_174388 < baseStart_174388 := by decide
  rcases family_descends (prefixWord ++ tailWord_174388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174392 : List Nat := [2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_174392 : Nat := 118140960795 + 174392 * 2 ^ 59
def prefixEnd_174392 : Nat := 4983230072969 + 3 ^ 40 * 174392 * 2
def baseEnd_174392 : Nat := 53064840473473732858069

theorem tailTrace_174392 : CollatzResearch.WordTrace tailWord_174392 prefixEnd_174392 53064840473473732858069 := by
  unfold tailWord_174392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180299392107521313750715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4240399189476695085000953 3180299392107521313750715)
  ·
    refine ⟨4770449088161281970626073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3180299392107521313750715 4770449088161281970626073)
    ·
      refine ⟨3577836816120961477969555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4770449088161281970626073 3577836816120961477969555)
      ·
        refine ⟨5366755224181442216954333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3577836816120961477969555 5366755224181442216954333)
        ·
          refine ⟨2012533209068040831357875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5366755224181442216954333 2012533209068040831357875)
          ·
            refine ⟨3018799813602061247036813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012533209068040831357875 3018799813602061247036813)
            ·
              refine ⟨1132049930100772967638805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3018799813602061247036813 1132049930100772967638805)
              ·
                refine ⟨53064840473473732858069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1132049930100772967638805 53064840473473732858069)
                ·
                  rfl

theorem cell19_174392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_174392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174392 prefixEnd_174392 := by exact prefixLift 174392
  have htrace : WordTrace (prefixWord ++ tailWord_174392) baseStart_174392 baseEnd_174392 := by
    simpa [prefixWord, tailWord_174392, baseEnd_174392] using wordTrace_append hprefix tailTrace_174392
  have hstable : (prefixWord ++ tailWord_174392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174392).length < 2 ^ (prefixWord ++ tailWord_174392).sum := by decide
  have hdescent : baseEnd_174392 < baseStart_174392 := by decide
  rcases family_descends (prefixWord ++ tailWord_174392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174428 : List Nat := [2, 2, 4, 3, 8]
def baseStart_174428 : Nat := 118140960795 + 174428 * 2 ^ 59
def prefixEnd_174428 : Nat := 4983230072969 + 3 ^ 40 * 174428 * 2
def baseEnd_174428 : Nat := 1965770175090233928073

theorem tailTrace_174428 : CollatzResearch.WordTrace tailWord_174428 prefixEnd_174428 1965770175090233928073 := by
  unfold tailWord_174428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180955906042310387905969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4241274541389747183874625 3180955906042310387905969)
  ·
    refine ⟨2385716929531732790929477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3180955906042310387905969 2385716929531732790929477)
    ·
      refine ⟨447321924287199898299277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2385716929531732790929477 447321924287199898299277)
      ·
        refine ⟨167745721607699961862229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447321924287199898299277 167745721607699961862229)
        ·
          refine ⟨1965770175090233928073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 167745721607699961862229 1965770175090233928073)
          ·
            rfl

theorem cell19_174428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 8].length) (baseStart_174428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174428 prefixEnd_174428 := by exact prefixLift 174428
  have htrace : WordTrace (prefixWord ++ tailWord_174428) baseStart_174428 baseEnd_174428 := by
    simpa [prefixWord, tailWord_174428, baseEnd_174428] using wordTrace_append hprefix tailTrace_174428
  have hstable : (prefixWord ++ tailWord_174428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174428).length < 2 ^ (prefixWord ++ tailWord_174428).sum := by decide
  have hdescent : baseEnd_174428 < baseStart_174428 := by decide
  rcases family_descends (prefixWord ++ tailWord_174428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174521 : List Nat := [1, 2, 1, 4, 3, 3, 2, 3]
def baseStart_174521 : Nat := 118140960795 + 174521 * 2 ^ 59
def prefixEnd_174521 : Nat := 4983230072969 + 3 ^ 40 * 174521 * 2
def baseEnd_174521 : Nat := 53104093216839655991051

theorem tailTrace_174521 : CollatzResearch.WordTrace tailWord_174521 prefixEnd_174521 53104093216839655991051 := by
  unfold tailWord_174521
  simp only [CollatzResearch.WordTrace]
  refine ⟨6365303800747697658947417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4243535867165131772631611 6365303800747697658947417)
  ·
    refine ⟨4773977850560773244210563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6365303800747697658947417 4773977850560773244210563)
    ·
      refine ⟨7160966775841159866315845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4773977850560773244210563 7160966775841159866315845)
      ·
        refine ⟨1342681270470217474934221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7160966775841159866315845 1342681270470217474934221)
        ·
          refine ⟨503505476426331553100333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1342681270470217474934221 503505476426331553100333)
          ·
            refine ⟨188814553659874332412625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 503505476426331553100333 188814553659874332412625)
            ·
              refine ⟨141610915244905749309469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188814553659874332412625 141610915244905749309469)
              ·
                refine ⟨53104093216839655991051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141610915244905749309469 53104093216839655991051)
                ·
                  rfl

theorem cell19_174521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_174521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174521 prefixEnd_174521 := by exact prefixLift 174521
  have htrace : WordTrace (prefixWord ++ tailWord_174521) baseStart_174521 baseEnd_174521 := by
    simpa [prefixWord, tailWord_174521, baseEnd_174521] using wordTrace_append hprefix tailTrace_174521
  have hstable : (prefixWord ++ tailWord_174521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174521).length < 2 ^ (prefixWord ++ tailWord_174521).sum := by decide
  have hdescent : baseEnd_174521 < baseStart_174521 := by decide
  rcases family_descends (prefixWord ++ tailWord_174521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174540 : List Nat := [2, 2, 1, 4, 4, 1, 5]
def baseStart_174540 : Nat := 118140960795 + 174540 * 2 ^ 59
def prefixEnd_174540 : Nat := 4983230072969 + 3 ^ 40 * 174540 * 2
def baseEnd_174540 : Nat := 17703291542884413856259

theorem tailTrace_174540 : CollatzResearch.WordTrace tailWord_174540 prefixEnd_174540 17703291542884413856259 := by
  unfold tailWord_174540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182998393839431951944537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4243997858452575935926049 3182998393839431951944537)
  ·
    refine ⟨2387248795379573963958403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3182998393839431951944537 2387248795379573963958403)
    ·
      refine ⟨3580873193069360945937605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387248795379573963958403 3580873193069360945937605)
      ·
        refine ⟨671413723700505177363301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3580873193069360945937605 671413723700505177363301)
        ·
          refine ⟨125890073193844720755619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 671413723700505177363301 125890073193844720755619)
          ·
            refine ⟨188835109790767081133429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125890073193844720755619 188835109790767081133429)
            ·
              refine ⟨17703291542884413856259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188835109790767081133429 17703291542884413856259)
              ·
                rfl

theorem cell19_174540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_174540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174540 prefixEnd_174540 := by exact prefixLift 174540
  have htrace : WordTrace (prefixWord ++ tailWord_174540) baseStart_174540 baseEnd_174540 := by
    simpa [prefixWord, tailWord_174540, baseEnd_174540] using wordTrace_append hprefix tailTrace_174540
  have hstable : (prefixWord ++ tailWord_174540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174540).length < 2 ^ (prefixWord ++ tailWord_174540).sum := by decide
  have hdescent : baseEnd_174540 < baseStart_174540 := by decide
  rcases family_descends (prefixWord ++ tailWord_174540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174599 : List Nat := [1, 1, 4, 3, 4, 6]
def baseStart_174599 : Nat := 118140960795 + 174599 * 2 ^ 59
def prefixEnd_174599 : Nat := 4983230072969 + 3 ^ 40 * 174599 * 2
def baseEnd_174599 : Nat := 5903091937084287361945

theorem tailTrace_174599 : CollatzResearch.WordTrace tailWord_174599 prefixEnd_174599 5903091937084287361945 := by
  unfold tailWord_174599
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368148694465116980286851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4245432462976744653524567 6368148694465116980286851)
  ·
    refine ⟨9552223041697675470430277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6368148694465116980286851 9552223041697675470430277)
    ·
      refine ⟨1791041820318314150705677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9552223041697675470430277 1791041820318314150705677)
      ·
        refine ⟨671640682619367806514629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1791041820318314150705677 671640682619367806514629)
        ·
          refine ⟨125932627991131463721493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 671640682619367806514629 125932627991131463721493)
          ·
            refine ⟨5903091937084287361945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125932627991131463721493 5903091937084287361945)
            ·
              rfl

theorem cell19_174599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 6].length) (baseStart_174599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174599 prefixEnd_174599 := by exact prefixLift 174599
  have htrace : WordTrace (prefixWord ++ tailWord_174599) baseStart_174599 baseEnd_174599 := by
    simpa [prefixWord, tailWord_174599, baseEnd_174599] using wordTrace_append hprefix tailTrace_174599
  have hstable : (prefixWord ++ tailWord_174599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174599).length < 2 ^ (prefixWord ++ tailWord_174599).sum := by decide
  have hdescent : baseEnd_174599 < baseStart_174599 := by decide
  rcases family_descends (prefixWord ++ tailWord_174599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174654 : List Nat := [4, 2, 1, 4, 1, 1, 6]
def baseStart_174654 : Nat := 118140960795 + 174654 * 2 ^ 59
def prefixEnd_174654 : Nat := 4983230072969 + 3 ^ 40 * 174654 * 2
def baseEnd_174654 : Nat := 17714854366511585011711

theorem tailTrace_174654 : CollatzResearch.WordTrace tailWord_174654 prefixEnd_174654 17714854366511585011711 := by
  unfold tailWord_174654
  simp only [CollatzResearch.WordTrace]
  refine ⟨796269338658232671692377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4246769806177240915692677 796269338658232671692377)
  ·
    refine ⟨597202003993674503769283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 796269338658232671692377 597202003993674503769283)
    ·
      refine ⟨895803005990511755653925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597202003993674503769283 895803005990511755653925)
      ·
        refine ⟨167963063623220954185111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 895803005990511755653925 167963063623220954185111)
        ·
          refine ⟨251944595434831431277667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167963063623220954185111 251944595434831431277667)
          ·
            refine ⟨377916893152247146916501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251944595434831431277667 377916893152247146916501)
            ·
              refine ⟨17714854366511585011711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 377916893152247146916501 17714854366511585011711)
              ·
                rfl

theorem cell19_174654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_174654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174654 prefixEnd_174654 := by exact prefixLift 174654
  have htrace : WordTrace (prefixWord ++ tailWord_174654) baseStart_174654 baseEnd_174654 := by
    simpa [prefixWord, tailWord_174654, baseEnd_174654] using wordTrace_append hprefix tailTrace_174654
  have hstable : (prefixWord ++ tailWord_174654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174654).length < 2 ^ (prefixWord ++ tailWord_174654).sum := by decide
  have hdescent : baseEnd_174654 < baseStart_174654 := by decide
  rcases family_descends (prefixWord ++ tailWord_174654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174686 : List Nat := [4, 4, 1, 2, 1, 2, 2, 3]
def baseStart_174686 : Nat := 118140960795 + 174686 * 2 ^ 59
def prefixEnd_174686 : Nat := 4983230072969 + 3 ^ 40 * 174686 * 2
def baseEnd_174686 : Nat := 53154300214168162323935

theorem tailTrace_174686 : CollatzResearch.WordTrace tailWord_174686 prefixEnd_174686 53154300214168162323935 := by
  unfold tailWord_174686
  simp only [CollatzResearch.WordTrace]
  refine ⟨796415230643741354837989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4247547896766620559135941 796415230643741354837989)
  ·
    refine ⟨149327855745701504032123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 796415230643741354837989 149327855745701504032123)
    ·
      refine ⟨223991783618552256048185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149327855745701504032123 223991783618552256048185)
      ·
        refine ⟨167993837713914192036139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223991783618552256048185 167993837713914192036139)
        ·
          refine ⟨251990756570871288054209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167993837713914192036139 251990756570871288054209)
          ·
            refine ⟨188993067428153466040657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251990756570871288054209 188993067428153466040657)
            ·
              refine ⟨141744800571115099530493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188993067428153466040657 141744800571115099530493)
              ·
                refine ⟨53154300214168162323935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141744800571115099530493 53154300214168162323935)
                ·
                  rfl

theorem cell19_174686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_174686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174686 prefixEnd_174686 := by exact prefixLift 174686
  have htrace : WordTrace (prefixWord ++ tailWord_174686) baseStart_174686 baseEnd_174686 := by
    simpa [prefixWord, tailWord_174686, baseEnd_174686] using wordTrace_append hprefix tailTrace_174686
  have hstable : (prefixWord ++ tailWord_174686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174686).length < 2 ^ (prefixWord ++ tailWord_174686).sum := by decide
  have hdescent : baseEnd_174686 < baseStart_174686 := by decide
  rcases family_descends (prefixWord ++ tailWord_174686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174785 : List Nat := [1, 2, 6, 2, 1, 2, 1, 4]
def baseStart_174785 : Nat := 118140960795 + 174785 * 2 ^ 59
def prefixEnd_174785 : Nat := 4983230072969 + 3 ^ 40 * 174785 * 2
def baseEnd_174785 : Nat := 53184424412565266123665

theorem tailTrace_174785 : CollatzResearch.WordTrace tailWord_174785 prefixEnd_174785 53184424412565266123665 := by
  unfold tailWord_174785
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374932671791270746557809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4249955114527513831038539 6374932671791270746557809)
  ·
    refine ⟨4781199503843453059918357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6374932671791270746557809 4781199503843453059918357)
    ·
      refine ⟨224118726742661862183673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4781199503843453059918357 224118726742661862183673)
      ·
        refine ⟨168089045056996396637755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224118726742661862183673 168089045056996396637755)
        ·
          refine ⟨252133567585494594956633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168089045056996396637755 252133567585494594956633)
          ·
            refine ⟨189100175689120946217475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252133567585494594956633 189100175689120946217475)
            ·
              refine ⟨283650263533681419326213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189100175689120946217475 283650263533681419326213)
              ·
                refine ⟨53184424412565266123665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283650263533681419326213 53184424412565266123665)
                ·
                  rfl

theorem cell19_174785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_174785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174785 prefixEnd_174785 := by exact prefixLift 174785
  have htrace : WordTrace (prefixWord ++ tailWord_174785) baseStart_174785 baseEnd_174785 := by
    simpa [prefixWord, tailWord_174785, baseEnd_174785] using wordTrace_append hprefix tailTrace_174785
  have hstable : (prefixWord ++ tailWord_174785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174785).length < 2 ^ (prefixWord ++ tailWord_174785).sum := by decide
  have hdescent : baseEnd_174785 < baseStart_174785 := by decide
  rcases family_descends (prefixWord ++ tailWord_174785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174808 : List Nat := [2, 1, 2, 2, 3, 3, 3, 3]
def baseStart_174808 : Nat := 118140960795 + 174808 * 2 ^ 59
def prefixEnd_174808 : Nat := 4983230072969 + 3 ^ 40 * 174808 * 2
def baseEnd_174808 : Nat := 53191422963708027612491

theorem tailTrace_174808 : CollatzResearch.WordTrace tailWord_174808 prefixEnd_174808 53191422963708027612491 := by
  unfold tailWord_174808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187885775353972837322539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4250514367138630449763385 3187885775353972837322539)
  ·
    refine ⟨4781828663030959255983809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3187885775353972837322539 4781828663030959255983809)
    ·
      refine ⟨3586371497273219441987857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4781828663030959255983809 3586371497273219441987857)
      ·
        refine ⟨2689778622954914581490893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3586371497273219441987857 2689778622954914581490893)
        ·
          refine ⟨1008666983608092968059085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2689778622954914581490893 1008666983608092968059085)
          ·
            refine ⟨378250118853034863022157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1008666983608092968059085 378250118853034863022157)
            ·
              refine ⟨141843794569888073633309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 378250118853034863022157 141843794569888073633309)
              ·
                refine ⟨53191422963708027612491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141843794569888073633309 53191422963708027612491)
                ·
                  rfl

theorem cell19_174808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_174808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174808 prefixEnd_174808 := by exact prefixLift 174808
  have htrace : WordTrace (prefixWord ++ tailWord_174808) baseStart_174808 baseEnd_174808 := by
    simpa [prefixWord, tailWord_174808, baseEnd_174808] using wordTrace_append hprefix tailTrace_174808
  have hstable : (prefixWord ++ tailWord_174808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174808).length < 2 ^ (prefixWord ++ tailWord_174808).sum := by decide
  have hdescent : baseEnd_174808 < baseStart_174808 := by decide
  rcases family_descends (prefixWord ++ tailWord_174808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174829 : List Nat := [1, 5, 1, 2, 1, 1, 8]
def baseStart_174829 : Nat := 118140960795 + 174829 * 2 ^ 59
def prefixEnd_174829 : Nat := 4983230072969 + 3 ^ 40 * 174829 * 2
def baseEnd_174829 : Nat := 17732604315062067048589

theorem tailTrace_174829 : CollatzResearch.WordTrace tailWord_174829 prefixEnd_174829 17732604315062067048589 := by
  unfold tailWord_174829
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376537483631866261159541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4251024989087910840773027 6376537483631866261159541)
  ·
    refine ⟨597800389090487461983707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6376537483631866261159541 597800389090487461983707)
    ·
      refine ⟨896700583635731192975561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597800389090487461983707 896700583635731192975561)
      ·
        refine ⟨672525437726798394731671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 896700583635731192975561 672525437726798394731671)
        ·
          refine ⟨1008788156590197592097507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672525437726798394731671 1008788156590197592097507)
          ·
            refine ⟨1513182234885296388146261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008788156590197592097507 1513182234885296388146261)
            ·
              refine ⟨17732604315062067048589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1513182234885296388146261 17732604315062067048589)
              ·
                rfl

theorem cell19_174829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_174829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174829 prefixEnd_174829 := by exact prefixLift 174829
  have htrace : WordTrace (prefixWord ++ tailWord_174829) baseStart_174829 baseEnd_174829 := by
    simpa [prefixWord, tailWord_174829, baseEnd_174829] using wordTrace_append hprefix tailTrace_174829
  have hstable : (prefixWord ++ tailWord_174829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174829).length < 2 ^ (prefixWord ++ tailWord_174829).sum := by decide
  have hdescent : baseEnd_174829 < baseStart_174829 := by decide
  rcases family_descends (prefixWord ++ tailWord_174829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174884 : List Nat := [2, 3, 1, 3, 3, 2, 5]
def baseStart_174884 : Nat := 118140960795 + 174884 * 2 ^ 59
def prefixEnd_174884 : Nat := 4983230072969 + 3 ^ 40 * 174884 * 2
def baseEnd_174884 : Nat := 17738182870320789974465

theorem tailTrace_174884 : CollatzResearch.WordTrace tailWord_174884 prefixEnd_174884 17738182870320789974465 := by
  unfold tailWord_174884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189271749216305327205853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4252362332288407102941137 3189271749216305327205853)
  ·
    refine ⟨1195976905956114497702195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3189271749216305327205853 1195976905956114497702195)
    ·
      refine ⟨1793965358934171746553293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195976905956114497702195 1793965358934171746553293)
      ·
        refine ⟨672737009600314404957485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1793965358934171746553293 672737009600314404957485)
        ·
          refine ⟨252276378600117901859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672737009600314404957485 252276378600117901859057)
          ·
            refine ⟨189207283950088426394293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252276378600117901859057 189207283950088426394293)
            ·
              refine ⟨17738182870320789974465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189207283950088426394293 17738182870320789974465)
              ·
                rfl

theorem cell19_174884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_174884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174884 prefixEnd_174884 := by exact prefixLift 174884
  have htrace : WordTrace (prefixWord ++ tailWord_174884) baseStart_174884 baseEnd_174884 := by
    simpa [prefixWord, tailWord_174884, baseEnd_174884] using wordTrace_append hprefix tailTrace_174884
  have hstable : (prefixWord ++ tailWord_174884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174884).length < 2 ^ (prefixWord ++ tailWord_174884).sum := by decide
  have hdescent : baseEnd_174884 < baseStart_174884 := by decide
  rcases family_descends (prefixWord ++ tailWord_174884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174924 : List Nat := [2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_174924 : Nat := 118140960795 + 174924 * 2 ^ 59
def prefixEnd_174924 : Nat := 4983230072969 + 3 ^ 40 * 174924 * 2
def baseEnd_174924 : Nat := 53226720004254129034397

theorem tailTrace_174924 : CollatzResearch.WordTrace tailWord_174924 prefixEnd_174924 53226720004254129034397 := by
  unfold tailWord_174924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190001209143848742933913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4253334945525131657245217 3190001209143848742933913)
  ·
    refine ⟨2392500906857886557200435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3190001209143848742933913 2392500906857886557200435)
    ·
      refine ⟨3588751360286829835800653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392500906857886557200435 3588751360286829835800653)
      ·
        refine ⟨1345781760107561188425245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3588751360286829835800653 1345781760107561188425245)
        ·
          refine ⟨504668160040335445659467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1345781760107561188425245 504668160040335445659467)
          ·
            refine ⟨757002240060503168489201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504668160040335445659467 757002240060503168489201)
            ·
              refine ⟨567751680045377376366901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757002240060503168489201 567751680045377376366901)
              ·
                refine ⟨53226720004254129034397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 567751680045377376366901 53226720004254129034397)
                ·
                  rfl

theorem cell19_174924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_174924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174924 prefixEnd_174924 := by exact prefixLift 174924
  have htrace : WordTrace (prefixWord ++ tailWord_174924) baseStart_174924 baseEnd_174924 := by
    simpa [prefixWord, tailWord_174924, baseEnd_174924] using wordTrace_append hprefix tailTrace_174924
  have hstable : (prefixWord ++ tailWord_174924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174924).length < 2 ^ (prefixWord ++ tailWord_174924).sum := by decide
  have hdescent : baseEnd_174924 < baseStart_174924 := by decide
  rcases family_descends (prefixWord ++ tailWord_174924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174958 : List Nat := [4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_174958 : Nat := 118140960795 + 174958 * 2 ^ 59
def prefixEnd_174958 : Nat := 4983230072969 + 3 ^ 40 * 174958 * 2
def baseEnd_174958 : Nat := 53237065688552124278749

theorem tailTrace_174958 : CollatzResearch.WordTrace tailWord_174958 prefixEnd_174958 53237065688552124278749 := by
  unfold tailWord_174958
  simp only [CollatzResearch.WordTrace]
  refine ⟨797655312520565161575691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4254161666776347528403685 797655312520565161575691)
  ·
    refine ⟨1196482968780847742363537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 797655312520565161575691 1196482968780847742363537)
    ·
      refine ⟨897362226585635806772653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1196482968780847742363537 897362226585635806772653)
      ·
        refine ⟨336510834969613427539745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 897362226585635806772653 336510834969613427539745)
        ·
          refine ⟨252383126227210070654809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336510834969613427539745 252383126227210070654809)
          ·
            refine ⟨189287344670407552991107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252383126227210070654809 189287344670407552991107)
            ·
              refine ⟨283931017005611329486661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189287344670407552991107 283931017005611329486661)
              ·
                refine ⟨53237065688552124278749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283931017005611329486661 53237065688552124278749)
                ·
                  rfl

theorem cell19_174958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_174958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174958 prefixEnd_174958 := by exact prefixLift 174958
  have htrace : WordTrace (prefixWord ++ tailWord_174958) baseStart_174958 baseEnd_174958 := by
    simpa [prefixWord, tailWord_174958, baseEnd_174958] using wordTrace_append hprefix tailTrace_174958
  have hstable : (prefixWord ++ tailWord_174958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174958).length < 2 ^ (prefixWord ++ tailWord_174958).sum := by decide
  have hdescent : baseEnd_174958 < baseStart_174958 := by decide
  rcases family_descends (prefixWord ++ tailWord_174958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174962 : List Nat := [3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_174962 : Nat := 118140960795 + 174962 * 2 ^ 59
def prefixEnd_174962 : Nat := 4983230072969 + 3 ^ 40 * 174962 * 2
def baseEnd_174962 : Nat := 53238282827881300189849

theorem tailTrace_174962 : CollatzResearch.WordTrace tailWord_174962 prefixEnd_174962 53238282827881300189849 := by
  unfold tailWord_174962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595347098037507493937785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4254258928100019983834093 1595347098037507493937785)
  ·
    refine ⟨1196510323528130620453339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1595347098037507493937785 1196510323528130620453339)
    ·
      refine ⟨1794765485292195930680009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196510323528130620453339 1794765485292195930680009)
      ·
        refine ⟨1346074113969146948010007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794765485292195930680009 1346074113969146948010007)
        ·
          refine ⟨2019111170953720422015011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346074113969146948010007 2019111170953720422015011)
          ·
            refine ⟨3028666756430580633022517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019111170953720422015011 3028666756430580633022517)
            ·
              refine ⟨283937508415366934345861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3028666756430580633022517 283937508415366934345861)
              ·
                refine ⟨53238282827881300189849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283937508415366934345861 53238282827881300189849)
                ·
                  rfl

theorem cell19_174962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_174962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_174962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_174962 prefixEnd_174962 := by exact prefixLift 174962
  have htrace : WordTrace (prefixWord ++ tailWord_174962) baseStart_174962 baseEnd_174962 := by
    simpa [prefixWord, tailWord_174962, baseEnd_174962] using wordTrace_append hprefix tailTrace_174962
  have hstable : (prefixWord ++ tailWord_174962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174962).length < 2 ^ (prefixWord ++ tailWord_174962).sum := by decide
  have hdescent : baseEnd_174962 < baseStart_174962 := by decide
  rcases family_descends (prefixWord ++ tailWord_174962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175038 : List Nat := [4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_175038 : Nat := 118140960795 + 175038 * 2 ^ 59
def prefixEnd_175038 : Nat := 4983230072969 + 3 ^ 40 * 175038 * 2
def baseEnd_175038 : Nat := 53261408475135642500753

theorem tailTrace_175038 : CollatzResearch.WordTrace tailWord_175038 prefixEnd_175038 53261408475135642500753 := by
  unfold tailWord_175038
  simp only [CollatzResearch.WordTrace]
  refine ⟨798020042484336869439721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4256106893249796637011845 798020042484336869439721)
  ·
    refine ⟨598515031863252652079791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 798020042484336869439721 598515031863252652079791)
    ·
      refine ⟨897772547794878978119687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598515031863252652079791 897772547794878978119687)
      ·
        refine ⟨1346658821692318467179531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897772547794878978119687 1346658821692318467179531)
        ·
          refine ⟨2019988232538477700769297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346658821692318467179531 2019988232538477700769297)
          ·
            refine ⟨1514991174403858275576973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019988232538477700769297 1514991174403858275576973)
            ·
              refine ⟨568121690401446853341365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1514991174403858275576973 568121690401446853341365)
              ·
                refine ⟨53261408475135642500753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568121690401446853341365 53261408475135642500753)
                ·
                  rfl

theorem cell19_175038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_175038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175038 prefixEnd_175038 := by exact prefixLift 175038
  have htrace : WordTrace (prefixWord ++ tailWord_175038) baseStart_175038 baseEnd_175038 := by
    simpa [prefixWord, tailWord_175038, baseEnd_175038] using wordTrace_append hprefix tailTrace_175038
  have hstable : (prefixWord ++ tailWord_175038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175038).length < 2 ^ (prefixWord ++ tailWord_175038).sum := by decide
  have hdescent : baseEnd_175038 < baseStart_175038 := by decide
  rcases family_descends (prefixWord ++ tailWord_175038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175074 : List Nat := [3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_175074 : Nat := 118140960795 + 175074 * 2 ^ 59
def prefixEnd_175074 : Nat := 4983230072969 + 3 ^ 40 * 175074 * 2
def baseEnd_175074 : Nat := 53272362729098225700655

theorem tailTrace_175074 : CollatzResearch.WordTrace tailWord_175074 prefixEnd_175074 53272362729098225700655 := by
  unfold tailWord_175074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596368341936068275957069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4256982245162848735885517 1596368341936068275957069)
  ·
    refine ⟨598638128226025603483901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1596368341936068275957069 598638128226025603483901)
    ·
      refine ⟨224489298084759601306463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 598638128226025603483901 224489298084759601306463)
      ·
        refine ⟨336733947127139401959695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224489298084759601306463 336733947127139401959695)
        ·
          refine ⟨505100920690709102939543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336733947127139401959695 505100920690709102939543)
          ·
            refine ⟨757651381036063654409315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505100920690709102939543 757651381036063654409315)
            ·
              refine ⟨1136477071554095481613973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757651381036063654409315 1136477071554095481613973)
              ·
                refine ⟨53272362729098225700655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1136477071554095481613973 53272362729098225700655)
                ·
                  rfl

theorem cell19_175074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_175074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175074 prefixEnd_175074 := by exact prefixLift 175074
  have htrace : WordTrace (prefixWord ++ tailWord_175074) baseStart_175074 baseEnd_175074 := by
    simpa [prefixWord, tailWord_175074, baseEnd_175074] using wordTrace_append hprefix tailTrace_175074
  have hstable : (prefixWord ++ tailWord_175074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175074).length < 2 ^ (prefixWord ++ tailWord_175074).sum := by decide
  have hdescent : baseEnd_175074 < baseStart_175074 := by decide
  rcases family_descends (prefixWord ++ tailWord_175074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175097 : List Nat := [1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_175097 : Nat := 118140960795 + 175097 * 2 ^ 59
def prefixEnd_175097 : Nat := 4983230072969 + 3 ^ 40 * 175097 * 2
def baseEnd_175097 : Nat := 53279361280240987189481

theorem tailTrace_175097 : CollatzResearch.WordTrace tailWord_175097 prefixEnd_175097 53279361280240987189481 := by
  unfold tailWord_175097
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386312246660948031915545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4257541497773965354610363 6386312246660948031915545)
  ·
    refine ⟨4789734184995711023936659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6386312246660948031915545 4789734184995711023936659)
    ·
      refine ⟨7184601277493566535904989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4789734184995711023936659 7184601277493566535904989)
      ·
        refine ⟨2694225479060087450964371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7184601277493566535904989 2694225479060087450964371)
        ·
          refine ⟨4041338218590131176446557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694225479060087450964371 4041338218590131176446557)
          ·
            refine ⟨1515501831971299191167459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4041338218590131176446557 1515501831971299191167459)
            ·
              refine ⟨2273252747956948786751189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515501831971299191167459 2273252747956948786751189)
              ·
                refine ⟨53279361280240987189481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2273252747956948786751189 53279361280240987189481)
                ·
                  rfl

theorem cell19_175097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_175097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175097 prefixEnd_175097 := by exact prefixLift 175097
  have htrace : WordTrace (prefixWord ++ tailWord_175097) baseStart_175097 baseEnd_175097 := by
    simpa [prefixWord, tailWord_175097, baseEnd_175097] using wordTrace_append hprefix tailTrace_175097
  have hstable : (prefixWord ++ tailWord_175097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175097).length < 2 ^ (prefixWord ++ tailWord_175097).sum := by decide
  have hdescent : baseEnd_175097 < baseStart_175097 := by decide
  rcases family_descends (prefixWord ++ tailWord_175097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175116 : List Nat := [2, 2, 1, 2, 3, 9]
def baseStart_175116 : Nat := 118140960795 + 175116 * 2 ^ 59
def prefixEnd_175116 : Nat := 4983230072969 + 3 ^ 40 * 175116 * 2
def baseEnd_175116 : Nat := 5920571410228285863023

theorem tailTrace_175116 : CollatzResearch.WordTrace tailWord_175116 prefixEnd_175116 5920571410228285863023 := by
  unfold tailWord_175116
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193502616796057138428601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4258003489061409517904801 3193502616796057138428601)
  ·
    refine ⟨2395126962597042853821451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3193502616796057138428601 2395126962597042853821451)
    ·
      refine ⟨3592690443895564280732177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395126962597042853821451 3592690443895564280732177)
      ·
        refine ⟨2694517832921673210549133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3592690443895564280732177 2694517832921673210549133)
        ·
          refine ⟨1010444187345627453955925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2694517832921673210549133 1010444187345627453955925)
          ·
            refine ⟨5920571410228285863023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1010444187345627453955925 5920571410228285863023)
            ·
              rfl

theorem cell19_175116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_175116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175116 prefixEnd_175116 := by exact prefixLift 175116
  have htrace : WordTrace (prefixWord ++ tailWord_175116) baseStart_175116 baseEnd_175116 := by
    simpa [prefixWord, tailWord_175116, baseEnd_175116] using wordTrace_append hprefix tailTrace_175116
  have hstable : (prefixWord ++ tailWord_175116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175116).length < 2 ^ (prefixWord ++ tailWord_175116).sum := by decide
  have hdescent : baseEnd_175116 < baseStart_175116 := by decide
  rcases family_descends (prefixWord ++ tailWord_175116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175150 : List Nat := [4, 1, 3, 1, 1, 1, 5, 3]
def baseStart_175150 : Nat := 118140960795 + 175150 * 2 ^ 59
def prefixEnd_175150 : Nat := 4983230072969 + 3 ^ 40 * 175150 * 2
def baseEnd_175150 : Nat := 53295488376352568011559

theorem tailTrace_175150 : CollatzResearch.WordTrace tailWord_175150 prefixEnd_175150 53295488376352568011559 := by
  unfold tailWord_175150
  simp only [CollatzResearch.WordTrace]
  refine ⟨798530664433617260449363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4258830210312625389063269 798530664433617260449363)
  ·
    refine ⟨1197795996650425890674045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798530664433617260449363 1197795996650425890674045)
    ·
      refine ⟨449173498743909709002767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1197795996650425890674045 449173498743909709002767)
      ·
        refine ⟨673760248115864563504151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449173498743909709002767 673760248115864563504151)
        ·
          refine ⟨1010640372173796845256227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673760248115864563504151 1010640372173796845256227)
          ·
            refine ⟨1515960558260695267884341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010640372173796845256227 1515960558260695267884341)
            ·
              refine ⟨142121302336940181364157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1515960558260695267884341 142121302336940181364157)
              ·
                refine ⟨53295488376352568011559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142121302336940181364157 53295488376352568011559)
                ·
                  rfl

theorem cell19_175150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_175150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175150 prefixEnd_175150 := by exact prefixLift 175150
  have htrace : WordTrace (prefixWord ++ tailWord_175150) baseStart_175150 baseEnd_175150 := by
    simpa [prefixWord, tailWord_175150, baseEnd_175150] using wordTrace_append hprefix tailTrace_175150
  have hstable : (prefixWord ++ tailWord_175150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175150).length < 2 ^ (prefixWord ++ tailWord_175150).sum := by decide
  have hdescent : baseEnd_175150 < baseStart_175150 := by decide
  rcases family_descends (prefixWord ++ tailWord_175150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175152 : List Nat := [2, 1, 1, 1, 2, 4, 5, 3]
def baseStart_175152 : Nat := 118140960795 + 175152 * 2 ^ 59
def prefixEnd_175152 : Nat := 4983230072969 + 3 ^ 40 * 175152 * 2
def baseEnd_175152 : Nat := 53296096946017155967109

theorem tailTrace_175152 : CollatzResearch.WordTrace tailWord_175152 prefixEnd_175152 53296096946017155967109 := by
  unfold tailWord_175152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194159130730846212583855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4258878840974461616778473 3194159130730846212583855)
  ·
    refine ⟨4791238696096269318875783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3194159130730846212583855 4791238696096269318875783)
    ·
      refine ⟨7186858044144403978313675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791238696096269318875783 7186858044144403978313675)
      ·
        refine ⟨10780287066216605967470513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7186858044144403978313675 10780287066216605967470513)
        ·
          refine ⟨8085215299662454475602885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10780287066216605967470513 8085215299662454475602885)
          ·
            refine ⟨1515977868686710214175541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8085215299662454475602885 1515977868686710214175541)
            ·
              refine ⟨142122925189379082578957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1515977868686710214175541 142122925189379082578957)
              ·
                refine ⟨53296096946017155967109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142122925189379082578957 53296096946017155967109)
                ·
                  rfl

theorem cell19_175152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_175152 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175152 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175152 prefixEnd_175152 := by exact prefixLift 175152
  have htrace : WordTrace (prefixWord ++ tailWord_175152) baseStart_175152 baseEnd_175152 := by
    simpa [prefixWord, tailWord_175152, baseEnd_175152] using wordTrace_append hprefix tailTrace_175152
  have hstable : (prefixWord ++ tailWord_175152).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175152).length < 2 ^ (prefixWord ++ tailWord_175152).sum := by decide
  have hdescent : baseEnd_175152 < baseStart_175152 := by decide
  rcases family_descends (prefixWord ++ tailWord_175152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175192 : List Nat := [2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_175192 : Nat := 118140960795 + 175192 * 2 ^ 59
def prefixEnd_175192 : Nat := 4983230072969 + 3 ^ 40 * 175192 * 2
def baseEnd_175192 : Nat := 53308268339308915078111

theorem tailTrace_175192 : CollatzResearch.WordTrace tailWord_175192 prefixEnd_175192 53308268339308915078111 := by
  unfold tailWord_175192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194888590658389628311915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4259851454211186171082553 3194888590658389628311915)
  ·
    refine ⟨4792332885987584442467873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3194888590658389628311915 4792332885987584442467873)
    ·
      refine ⟨3594249664490688331850905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4792332885987584442467873 3594249664490688331850905)
      ·
        refine ⟨2695687248368016248888179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3594249664490688331850905 2695687248368016248888179)
        ·
          refine ⟨4043530872552024373332269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695687248368016248888179 4043530872552024373332269)
          ·
            refine ⟨1516324077207009139999601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4043530872552024373332269 1516324077207009139999601)
            ·
              refine ⟨1137243057905256854999701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516324077207009139999601 1137243057905256854999701)
              ·
                refine ⟨53308268339308915078111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1137243057905256854999701 53308268339308915078111)
                ·
                  rfl

theorem cell19_175192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_175192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175192 prefixEnd_175192 := by exact prefixLift 175192
  have htrace : WordTrace (prefixWord ++ tailWord_175192) baseStart_175192 baseEnd_175192 := by
    simpa [prefixWord, tailWord_175192, baseEnd_175192] using wordTrace_append hprefix tailTrace_175192
  have hstable : (prefixWord ++ tailWord_175192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175192).length < 2 ^ (prefixWord ++ tailWord_175192).sum := by decide
  have hdescent : baseEnd_175192 < baseStart_175192 := by decide
  rcases family_descends (prefixWord ++ tailWord_175192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175207 : List Nat := [1, 1, 5, 1, 1, 5, 2, 3]
def baseStart_175207 : Nat := 118140960795 + 175207 * 2 ^ 59
def prefixEnd_175207 : Nat := 4983230072969 + 3 ^ 40 * 175207 * 2
def baseEnd_175207 : Nat := 53312832611793324744737

theorem tailTrace_175207 : CollatzResearch.WordTrace tailWord_175207 prefixEnd_175207 53312832611793324744737 := by
  unfold tailWord_175207
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390324276262436818419875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4260216184174957878946583 6390324276262436818419875)
  ·
    refine ⟨9585486414393655227629813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6390324276262436818419875 9585486414393655227629813)
    ·
      refine ⟨898639351349405177590295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9585486414393655227629813 898639351349405177590295)
      ·
        refine ⟨1347959027024107766385443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898639351349405177590295 1347959027024107766385443)
        ·
          refine ⟨2021938540536161649578165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347959027024107766385443 2021938540536161649578165)
          ·
            refine ⟨189556738175265154647953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2021938540536161649578165 189556738175265154647953)
            ·
              refine ⟨142167553631448865985965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189556738175265154647953 142167553631448865985965)
              ·
                refine ⟨53312832611793324744737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142167553631448865985965 53312832611793324744737)
                ·
                  rfl

theorem cell19_175207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_175207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175207 prefixEnd_175207 := by exact prefixLift 175207
  have htrace : WordTrace (prefixWord ++ tailWord_175207) baseStart_175207 baseEnd_175207 := by
    simpa [prefixWord, tailWord_175207, baseEnd_175207] using wordTrace_append hprefix tailTrace_175207
  have hstable : (prefixWord ++ tailWord_175207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175207).length < 2 ^ (prefixWord ++ tailWord_175207).sum := by decide
  have hdescent : baseEnd_175207 < baseStart_175207 := by decide
  rcases family_descends (prefixWord ++ tailWord_175207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175209 : List Nat := [1, 2, 1, 1, 1, 6, 4, 3]
def baseStart_175209 : Nat := 118140960795 + 175209 * 2 ^ 59
def prefixEnd_175209 : Nat := 4983230072969 + 3 ^ 40 * 175209 * 2
def baseEnd_175209 : Nat := 53313441181457912700287

theorem tailTrace_175209 : CollatzResearch.WordTrace tailWord_175209 prefixEnd_175209 53313441181457912700287 := by
  unfold tailWord_175209
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390397222255191159992681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4260264814836794106661787 6390397222255191159992681)
  ·
    refine ⟨4792797916691393369994511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6390397222255191159992681 4792797916691393369994511)
    ·
      refine ⟨7189196875037090054991767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4792797916691393369994511 7189196875037090054991767)
      ·
        refine ⟨10783795312555635082487651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189196875037090054991767 10783795312555635082487651)
        ·
          refine ⟨16175692968833452623731477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10783795312555635082487651 16175692968833452623731477)
          ·
            refine ⟨758235607914068091737413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16175692968833452623731477 758235607914068091737413)
            ·
              refine ⟨142169176483887767200765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 758235607914068091737413 142169176483887767200765)
              ·
                refine ⟨53313441181457912700287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142169176483887767200765 53313441181457912700287)
                ·
                  rfl

theorem cell19_175209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_175209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175209 prefixEnd_175209 := by exact prefixLift 175209
  have htrace : WordTrace (prefixWord ++ tailWord_175209) baseStart_175209 baseEnd_175209 := by
    simpa [prefixWord, tailWord_175209, baseEnd_175209] using wordTrace_append hprefix tailTrace_175209
  have hstable : (prefixWord ++ tailWord_175209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175209).length < 2 ^ (prefixWord ++ tailWord_175209).sum := by decide
  have hdescent : baseEnd_175209 < baseStart_175209 := by decide
  rcases family_descends (prefixWord ++ tailWord_175209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175298 : List Nat := [3, 5, 1, 1, 2, 2, 1, 4]
def baseStart_175298 : Nat := 118140960795 + 175298 * 2 ^ 59
def prefixEnd_175298 : Nat := 4983230072969 + 3 ^ 40 * 175298 * 2
def baseEnd_175298 : Nat := 53340522531532076722267

theorem tailTrace_175298 : CollatzResearch.WordTrace tailWord_175298 prefixEnd_175298 53340522531532076722267 := by
  unfold tailWord_175298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598410829733189839995637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4262428879288506239988365 1598410829733189839995637)
  ·
    refine ⟨149851015287486547499591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1598410829733189839995637 149851015287486547499591)
    ·
      refine ⟨224776522931229821249387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149851015287486547499591 224776522931229821249387)
      ·
        refine ⟨337164784396844731874081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224776522931229821249387 337164784396844731874081)
        ·
          refine ⟨252873588297633548905561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337164784396844731874081 252873588297633548905561)
          ·
            refine ⟨189655191223225161679171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252873588297633548905561 189655191223225161679171)
            ·
              refine ⟨284482786834837742518757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189655191223225161679171 284482786834837742518757)
              ·
                refine ⟨53340522531532076722267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284482786834837742518757 53340522531532076722267)
                ·
                  rfl

theorem cell19_175298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_175298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175298 prefixEnd_175298 := by exact prefixLift 175298
  have htrace : WordTrace (prefixWord ++ tailWord_175298) baseStart_175298 baseEnd_175298 := by
    simpa [prefixWord, tailWord_175298, baseEnd_175298] using wordTrace_append hprefix tailTrace_175298
  have hstable : (prefixWord ++ tailWord_175298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175298).length < 2 ^ (prefixWord ++ tailWord_175298).sum := by decide
  have hdescent : baseEnd_175298 < baseStart_175298 := by decide
  rcases family_descends (prefixWord ++ tailWord_175298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175300 : List Nat := [2, 3, 3, 1, 4, 1, 1, 4]
def baseStart_175300 : Nat := 118140960795 + 175300 * 2 ^ 59
def prefixEnd_175300 : Nat := 4983230072969 + 3 ^ 40 * 175300 * 2
def baseEnd_175300 : Nat := 53341131101196664677817

theorem tailTrace_175300 : CollatzResearch.WordTrace tailWord_175300 prefixEnd_175300 53341131101196664677817 := by
  unfold tailWord_175300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196858132462756850777677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4262477509950342467703569 3196858132462756850777677)
  ·
    refine ⟨1198821799673533819041629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3196858132462756850777677 1198821799673533819041629)
    ·
      refine ⟨449558174877575182140611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1198821799673533819041629 449558174877575182140611)
      ·
        refine ⟨674337262316362773210917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449558174877575182140611 674337262316362773210917)
        ·
          refine ⟨126438236684318019977047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 674337262316362773210917 126438236684318019977047)
          ·
            refine ⟨189657355026477029965571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126438236684318019977047 189657355026477029965571)
            ·
              refine ⟨284486032539715544948357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189657355026477029965571 284486032539715544948357)
              ·
                refine ⟨53341131101196664677817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284486032539715544948357 53341131101196664677817)
                ·
                  rfl

theorem cell19_175300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_175300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175300 prefixEnd_175300 := by exact prefixLift 175300
  have htrace : WordTrace (prefixWord ++ tailWord_175300) baseStart_175300 baseEnd_175300 := by
    simpa [prefixWord, tailWord_175300, baseEnd_175300] using wordTrace_append hprefix tailTrace_175300
  have hstable : (prefixWord ++ tailWord_175300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175300).length < 2 ^ (prefixWord ++ tailWord_175300).sum := by decide
  have hdescent : baseEnd_175300 < baseStart_175300 := by decide
  rcases family_descends (prefixWord ++ tailWord_175300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175414 : List Nat := [5, 1, 2, 3, 1, 1, 2, 4]
def baseStart_175414 : Nat := 118140960795 + 175414 * 2 ^ 59
def prefixEnd_175414 : Nat := 4983230072969 + 3 ^ 40 * 175414 * 2
def baseEnd_175414 : Nat := 53375819572078178144173

theorem tailTrace_175414 : CollatzResearch.WordTrace tailWord_175414 prefixEnd_175414 53375819572078178144173 := by
  unfold tailWord_175414
  simp only [CollatzResearch.WordTrace]
  refine ⟨399867136657031948200331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4265249457675007447470197 399867136657031948200331)
  ·
    refine ⟨599800704985547922300497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399867136657031948200331 599800704985547922300497)
    ·
      refine ⟨449850528739160941725373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 599800704985547922300497 449850528739160941725373)
      ·
        refine ⟨168693948277185353147015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449850528739160941725373 168693948277185353147015)
        ·
          refine ⟨253040922415778029720523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168693948277185353147015 253040922415778029720523)
          ·
            refine ⟨379561383623667044580785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253040922415778029720523 379561383623667044580785)
            ·
              refine ⟨284671037717750283435589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379561383623667044580785 284671037717750283435589)
              ·
                refine ⟨53375819572078178144173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284671037717750283435589 53375819572078178144173)
                ·
                  rfl

theorem cell19_175414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_175414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175414 prefixEnd_175414 := by exact prefixLift 175414
  have htrace : WordTrace (prefixWord ++ tailWord_175414) baseStart_175414 baseEnd_175414 := by
    simpa [prefixWord, tailWord_175414, baseEnd_175414] using wordTrace_append hprefix tailTrace_175414
  have hstable : (prefixWord ++ tailWord_175414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175414).length < 2 ^ (prefixWord ++ tailWord_175414).sum := by decide
  have hdescent : baseEnd_175414 < baseStart_175414 := by decide
  rcases family_descends (prefixWord ++ tailWord_175414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175420 : List Nat := [2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_175420 : Nat := 118140960795 + 175420 * 2 ^ 59
def prefixEnd_175420 : Nat := 4983230072969 + 3 ^ 40 * 175420 * 2
def baseEnd_175420 : Nat := 53377645281071942010823

theorem tailTrace_175420 : CollatzResearch.WordTrace tailWord_175420 prefixEnd_175420 53377645281071942010823 := by
  unfold tailWord_175420
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199046512245387097961857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4265395349660516130615809 3199046512245387097961857)
  ·
    refine ⟨2399284884184040323471393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3199046512245387097961857 2399284884184040323471393)
    ·
      refine ⟨1799463663138030242603545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2399284884184040323471393 1799463663138030242603545)
      ·
        refine ⟨1349597747353522681952659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1799463663138030242603545 1349597747353522681952659)
        ·
          refine ⟨2024396621030284022928989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349597747353522681952659 2024396621030284022928989)
          ·
            refine ⟨759148732886356508598371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2024396621030284022928989 759148732886356508598371)
            ·
              refine ⟨1138723099329534762897557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759148732886356508598371 1138723099329534762897557)
              ·
                refine ⟨53377645281071942010823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1138723099329534762897557 53377645281071942010823)
                ·
                  rfl

theorem cell19_175420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_175420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175420 prefixEnd_175420 := by exact prefixLift 175420
  have htrace : WordTrace (prefixWord ++ tailWord_175420) baseStart_175420 baseEnd_175420 := by
    simpa [prefixWord, tailWord_175420, baseEnd_175420] using wordTrace_append hprefix tailTrace_175420
  have hstable : (prefixWord ++ tailWord_175420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175420).length < 2 ^ (prefixWord ++ tailWord_175420).sum := by decide
  have hdescent : baseEnd_175420 < baseStart_175420 := by decide
  rcases family_descends (prefixWord ++ tailWord_175420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175454 : List Nat := [4, 4, 2, 9]
def baseStart_175454 : Nat := 118140960795 + 175454 * 2 ^ 59
def prefixEnd_175454 : Nat := 4983230072969 + 3 ^ 40 * 175454 * 2
def baseEnd_175454 : Nat := 659110999572468361175

theorem tailTrace_175454 : CollatzResearch.WordTrace tailWord_175454 prefixEnd_175454 659110999572468361175 := by
  unfold tailWord_175454
  simp only [CollatzResearch.WordTrace]
  refine ⟨799916638295949750332677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4266222070911732001774277 799916638295949750332677)
  ·
    refine ⟨149984369680490578187377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 799916638295949750332677 149984369680490578187377)
    ·
      refine ⟨112488277260367933640533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149984369680490578187377 112488277260367933640533)
      ·
        refine ⟨659110999572468361175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 112488277260367933640533 659110999572468361175)
        ·
          rfl

theorem cell19_175454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 9].length) (baseStart_175454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175454 prefixEnd_175454 := by exact prefixLift 175454
  have htrace : WordTrace (prefixWord ++ tailWord_175454) baseStart_175454 baseEnd_175454 := by
    simpa [prefixWord, tailWord_175454, baseEnd_175454] using wordTrace_append hprefix tailTrace_175454
  have hstable : (prefixWord ++ tailWord_175454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175454).length < 2 ^ (prefixWord ++ tailWord_175454).sum := by decide
  have hdescent : baseEnd_175454 < baseStart_175454 := by decide
  rcases family_descends (prefixWord ++ tailWord_175454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175490 : List Nat := [3, 4, 2, 1, 1, 2, 3, 3]
def baseStart_175490 : Nat := 118140960795 + 175490 * 2 ^ 59
def prefixEnd_175490 : Nat := 4983230072969 + 3 ^ 40 * 175490 * 2
def baseEnd_175490 : Nat := 53398945219332520455077

theorem tailTrace_175490 : CollatzResearch.WordTrace tailWord_175490 prefixEnd_175490 53398945219332520455077 := by
  unfold tailWord_175490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600161533559294037742981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4267097422824784100647949 1600161533559294037742981)
  ·
    refine ⟨300030287542367632076809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1600161533559294037742981 300030287542367632076809)
    ·
      refine ⟨225022715656775724057607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300030287542367632076809 225022715656775724057607)
      ·
        refine ⟨337534073485163586086411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225022715656775724057607 337534073485163586086411)
        ·
          refine ⟨506301110227745379129617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337534073485163586086411 506301110227745379129617)
          ·
            refine ⟨379725832670809034347213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506301110227745379129617 379725832670809034347213)
            ·
              refine ⟨142397187251553387880205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379725832670809034347213 142397187251553387880205)
              ·
                refine ⟨53398945219332520455077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142397187251553387880205 53398945219332520455077)
                ·
                  rfl

theorem cell19_175490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_175490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175490 prefixEnd_175490 := by exact prefixLift 175490
  have htrace : WordTrace (prefixWord ++ tailWord_175490) baseStart_175490 baseEnd_175490 := by
    simpa [prefixWord, tailWord_175490, baseEnd_175490] using wordTrace_append hprefix tailTrace_175490
  have hstable : (prefixWord ++ tailWord_175490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175490).length < 2 ^ (prefixWord ++ tailWord_175490).sum := by decide
  have hdescent : baseEnd_175490 < baseStart_175490 := by decide
  rcases family_descends (prefixWord ++ tailWord_175490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175589 : List Nat := [1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_175589 : Nat := 118140960795 + 175589 * 2 ^ 59
def prefixEnd_175589 : Nat := 4983230072969 + 3 ^ 40 * 175589 * 2
def baseEnd_175589 : Nat := 53429069417729624254807

theorem tailTrace_175589 : CollatzResearch.WordTrace tailWord_175589 prefixEnd_175589 53429069417729624254807 := by
  unfold tailWord_175589
  simp only [CollatzResearch.WordTrace]
  refine ⟨6404256960878516058825821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4269504640585677372550547 6404256960878516058825821)
  ·
    refine ⟨2401596360329443522059683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6404256960878516058825821 2401596360329443522059683)
    ·
      refine ⟨3602394540494165283089525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2401596360329443522059683 3602394540494165283089525)
      ·
        refine ⟨337724488171327995289643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3602394540494165283089525 337724488171327995289643)
        ·
          refine ⟨506586732256991992934465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337724488171327995289643 506586732256991992934465)
          ·
            refine ⟨379940049192743994700849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506586732256991992934465 379940049192743994700849)
            ·
              refine ⟨284955036894557996025637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379940049192743994700849 284955036894557996025637)
              ·
                refine ⟨53429069417729624254807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284955036894557996025637 53429069417729624254807)
                ·
                  rfl

theorem cell19_175589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_175589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175589 prefixEnd_175589 := by exact prefixLift 175589
  have htrace : WordTrace (prefixWord ++ tailWord_175589) baseStart_175589 baseEnd_175589 := by
    simpa [prefixWord, tailWord_175589, baseEnd_175589] using wordTrace_append hprefix tailTrace_175589
  have hstable : (prefixWord ++ tailWord_175589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175589).length < 2 ^ (prefixWord ++ tailWord_175589).sum := by decide
  have hdescent : baseEnd_175589 < baseStart_175589 := by decide
  rcases family_descends (prefixWord ++ tailWord_175589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175591 : List Nat := [1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_175591 : Nat := 118140960795 + 175591 * 2 ^ 59
def prefixEnd_175591 : Nat := 4983230072969 + 3 ^ 40 * 175591 * 2
def baseEnd_175591 : Nat := 53429677987394212210357

theorem tailTrace_175591 : CollatzResearch.WordTrace tailWord_175591 prefixEnd_175591 53429677987394212210357 := by
  unfold tailWord_175591
  simp only [CollatzResearch.WordTrace]
  refine ⟨6404329906871270400398627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4269553271247513600265751 6404329906871270400398627)
  ·
    refine ⟨9606494860306905600597941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6404329906871270400398627 9606494860306905600597941)
    ·
      refine ⟨900608893153772400056057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9606494860306905600597941 900608893153772400056057)
      ·
        refine ⟨675456669865329300042043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900608893153772400056057 675456669865329300042043)
        ·
          refine ⟨1013185004797993950063065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675456669865329300042043 1013185004797993950063065)
          ·
            refine ⟨759888753598495462547299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013185004797993950063065 759888753598495462547299)
            ·
              refine ⟨1139833130397743193820949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759888753598495462547299 1139833130397743193820949)
              ·
                refine ⟨53429677987394212210357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1139833130397743193820949 53429677987394212210357)
                ·
                  rfl

theorem cell19_175591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_175591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175591 prefixEnd_175591 := by exact prefixLift 175591
  have htrace : WordTrace (prefixWord ++ tailWord_175591) baseStart_175591 baseEnd_175591 := by
    simpa [prefixWord, tailWord_175591, baseEnd_175591] using wordTrace_append hprefix tailTrace_175591
  have hstable : (prefixWord ++ tailWord_175591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175591).length < 2 ^ (prefixWord ++ tailWord_175591).sum := by decide
  have hdescent : baseEnd_175591 < baseStart_175591 := by decide
  rcases family_descends (prefixWord ++ tailWord_175591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175720 : List Nat := [2, 1, 4, 3, 1, 3, 2, 3]
def baseStart_175720 : Nat := 118140960795 + 175720 * 2 ^ 59
def prefixEnd_175720 : Nat := 4983230072969 + 3 ^ 40 * 175720 * 2
def baseEnd_175720 : Nat := 53468930730760135343339

theorem tailTrace_175720 : CollatzResearch.WordTrace tailWord_175720 prefixEnd_175720 53468930730760135343339 := by
  unfold tailWord_175720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204517461701962715922307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4272689948935950287896409 3204517461701962715922307)
  ·
    refine ⟨4806776192552944073883461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3204517461701962715922307 4806776192552944073883461)
    ·
      refine ⟨901270536103677013853149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4806776192552944073883461 901270536103677013853149)
      ·
        refine ⟨337976451038878880194931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 901270536103677013853149 337976451038878880194931)
        ·
          refine ⟨506964676558318320292397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337976451038878880194931 506964676558318320292397)
          ·
            refine ⟨190111753709369370109649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506964676558318320292397 190111753709369370109649)
            ·
              refine ⟨142583815282027027582237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190111753709369370109649 142583815282027027582237)
              ·
                refine ⟨53468930730760135343339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142583815282027027582237 53468930730760135343339)
                ·
                  rfl

theorem cell19_175720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_175720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175720 prefixEnd_175720 := by exact prefixLift 175720
  have htrace : WordTrace (prefixWord ++ tailWord_175720) baseStart_175720 baseEnd_175720 := by
    simpa [prefixWord, tailWord_175720, baseEnd_175720] using wordTrace_append hprefix tailTrace_175720
  have hstable : (prefixWord ++ tailWord_175720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175720).length < 2 ^ (prefixWord ++ tailWord_175720).sum := by decide
  have hdescent : baseEnd_175720 < baseStart_175720 := by decide
  rcases family_descends (prefixWord ++ tailWord_175720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175722 : List Nat := [3, 1, 3, 2, 1, 2, 4, 3]
def baseStart_175722 : Nat := 118140960795 + 175722 * 2 ^ 59
def prefixEnd_175722 : Nat := 4983230072969 + 3 ^ 40 * 175722 * 2
def baseEnd_175722 : Nat := 53469539300424723298889

theorem tailTrace_175722 : CollatzResearch.WordTrace tailWord_175722 prefixEnd_175722 53469539300424723298889 := by
  unfold tailWord_175722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1602276967349169943354355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4272738579597786515611613 1602276967349169943354355)
  ·
    refine ⟨2403415451023754915031533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1602276967349169943354355 2403415451023754915031533)
    ·
      refine ⟨901280794133908093136825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2403415451023754915031533 901280794133908093136825)
      ·
        refine ⟨675960595600431069852619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 901280794133908093136825 675960595600431069852619)
        ·
          refine ⟨1013940893400646604778929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675960595600431069852619 1013940893400646604778929)
          ·
            refine ⟨760455670050484953584197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013940893400646604778929 760455670050484953584197)
            ·
              refine ⟨142585438134465928797037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 760455670050484953584197 142585438134465928797037)
              ·
                refine ⟨53469539300424723298889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142585438134465928797037 53469539300424723298889)
                ·
                  rfl

theorem cell19_175722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_175722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175722 prefixEnd_175722 := by exact prefixLift 175722
  have htrace : WordTrace (prefixWord ++ tailWord_175722) baseStart_175722 baseEnd_175722 := by
    simpa [prefixWord, tailWord_175722, baseEnd_175722] using wordTrace_append hprefix tailTrace_175722
  have hstable : (prefixWord ++ tailWord_175722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175722).length < 2 ^ (prefixWord ++ tailWord_175722).sum := by decide
  have hdescent : baseEnd_175722 < baseStart_175722 := by decide
  rcases family_descends (prefixWord ++ tailWord_175722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175798 : List Nat := [5, 1, 3, 1, 1, 8]
def baseStart_175798 : Nat := 118140960795 + 175798 * 2 ^ 59
def prefixEnd_175798 : Nat := 4983230072969 + 3 ^ 40 * 175798 * 2
def baseEnd_175798 : Nat := 5943629438631007289977

theorem tailTrace_175798 : CollatzResearch.WordTrace tailWord_175798 prefixEnd_175798 5943629438631007289977 := by
  unfold tailWord_175798
  simp only [CollatzResearch.WordTrace]
  refine ⟨400742488570084047074003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4274586544747563168789365 400742488570084047074003)
  ·
    refine ⟨601113732855126070611005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400742488570084047074003 601113732855126070611005)
    ·
      refine ⟨225417649820672276479127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 601113732855126070611005 225417649820672276479127)
      ·
        refine ⟨338126474731008414718691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225417649820672276479127 338126474731008414718691)
        ·
          refine ⟨507189712096512622078037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338126474731008414718691 507189712096512622078037)
          ·
            refine ⟨5943629438631007289977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 507189712096512622078037 5943629438631007289977)
            ·
              rfl

theorem cell19_175798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_175798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175798 prefixEnd_175798 := by exact prefixLift 175798
  have htrace : WordTrace (prefixWord ++ tailWord_175798) baseStart_175798 baseEnd_175798 := by
    simpa [prefixWord, tailWord_175798, baseEnd_175798] using wordTrace_append hprefix tailTrace_175798
  have hstable : (prefixWord ++ tailWord_175798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175798).length < 2 ^ (prefixWord ++ tailWord_175798).sum := by decide
  have hdescent : baseEnd_175798 < baseStart_175798 := by decide
  rcases family_descends (prefixWord ++ tailWord_175798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175802 : List Nat := [3, 1, 1, 1, 2, 11]
def baseStart_175802 : Nat := 118140960795 + 175802 * 2 ^ 59
def prefixEnd_175802 : Nat := 4983230072969 + 3 ^ 40 * 175802 * 2
def baseEnd_175802 : Nat := 5943764676334249057877

theorem tailTrace_175802 : CollatzResearch.WordTrace tailWord_175802 prefixEnd_175802 5943764676334249057877 := by
  unfold tailWord_175802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603006427276713359082415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4274683806071235624219773 1603006427276713359082415)
  ·
    refine ⟨2404509640915070038623623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1603006427276713359082415 2404509640915070038623623)
    ·
      refine ⟨3606764461372605057935435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404509640915070038623623 3606764461372605057935435)
      ·
        refine ⟨5410146692058907586903153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3606764461372605057935435 5410146692058907586903153)
        ·
          refine ⟨4057610019044180690177365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5410146692058907586903153 4057610019044180690177365)
          ·
            refine ⟨5943764676334249057877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4057610019044180690177365 5943764676334249057877)
            ·
              rfl

theorem cell19_175802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_175802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175802 prefixEnd_175802 := by exact prefixLift 175802
  have htrace : WordTrace (prefixWord ++ tailWord_175802) baseStart_175802 baseEnd_175802 := by
    simpa [prefixWord, tailWord_175802, baseEnd_175802] using wordTrace_append hprefix tailTrace_175802
  have hstable : (prefixWord ++ tailWord_175802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175802).length < 2 ^ (prefixWord ++ tailWord_175802).sum := by decide
  have hdescent : baseEnd_175802 < baseStart_175802 := by decide
  rcases family_descends (prefixWord ++ tailWord_175802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175840 : List Nat := [2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_175840 : Nat := 118140960795 + 175840 * 2 ^ 59
def prefixEnd_175840 : Nat := 4983230072969 + 3 ^ 40 * 175840 * 2
def baseEnd_175840 : Nat := 53505444910635412676345

theorem tailTrace_175840 : CollatzResearch.WordTrace tailWord_175840 prefixEnd_175840 53505444910635412676345 := by
  unfold tailWord_175840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206705841484592963106487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4275607788646123950808649 3206705841484592963106487)
  ·
    refine ⟨4810058762226889444659731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3206705841484592963106487 4810058762226889444659731)
    ·
      refine ⟨7215088143340334166989597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4810058762226889444659731 7215088143340334166989597)
      ·
        refine ⟨2705658053752625312621099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7215088143340334166989597 2705658053752625312621099)
        ·
          refine ⟨4058487080628937968931649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705658053752625312621099 4058487080628937968931649)
          ·
            refine ⟨3043865310471703476698737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4058487080628937968931649 3043865310471703476698737)
            ·
              refine ⟨2282898982853777607524053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043865310471703476698737 2282898982853777607524053)
              ·
                refine ⟨53505444910635412676345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2282898982853777607524053 53505444910635412676345)
                ·
                  rfl

theorem cell19_175840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_175840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175840 prefixEnd_175840 := by exact prefixLift 175840
  have htrace : WordTrace (prefixWord ++ tailWord_175840) baseStart_175840 baseEnd_175840 := by
    simpa [prefixWord, tailWord_175840, baseEnd_175840] using wordTrace_append hprefix tailTrace_175840
  have hstable : (prefixWord ++ tailWord_175840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175840).length < 2 ^ (prefixWord ++ tailWord_175840).sum := by decide
  have hdescent : baseEnd_175840 < baseStart_175840 := by decide
  rcases family_descends (prefixWord ++ tailWord_175840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175885 : List Nat := [1, 7, 2, 1, 1, 2, 2, 3]
def baseStart_175885 : Nat := 118140960795 + 175885 * 2 ^ 59
def prefixEnd_175885 : Nat := 4983230072969 + 3 ^ 40 * 175885 * 2
def baseEnd_175885 : Nat := 53519137728088641676223

theorem tailTrace_175885 : CollatzResearch.WordTrace tailWord_175885 prefixEnd_175885 53519137728088641676223 := by
  unfold tailWord_175885
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415052967806158611601109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4276701978537439074400739 6415052967806158611601109)
  ·
    refine ⟨150352803932956842459401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6415052967806158611601109 150352803932956842459401)
    ·
      refine ⟨112764602949717631844551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150352803932956842459401 112764602949717631844551)
      ·
        refine ⟨169146904424576447766827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112764602949717631844551 169146904424576447766827)
        ·
          refine ⟨253720356636864671650241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169146904424576447766827 253720356636864671650241)
          ·
            refine ⟨190290267477648503737681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253720356636864671650241 190290267477648503737681)
            ·
              refine ⟨142717700608236377803261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190290267477648503737681 142717700608236377803261)
              ·
                refine ⟨53519137728088641676223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142717700608236377803261 53519137728088641676223)
                ·
                  rfl

theorem cell19_175885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_175885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175885 prefixEnd_175885 := by exact prefixLift 175885
  have htrace : WordTrace (prefixWord ++ tailWord_175885) baseStart_175885 baseEnd_175885 := by
    simpa [prefixWord, tailWord_175885, baseEnd_175885] using wordTrace_append hprefix tailTrace_175885
  have hstable : (prefixWord ++ tailWord_175885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175885).length < 2 ^ (prefixWord ++ tailWord_175885).sum := by decide
  have hdescent : baseEnd_175885 < baseStart_175885 := by decide
  rcases family_descends (prefixWord ++ tailWord_175885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175893 : List Nat := [1, 3, 2, 1, 2, 5, 2, 3]
def baseStart_175893 : Nat := 118140960795 + 175893 * 2 ^ 59
def prefixEnd_175893 : Nat := 4983230072969 + 3 ^ 40 * 175893 * 2
def baseEnd_175893 : Nat := 53521572006746993498423

theorem tailTrace_175893 : CollatzResearch.WordTrace tailWord_175893 prefixEnd_175893 53521572006746993498423 := by
  unfold tailWord_175893
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415344751777175977892333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4276896501184783985261555 6415344751777175977892333)
  ·
    refine ⟨2405754281916440991709625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6415344751777175977892333 2405754281916440991709625)
    ·
      refine ⟨1804315711437330743782219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2405754281916440991709625 1804315711437330743782219)
      ·
        refine ⟨2706473567155996115673329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804315711437330743782219 2706473567155996115673329)
        ·
          refine ⟨2029855175366997086754997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2706473567155996115673329 2029855175366997086754997)
          ·
            refine ⟨190298922690655976883281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2029855175366997086754997 190298922690655976883281)
            ·
              refine ⟨142724192017991982662461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190298922690655976883281 142724192017991982662461)
              ·
                refine ⟨53521572006746993498423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142724192017991982662461 53521572006746993498423)
                ·
                  rfl

theorem cell19_175893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_175893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175893 prefixEnd_175893 := by exact prefixLift 175893
  have htrace : WordTrace (prefixWord ++ tailWord_175893) baseStart_175893 baseEnd_175893 := by
    simpa [prefixWord, tailWord_175893, baseEnd_175893] using wordTrace_append hprefix tailTrace_175893
  have hstable : (prefixWord ++ tailWord_175893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175893).length < 2 ^ (prefixWord ++ tailWord_175893).sum := by decide
  have hdescent : baseEnd_175893 < baseStart_175893 := by decide
  rcases family_descends (prefixWord ++ tailWord_175893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175895 : List Nat := [1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_175895 : Nat := 118140960795 + 175895 * 2 ^ 59
def prefixEnd_175895 : Nat := 4983230072969 + 3 ^ 40 * 175895 * 2
def baseEnd_175895 : Nat := 53522180576411581453973

theorem tailTrace_175895 : CollatzResearch.WordTrace tailWord_175895 prefixEnd_175895 53522180576411581453973 := by
  unfold tailWord_175895
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415417697769930319465139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4276945131846620212976759 6415417697769930319465139)
  ·
    refine ⟨9623126546654895479197709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6415417697769930319465139 9623126546654895479197709)
    ·
      refine ⟨3608672454995585804699141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9623126546654895479197709 3608672454995585804699141)
      ·
        refine ⟨676626085311672338381089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3608672454995585804699141 676626085311672338381089)
        ·
          refine ⟨507469563983754253785817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676626085311672338381089 507469563983754253785817)
          ·
            refine ⟨380602172987815690339363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507469563983754253785817 380602172987815690339363)
            ·
              refine ⟨570903259481723535509045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380602172987815690339363 570903259481723535509045)
              ·
                refine ⟨53522180576411581453973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 570903259481723535509045 53522180576411581453973)
                ·
                  rfl

theorem cell19_175895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_175895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175895 prefixEnd_175895 := by exact prefixLift 175895
  have htrace : WordTrace (prefixWord ++ tailWord_175895) baseStart_175895 baseEnd_175895 := by
    simpa [prefixWord, tailWord_175895, baseEnd_175895] using wordTrace_append hprefix tailTrace_175895
  have hstable : (prefixWord ++ tailWord_175895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175895).length < 2 ^ (prefixWord ++ tailWord_175895).sum := by decide
  have hdescent : baseEnd_175895 < baseStart_175895 := by decide
  rcases family_descends (prefixWord ++ tailWord_175895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175916 : List Nat := [2, 2, 1, 1, 1, 5, 7]
def baseStart_175916 : Nat := 118140960795 + 175916 * 2 ^ 59
def prefixEnd_175916 : Nat := 4983230072969 + 3 ^ 40 * 175916 * 2
def baseEnd_175916 : Nat := 17842856852629918329083

theorem tailTrace_175916 : CollatzResearch.WordTrace tailWord_175916 prefixEnd_175916 17842856852629918329083 := by
  unfold tailWord_175916
  simp only [CollatzResearch.WordTrace]
  refine ⟨3208091815346925452989801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4277455753795900603986401 3208091815346925452989801)
  ·
    refine ⟨2406068861510194089742351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3208091815346925452989801 2406068861510194089742351)
    ·
      refine ⟨3609103292265291134613527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406068861510194089742351 3609103292265291134613527)
      ·
        refine ⟨5413654938397936701920291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609103292265291134613527 5413654938397936701920291)
        ·
          refine ⟨8120482407596905052880437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413654938397936701920291 8120482407596905052880437)
          ·
            refine ⟨761295225712209848707541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8120482407596905052880437 761295225712209848707541)
            ·
              refine ⟨17842856852629918329083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 761295225712209848707541 17842856852629918329083)
              ·
                rfl

theorem cell19_175916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_175916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175916 prefixEnd_175916 := by exact prefixLift 175916
  have htrace : WordTrace (prefixWord ++ tailWord_175916) baseStart_175916 baseEnd_175916 := by
    simpa [prefixWord, tailWord_175916, baseEnd_175916] using wordTrace_append hprefix tailTrace_175916
  have hstable : (prefixWord ++ tailWord_175916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175916).length < 2 ^ (prefixWord ++ tailWord_175916).sum := by decide
  have hdescent : baseEnd_175916 < baseStart_175916 := by decide
  rcases family_descends (prefixWord ++ tailWord_175916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175933 : List Nat := [1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_175933 : Nat := 118140960795 + 175933 * 2 ^ 59
def prefixEnd_175933 : Nat := 4983230072969 + 3 ^ 40 * 175933 * 2
def baseEnd_175933 : Nat := 53533743400038752609425

theorem tailTrace_175933 : CollatzResearch.WordTrace tailWord_175933 prefixEnd_175933 53533743400038752609425 := by
  unfold tailWord_175933
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416803671632262809348453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4277869114421508539565635 6416803671632262809348453)
  ·
    refine ⟨1203150688431049276752835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6416803671632262809348453 1203150688431049276752835)
    ·
      refine ⟨1804726032646573915129253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203150688431049276752835 1804726032646573915129253)
      ·
        refine ⟨338386131121232609086735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1804726032646573915129253 338386131121232609086735)
        ·
          refine ⟨507579196681848913630103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338386131121232609086735 507579196681848913630103)
          ·
            refine ⟨761368795022773370445155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507579196681848913630103 761368795022773370445155)
            ·
              refine ⟨1142053192534160055667733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761368795022773370445155 1142053192534160055667733)
              ·
                refine ⟨53533743400038752609425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1142053192534160055667733 53533743400038752609425)
                ·
                  rfl

theorem cell19_175933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_175933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175933 prefixEnd_175933 := by exact prefixLift 175933
  have htrace : WordTrace (prefixWord ++ tailWord_175933) baseStart_175933 baseEnd_175933 := by
    simpa [prefixWord, tailWord_175933, baseEnd_175933] using wordTrace_append hprefix tailTrace_175933
  have hstable : (prefixWord ++ tailWord_175933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175933).length < 2 ^ (prefixWord ++ tailWord_175933).sum := by decide
  have hdescent : baseEnd_175933 < baseStart_175933 := by decide
  rcases family_descends (prefixWord ++ tailWord_175933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175971 : List Nat := [1, 1, 1, 5, 5, 6]
def baseStart_175971 : Nat := 118140960795 + 175971 * 2 ^ 59
def prefixEnd_175971 : Nat := 4983230072969 + 3 ^ 40 * 175971 * 2
def baseEnd_175971 : Nat := 5949478469296213751653

theorem tailTrace_175971 : CollatzResearch.WordTrace tailWord_175971 prefixEnd_175971 5949478469296213751653 := by
  unfold tailWord_175971
  simp only [CollatzResearch.WordTrace]
  refine ⟨6418189645494595299231767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4278793096996396866154511 6418189645494595299231767)
  ·
    refine ⟨9627284468241892948847651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6418189645494595299231767 9627284468241892948847651)
    ·
      refine ⟨14440926702362839423271477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9627284468241892948847651 14440926702362839423271477)
      ·
        refine ⟨1353836878346516195931701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14440926702362839423271477 1353836878346516195931701)
        ·
          refine ⟨126922207344985893368597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1353836878346516195931701 126922207344985893368597)
          ·
            refine ⟨5949478469296213751653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126922207344985893368597 5949478469296213751653)
            ·
              rfl

theorem cell19_175971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 6].length) (baseStart_175971 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_175971 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_175971 prefixEnd_175971 := by exact prefixLift 175971
  have htrace : WordTrace (prefixWord ++ tailWord_175971) baseStart_175971 baseEnd_175971 := by
    simpa [prefixWord, tailWord_175971, baseEnd_175971] using wordTrace_append hprefix tailTrace_175971
  have hstable : (prefixWord ++ tailWord_175971).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175971).length < 2 ^ (prefixWord ++ tailWord_175971).sum := by decide
  have hdescent : baseEnd_175971 < baseStart_175971 := by decide
  rcases family_descends (prefixWord ++ tailWord_175971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176007 : List Nat := [1, 1, 4, 2, 4, 1, 3, 3]
def baseStart_176007 : Nat := 118140960795 + 176007 * 2 ^ 59
def prefixEnd_176007 : Nat := 4983230072969 + 3 ^ 40 * 176007 * 2
def baseEnd_176007 : Nat := 53556260477628506964779

theorem tailTrace_176007 : CollatzResearch.WordTrace tailWord_176007 prefixEnd_176007 53556260477628506964779 := by
  unfold tailWord_176007
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419502673364173447542275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4279668448909448965028183 6419502673364173447542275)
  ·
    refine ⟨9629254010046260171313413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6419502673364173447542275 9629254010046260171313413)
    ·
      refine ⟨1805485126883673782121265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9629254010046260171313413 1805485126883673782121265)
      ·
        refine ⟨1354113845162755336590949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1805485126883673782121265 1354113845162755336590949)
        ·
          refine ⟨253896345968016625610803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1354113845162755336590949 253896345968016625610803)
          ·
            refine ⟨380844518952024938416205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253896345968016625610803 380844518952024938416205)
            ·
              refine ⟨142816694607009351906077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380844518952024938416205 142816694607009351906077)
              ·
                refine ⟨53556260477628506964779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142816694607009351906077 53556260477628506964779)
                ·
                  rfl

theorem cell19_176007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_176007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176007 prefixEnd_176007 := by exact prefixLift 176007
  have htrace : WordTrace (prefixWord ++ tailWord_176007) baseStart_176007 baseEnd_176007 := by
    simpa [prefixWord, tailWord_176007, baseEnd_176007] using wordTrace_append hprefix tailTrace_176007
  have hstable : (prefixWord ++ tailWord_176007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176007).length < 2 ^ (prefixWord ++ tailWord_176007).sum := by decide
  have hdescent : baseEnd_176007 < baseStart_176007 := by decide
  rcases family_descends (prefixWord ++ tailWord_176007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176009 : List Nat := [1, 2, 1, 1, 5, 1, 5, 3]
def baseStart_176009 : Nat := 118140960795 + 176009 * 2 ^ 59
def prefixEnd_176009 : Nat := 4983230072969 + 3 ^ 40 * 176009 * 2
def baseEnd_176009 : Nat := 53556869047293094920329

theorem tailTrace_176009 : CollatzResearch.WordTrace tailWord_176009 prefixEnd_176009 53556869047293094920329 := by
  unfold tailWord_176009
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419575619356927789115081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4279717079571285192743387 6419575619356927789115081)
  ·
    refine ⟨4814681714517695841836311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6419575619356927789115081 4814681714517695841836311)
    ·
      refine ⟨7222022571776543762754467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4814681714517695841836311 7222022571776543762754467)
      ·
        refine ⟨10833033857664815644131701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222022571776543762754467 10833033857664815644131701)
        ·
          refine ⟨1015596924156076466637347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10833033857664815644131701 1015596924156076466637347)
          ·
            refine ⟨1523395386234114699956021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015596924156076466637347 1523395386234114699956021)
            ·
              refine ⟨142818317459448253120877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1523395386234114699956021 142818317459448253120877)
              ·
                refine ⟨53556869047293094920329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142818317459448253120877 53556869047293094920329)
                ·
                  rfl

theorem cell19_176009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_176009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176009 prefixEnd_176009 := by exact prefixLift 176009
  have htrace : WordTrace (prefixWord ++ tailWord_176009) baseStart_176009 baseEnd_176009 := by
    simpa [prefixWord, tailWord_176009, baseEnd_176009] using wordTrace_append hprefix tailTrace_176009
  have hstable : (prefixWord ++ tailWord_176009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176009).length < 2 ^ (prefixWord ++ tailWord_176009).sum := by decide
  have hdescent : baseEnd_176009 < baseStart_176009 := by decide
  rcases family_descends (prefixWord ++ tailWord_176009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176028 : List Nat := [2, 2, 3, 3, 1, 2, 6]
def baseStart_176028 : Nat := 118140960795 + 176028 * 2 ^ 59
def prefixEnd_176028 : Nat := 4983230072969 + 3 ^ 40 * 176028 * 2
def baseEnd_176028 : Nat := 17854216819702226832685

theorem tailTrace_176028 : CollatzResearch.WordTrace tailWord_176028 prefixEnd_176028 17854216819702226832685 := by
  unfold tailWord_176028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210134303144047017028369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4280179070858729356037825 3210134303144047017028369)
  ·
    refine ⟨2407600727358035262771277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3210134303144047017028369 2407600727358035262771277)
    ·
      refine ⟨902850272759263223539229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2407600727358035262771277 902850272759263223539229)
      ·
        refine ⟨338568852284723708827211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 902850272759263223539229 338568852284723708827211)
        ·
          refine ⟨507853278427085563240817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338568852284723708827211 507853278427085563240817)
          ·
            refine ⟨380889958820314172430613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507853278427085563240817 380889958820314172430613)
            ·
              refine ⟨17854216819702226832685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 380889958820314172430613 17854216819702226832685)
              ·
                rfl

theorem cell19_176028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_176028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176028 prefixEnd_176028 := by exact prefixLift 176028
  have htrace : WordTrace (prefixWord ++ tailWord_176028) baseStart_176028 baseEnd_176028 := by
    simpa [prefixWord, tailWord_176028, baseEnd_176028] using wordTrace_append hprefix tailTrace_176028
  have hstable : (prefixWord ++ tailWord_176028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176028).length < 2 ^ (prefixWord ++ tailWord_176028).sum := by decide
  have hdescent : baseEnd_176028 < baseStart_176028 := by decide
  rcases family_descends (prefixWord ++ tailWord_176028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176060 : List Nat := [2, 2, 2, 5, 2, 1, 2, 3]
def baseStart_176060 : Nat := 118140960795 + 176060 * 2 ^ 59
def prefixEnd_176060 : Nat := 4983230072969 + 3 ^ 40 * 176060 * 2
def baseEnd_176060 : Nat := 53572387573740087786857

theorem tailTrace_176060 : CollatzResearch.WordTrace tailWord_176060 prefixEnd_176060 53572387573740087786857 := by
  unfold tailWord_176060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210717871086081749610817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4280957161448108999481089 3210717871086081749610817)
  ·
    refine ⟨2408038403314561312208113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3210717871086081749610817 2408038403314561312208113)
    ·
      refine ⟨1806028802485920984156085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408038403314561312208113 1806028802485920984156085)
      ·
        refine ⟨169315200233055092264633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1806028802485920984156085 169315200233055092264633)
        ·
          refine ⟨126986400174791319198475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169315200233055092264633 126986400174791319198475)
          ·
            refine ⟨190479600262186978797713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126986400174791319198475 190479600262186978797713)
            ·
              refine ⟨142859700196640234098285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190479600262186978797713 142859700196640234098285)
              ·
                refine ⟨53572387573740087786857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142859700196640234098285 53572387573740087786857)
                ·
                  rfl

theorem cell19_176060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_176060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176060 prefixEnd_176060 := by exact prefixLift 176060
  have htrace : WordTrace (prefixWord ++ tailWord_176060) baseStart_176060 baseEnd_176060 := by
    simpa [prefixWord, tailWord_176060, baseEnd_176060] using wordTrace_append hprefix tailTrace_176060
  have hstable : (prefixWord ++ tailWord_176060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176060).length < 2 ^ (prefixWord ++ tailWord_176060).sum := by decide
  have hdescent : baseEnd_176060 < baseStart_176060 := by decide
  rcases family_descends (prefixWord ++ tailWord_176060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176085 : List Nat := [1, 3, 2, 3, 2, 3, 5]
def baseStart_176085 : Nat := 118140960795 + 176085 * 2 ^ 59
def prefixEnd_176085 : Nat := 4983230072969 + 3 ^ 40 * 176085 * 2
def baseEnd_176085 : Nat := 17859998231515812410411

theorem tailTrace_176085 : CollatzResearch.WordTrace tailWord_176085 prefixEnd_176085 17859998231515812410411 := by
  unfold tailWord_176085
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422347567081592768881709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4281565044721061845921139 6422347567081592768881709)
  ·
    refine ⟨2408380337655597288330641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6422347567081592768881709 2408380337655597288330641)
    ·
      refine ⟨1806285253241697966247981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408380337655597288330641 1806285253241697966247981)
      ·
        refine ⟨677356969965636737342993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1806285253241697966247981 677356969965636737342993)
        ·
          refine ⟨508017727474227553007245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677356969965636737342993 508017727474227553007245)
          ·
            refine ⟨190506647802835332377717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 508017727474227553007245 190506647802835332377717)
            ·
              refine ⟨17859998231515812410411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190506647802835332377717 17859998231515812410411)
              ·
                rfl

theorem cell19_176085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_176085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176085 prefixEnd_176085 := by exact prefixLift 176085
  have htrace : WordTrace (prefixWord ++ tailWord_176085) baseStart_176085 baseEnd_176085 := by
    simpa [prefixWord, tailWord_176085, baseEnd_176085] using wordTrace_append hprefix tailTrace_176085
  have hstable : (prefixWord ++ tailWord_176085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176085).length < 2 ^ (prefixWord ++ tailWord_176085).sum := by decide
  have hdescent : baseEnd_176085 < baseStart_176085 := by decide
  rcases family_descends (prefixWord ++ tailWord_176085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176125 : List Nat := [1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_176125 : Nat := 118140960795 + 176125 * 2 ^ 59
def prefixEnd_176125 : Nat := 4983230072969 + 3 ^ 40 * 176125 * 2
def baseEnd_176125 : Nat := 53592166087839196342235

theorem tailTrace_176125 : CollatzResearch.WordTrace tailWord_176125 prefixEnd_176125 53592166087839196342235 := by
  unfold tailWord_176125
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423806486936679600337829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4282537657957786400225219 6423806486936679600337829)
  ·
    refine ⟨1204463716300627425063343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6423806486936679600337829 1204463716300627425063343)
    ·
      refine ⟨1806695574450941137595015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1204463716300627425063343 1806695574450941137595015)
      ·
        refine ⟨2710043361676411706392523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806695574450941137595015 2710043361676411706392523)
        ·
          refine ⟨4065065042514617559588785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710043361676411706392523 4065065042514617559588785)
          ·
            refine ⟨3048798781885963169691589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4065065042514617559588785 3048798781885963169691589)
            ·
              refine ⟨571649771603618094317173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3048798781885963169691589 571649771603618094317173)
              ·
                refine ⟨53592166087839196342235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 571649771603618094317173 53592166087839196342235)
                ·
                  rfl

theorem cell19_176125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_176125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176125 prefixEnd_176125 := by exact prefixLift 176125
  have htrace : WordTrace (prefixWord ++ tailWord_176125) baseStart_176125 baseEnd_176125 := by
    simpa [prefixWord, tailWord_176125, baseEnd_176125] using wordTrace_append hprefix tailTrace_176125
  have hstable : (prefixWord ++ tailWord_176125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176125).length < 2 ^ (prefixWord ++ tailWord_176125).sum := by decide
  have hdescent : baseEnd_176125 < baseStart_176125 := by decide
  rcases family_descends (prefixWord ++ tailWord_176125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176239 : List Nat := [1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_176239 : Nat := 118140960795 + 176239 * 2 ^ 59
def prefixEnd_176239 : Nat := 4983230072969 + 3 ^ 40 * 176239 * 2
def baseEnd_176239 : Nat := 53626854558720709808591

theorem tailTrace_176239 : CollatzResearch.WordTrace tailWord_176239 prefixEnd_176239 53626854558720709808591 := by
  unfold tailWord_176239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6427964408523677069987771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4285309605682451379991847 6427964408523677069987771)
  ·
    refine ⟨9641946612785515604981657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6427964408523677069987771 9641946612785515604981657)
    ·
      refine ⟨7231459959589136703736243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9641946612785515604981657 7231459959589136703736243)
      ·
        refine ⟨10847189939383705055604365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7231459959589136703736243 10847189939383705055604365)
        ·
          refine ⟨4067696227268889395851637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10847189939383705055604365 4067696227268889395851637)
          ·
            refine ⟨381346521306458380861091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4067696227268889395851637 381346521306458380861091)
            ·
              refine ⟨572019781959687571291637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381346521306458380861091 572019781959687571291637)
              ·
                refine ⟨53626854558720709808591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 572019781959687571291637 53626854558720709808591)
                ·
                  rfl

theorem cell19_176239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_176239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176239 prefixEnd_176239 := by exact prefixLift 176239
  have htrace : WordTrace (prefixWord ++ tailWord_176239) baseStart_176239 baseEnd_176239 := by
    simpa [prefixWord, tailWord_176239, baseEnd_176239] using wordTrace_append hprefix tailTrace_176239
  have hstable : (prefixWord ++ tailWord_176239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176239).length < 2 ^ (prefixWord ++ tailWord_176239).sum := by decide
  have hdescent : baseEnd_176239 < baseStart_176239 := by decide
  rcases family_descends (prefixWord ++ tailWord_176239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176277 : List Nat := [1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_176277 : Nat := 118140960795 + 176277 * 2 ^ 59
def prefixEnd_176277 : Nat := 4983230072969 + 3 ^ 40 * 176277 * 2
def baseEnd_176277 : Nat := 53638417382347880964043

theorem tailTrace_176277 : CollatzResearch.WordTrace tailWord_176277 prefixEnd_176277 53638417382347880964043 := by
  unfold tailWord_176277
  simp only [CollatzResearch.WordTrace]
  refine ⟨6429350382386009559871085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4286233588257339706580723 6429350382386009559871085)
  ·
    refine ⟨2411006393394753584951657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6429350382386009559871085 2411006393394753584951657)
    ·
      refine ⟨1808254795046065188713743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2411006393394753584951657 1808254795046065188713743)
      ·
        refine ⟨2712382192569097783070615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808254795046065188713743 2712382192569097783070615)
        ·
          refine ⟨4068573288853646674605923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712382192569097783070615 4068573288853646674605923)
          ·
            refine ⟨6102859933280470011908885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068573288853646674605923 6102859933280470011908885)
            ·
              refine ⟨286071559372522031808229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6102859933280470011908885 286071559372522031808229)
              ·
                refine ⟨53638417382347880964043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286071559372522031808229 53638417382347880964043)
                ·
                  rfl

theorem cell19_176277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_176277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176277 prefixEnd_176277 := by exact prefixLift 176277
  have htrace : WordTrace (prefixWord ++ tailWord_176277) baseStart_176277 baseEnd_176277 := by
    simpa [prefixWord, tailWord_176277, baseEnd_176277] using wordTrace_append hprefix tailTrace_176277
  have hstable : (prefixWord ++ tailWord_176277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176277).length < 2 ^ (prefixWord ++ tailWord_176277).sum := by decide
  have hdescent : baseEnd_176277 < baseStart_176277 := by decide
  rcases family_descends (prefixWord ++ tailWord_176277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176349 : List Nat := [1, 4, 3, 2, 1, 2, 3, 3]
def baseStart_176349 : Nat := 118140960795 + 176349 * 2 ^ 59
def prefixEnd_176349 : Nat := 4983230072969 + 3 ^ 40 * 176349 * 2
def baseEnd_176349 : Nat := 53660325890273047363847

theorem tailTrace_176349 : CollatzResearch.WordTrace tailWord_176349 prefixEnd_176349 53660325890273047363847 := by
  unfold tailWord_176349
  simp only [CollatzResearch.WordTrace]
  refine ⟨6431976438125165856492101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4287984292083443904328067 6431976438125165856492101)
  ·
    refine ⟨1205995582148468598092269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6431976438125165856492101 1205995582148468598092269)
    ·
      refine ⟨452248343305675724284601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1205995582148468598092269 452248343305675724284601)
      ·
        refine ⟨339186257479256793213451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452248343305675724284601 339186257479256793213451)
        ·
          refine ⟨508779386218885189820177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339186257479256793213451 508779386218885189820177)
          ·
            refine ⟨381584539664163892365133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508779386218885189820177 381584539664163892365133)
            ·
              refine ⟨143094202374061459636925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381584539664163892365133 143094202374061459636925)
              ·
                refine ⟨53660325890273047363847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143094202374061459636925 53660325890273047363847)
                ·
                  rfl

theorem cell19_176349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_176349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176349 prefixEnd_176349 := by exact prefixLift 176349
  have htrace : WordTrace (prefixWord ++ tailWord_176349) baseStart_176349 baseEnd_176349 := by
    simpa [prefixWord, tailWord_176349, baseEnd_176349] using wordTrace_append hprefix tailTrace_176349
  have hstable : (prefixWord ++ tailWord_176349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176349).length < 2 ^ (prefixWord ++ tailWord_176349).sum := by decide
  have hdescent : baseEnd_176349 < baseStart_176349 := by decide
  rcases family_descends (prefixWord ++ tailWord_176349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176423 : List Nat := [1, 1, 8, 1, 1, 2, 5]
def baseStart_176423 : Nat := 118140960795 + 176423 * 2 ^ 59
def prefixEnd_176423 : Nat := 4983230072969 + 3 ^ 40 * 176423 * 2
def baseEnd_176423 : Nat := 17894280989287600573067

theorem tailTrace_176423 : CollatzResearch.WordTrace tailWord_176423 prefixEnd_176423 17894280989287600573067 := by
  unfold tailWord_176423
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434675439857076494685923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4289783626571384329790615 6434675439857076494685923)
  ·
    refine ⟨9652013159785614742028885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434675439857076494685923 9652013159785614742028885)
    ·
      refine ⟨113109529216237672758151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 9652013159785614742028885 113109529216237672758151)
      ·
        refine ⟨169664293824356509137227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113109529216237672758151 169664293824356509137227)
        ·
          refine ⟨254496440736534763705841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169664293824356509137227 254496440736534763705841)
          ·
            refine ⟨190872330552401072779381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254496440736534763705841 190872330552401072779381)
            ·
              refine ⟨17894280989287600573067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190872330552401072779381 17894280989287600573067)
              ·
                rfl

theorem cell19_176423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_176423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176423 prefixEnd_176423 := by exact prefixLift 176423
  have htrace : WordTrace (prefixWord ++ tailWord_176423) baseStart_176423 baseEnd_176423 := by
    simpa [prefixWord, tailWord_176423, baseEnd_176423] using wordTrace_append hprefix tailTrace_176423
  have hstable : (prefixWord ++ tailWord_176423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176423).length < 2 ^ (prefixWord ++ tailWord_176423).sum := by decide
  have hdescent : baseEnd_176423 < baseStart_176423 := by decide
  rcases family_descends (prefixWord ++ tailWord_176423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176431 : List Nat := [1, 1, 2, 1, 2, 1, 11]
def baseStart_176431 : Nat := 118140960795 + 176431 * 2 ^ 59
def prefixEnd_176431 : Nat := 4983230072969 + 3 ^ 40 * 176431 * 2
def baseEnd_176431 : Nat := 17895092415507051180467

theorem tailTrace_176431 : CollatzResearch.WordTrace tailWord_176431 prefixEnd_176431 17895092415507051180467 := by
  unfold tailWord_176431
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434967223828093860977147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4289978149218729240651431 6434967223828093860977147)
  ·
    refine ⟨9652450835742140791465721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434967223828093860977147 9652450835742140791465721)
    ·
      refine ⟨7239338126806605593599291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9652450835742140791465721 7239338126806605593599291)
      ·
        refine ⟨10859007190209908390398937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7239338126806605593599291 10859007190209908390398937)
        ·
          refine ⟨8144255392657431292799203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10859007190209908390398937 8144255392657431292799203)
          ·
            refine ⟨12216383088986146939198805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144255392657431292799203 12216383088986146939198805)
            ·
              refine ⟨17895092415507051180467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12216383088986146939198805 17895092415507051180467)
              ·
                rfl

theorem cell19_176431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_176431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176431 prefixEnd_176431 := by exact prefixLift 176431
  have htrace : WordTrace (prefixWord ++ tailWord_176431) baseStart_176431 baseEnd_176431 := by
    simpa [prefixWord, tailWord_176431, baseEnd_176431] using wordTrace_append hprefix tailTrace_176431
  have hstable : (prefixWord ++ tailWord_176431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176431).length < 2 ^ (prefixWord ++ tailWord_176431).sum := by decide
  have hdescent : baseEnd_176431 < baseStart_176431 := by decide
  rcases family_descends (prefixWord ++ tailWord_176431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176446 : List Nat := [4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_176446 : Nat := 118140960795 + 176446 * 2 ^ 59
def prefixEnd_176446 : Nat := 4983230072969 + 3 ^ 40 * 176446 * 2
def baseEnd_176446 : Nat := 53689841519005563208027

theorem tailTrace_176446 : CollatzResearch.WordTrace tailWord_176446 prefixEnd_176446 53689841519005563208027 := by
  unfold tailWord_176446
  simp only [CollatzResearch.WordTrace]
  refine ⟨804439289846718927846649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4290342879182500948515461 804439289846718927846649)
  ·
    refine ⟨603329467385039195884987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 804439289846718927846649 603329467385039195884987)
    ·
      refine ⟨904994201077558793827481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603329467385039195884987 904994201077558793827481)
      ·
        refine ⟨678745650808169095370611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 904994201077558793827481 678745650808169095370611)
        ·
          refine ⟨1018118476212253643055917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678745650808169095370611 1018118476212253643055917)
          ·
            refine ⟨381794428579595116145969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1018118476212253643055917 381794428579595116145969)
            ·
              refine ⟨286345821434696337109477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381794428579595116145969 286345821434696337109477)
              ·
                refine ⟨53689841519005563208027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286345821434696337109477 53689841519005563208027)
                ·
                  rfl

theorem cell19_176446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_176446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176446 prefixEnd_176446 := by exact prefixLift 176446
  have htrace : WordTrace (prefixWord ++ tailWord_176446) baseStart_176446 baseEnd_176446 := by
    simpa [prefixWord, tailWord_176446, baseEnd_176446] using wordTrace_append hprefix tailTrace_176446
  have hstable : (prefixWord ++ tailWord_176446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176446).length < 2 ^ (prefixWord ++ tailWord_176446).sum := by decide
  have hdescent : baseEnd_176446 < baseStart_176446 := by decide
  rcases family_descends (prefixWord ++ tailWord_176446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176478 : List Nat := [4, 4, 2, 1, 2, 6]
def baseStart_176478 : Nat := 118140960795 + 176478 * 2 ^ 59
def prefixEnd_176478 : Nat := 4983230072969 + 3 ^ 40 * 176478 * 2
def baseEnd_176478 : Nat := 5966619848182107832981

theorem tailTrace_176478 : CollatzResearch.WordTrace tailWord_176478 prefixEnd_176478 5966619848182107832981 := by
  unfold tailWord_176478
  simp only [CollatzResearch.WordTrace]
  refine ⟨804585181832227610992261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4291120969771880591958725 804585181832227610992261)
  ·
    refine ⟨150859721593542677061049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 804585181832227610992261 150859721593542677061049)
    ·
      refine ⟨113144791195157007795787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150859721593542677061049 113144791195157007795787)
      ·
        refine ⟨169717186792735511693681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113144791195157007795787 169717186792735511693681)
        ·
          refine ⟨127287890094551633770261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169717186792735511693681 127287890094551633770261)
          ·
            refine ⟨5966619848182107832981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127287890094551633770261 5966619848182107832981)
            ·
              rfl

theorem cell19_176478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 6].length) (baseStart_176478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176478 prefixEnd_176478 := by exact prefixLift 176478
  have htrace : WordTrace (prefixWord ++ tailWord_176478) baseStart_176478 baseEnd_176478 := by
    simpa [prefixWord, tailWord_176478, baseEnd_176478] using wordTrace_append hprefix tailTrace_176478
  have hstable : (prefixWord ++ tailWord_176478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176478).length < 2 ^ (prefixWord ++ tailWord_176478).sum := by decide
  have hdescent : baseEnd_176478 < baseStart_176478 := by decide
  rcases family_descends (prefixWord ++ tailWord_176478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176672 : List Nat := [2, 1, 1, 6, 3, 1, 1, 4]
def baseStart_176672 : Nat := 118140960795 + 176672 * 2 ^ 59
def prefixEnd_176672 : Nat := 4983230072969 + 3 ^ 40 * 176672 * 2
def baseEnd_176672 : Nat := 53758609891104002185189

theorem tailTrace_176672 : CollatzResearch.WordTrace tailWord_176672 prefixEnd_176672 53758609891104002185189 := by
  unfold tailWord_176672
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221878607977496010250135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4295838143969994680333513 3221878607977496010250135)
  ·
    refine ⟨4832817911966244015375203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221878607977496010250135 4832817911966244015375203)
    ·
      refine ⟨7249226867949366023062805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832817911966244015375203 7249226867949366023062805)
      ·
        refine ⟨339807509435126532331069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7249226867949366023062805 339807509435126532331069)
        ·
          refine ⟨127427816038172449624151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339807509435126532331069 127427816038172449624151)
          ·
            refine ⟨191141724057258674436227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127427816038172449624151 191141724057258674436227)
            ·
              refine ⟨286712586085888011654341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191141724057258674436227 286712586085888011654341)
              ·
                refine ⟨53758609891104002185189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286712586085888011654341 53758609891104002185189)
                ·
                  rfl

theorem cell19_176672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_176672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176672 prefixEnd_176672 := by exact prefixLift 176672
  have htrace : WordTrace (prefixWord ++ tailWord_176672) baseStart_176672 baseEnd_176672 := by
    simpa [prefixWord, tailWord_176672, baseEnd_176672] using wordTrace_append hprefix tailTrace_176672
  have hstable : (prefixWord ++ tailWord_176672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176672).length < 2 ^ (prefixWord ++ tailWord_176672).sum := by decide
  have hdescent : baseEnd_176672 < baseStart_176672 := by decide
  rcases family_descends (prefixWord ++ tailWord_176672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176695 : List Nat := [1, 1, 3, 1, 2, 3, 5, 3]
def baseStart_176695 : Nat := 118140960795 + 176695 * 2 ^ 59
def prefixEnd_176695 : Nat := 4983230072969 + 3 ^ 40 * 176695 * 2
def baseEnd_176695 : Nat := 53765608442246763674015

theorem tailTrace_176695 : CollatzResearch.WordTrace tailWord_176695 prefixEnd_176695 53765608442246763674015 := by
  unfold tailWord_176695
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444596094871666948587539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4296397396581111299058359 6444596094871666948587539)
  ·
    refine ⟨9666894142307500422881309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6444596094871666948587539 9666894142307500422881309)
    ·
      refine ⟨3625085303365312658580491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9666894142307500422881309 3625085303365312658580491)
      ·
        refine ⟨5437627955047968987870737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625085303365312658580491 5437627955047968987870737)
        ·
          refine ⟨4078220966285976740903053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5437627955047968987870737 4078220966285976740903053)
          ·
            refine ⟨1529332862357241277838645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4078220966285976740903053 1529332862357241277838645)
            ·
              refine ⟨143374955845991369797373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1529332862357241277838645 143374955845991369797373)
              ·
                refine ⟨53765608442246763674015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143374955845991369797373 53765608442246763674015)
                ·
                  rfl

theorem cell19_176695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_176695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176695 prefixEnd_176695 := by exact prefixLift 176695
  have htrace : WordTrace (prefixWord ++ tailWord_176695) baseStart_176695 baseEnd_176695 := by
    simpa [prefixWord, tailWord_176695, baseEnd_176695] using wordTrace_append hprefix tailTrace_176695
  have hstable : (prefixWord ++ tailWord_176695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176695).length < 2 ^ (prefixWord ++ tailWord_176695).sum := by decide
  have hdescent : baseEnd_176695 < baseStart_176695 := by decide
  rcases family_descends (prefixWord ++ tailWord_176695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176716 : List Nat := [2, 2, 1, 3, 1, 2, 8]
def baseStart_176716 : Nat := 118140960795 + 176716 * 2 ^ 59
def prefixEnd_176716 : Nat := 4983230072969 + 3 ^ 40 * 176716 * 2
def baseEnd_176716 : Nat := 17923999474574979069097

theorem tailTrace_176716 : CollatzResearch.WordTrace tailWord_176716 prefixEnd_176716 17923999474574979069097 := by
  unfold tailWord_176716
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222681013897793767551001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4296908018530391690068001 3222681013897793767551001)
  ·
    refine ⟨2417010760423345325663251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3222681013897793767551001 2417010760423345325663251)
    ·
      refine ⟨3625516140635017988494877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417010760423345325663251 3625516140635017988494877)
      ·
        refine ⟨1359568552738131745685579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3625516140635017988494877 1359568552738131745685579)
        ·
          refine ⟨2039352829107197618528369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359568552738131745685579 2039352829107197618528369)
          ·
            refine ⟨1529514621830398213896277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2039352829107197618528369 1529514621830398213896277)
            ·
              refine ⟨17923999474574979069097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1529514621830398213896277 17923999474574979069097)
              ·
                rfl

theorem cell19_176716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_176716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176716 prefixEnd_176716 := by exact prefixLift 176716
  have htrace : WordTrace (prefixWord ++ tailWord_176716) baseStart_176716 baseEnd_176716 := by
    simpa [prefixWord, tailWord_176716, baseEnd_176716] using wordTrace_append hprefix tailTrace_176716
  have hstable : (prefixWord ++ tailWord_176716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176716).length < 2 ^ (prefixWord ++ tailWord_176716).sum := by decide
  have hdescent : baseEnd_176716 < baseStart_176716 := by decide
  rcases family_descends (prefixWord ++ tailWord_176716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176750 : List Nat := [4, 1, 2, 2, 2, 1, 4, 3]
def baseStart_176750 : Nat := 118140960795 + 176750 * 2 ^ 59
def prefixEnd_176750 : Nat := 4983230072969 + 3 ^ 40 * 176750 * 2
def baseEnd_176750 : Nat := 53782344108022932451643

theorem tailTrace_176750 : CollatzResearch.WordTrace tailWord_176750 prefixEnd_176750 53782344108022932451643 := by
  unfold tailWord_176750
  simp only [CollatzResearch.WordTrace]
  refine ⟨805825263709051417729963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4297734739781607561226469 805825263709051417729963)
  ·
    refine ⟨1208737895563577126594945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 805825263709051417729963 1208737895563577126594945)
    ·
      refine ⟨906553421672682844946209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1208737895563577126594945 906553421672682844946209)
      ·
        refine ⟨679915066254512133709657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 906553421672682844946209 679915066254512133709657)
        ·
          refine ⟨509936299690884100282243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 679915066254512133709657 509936299690884100282243)
          ·
            refine ⟨764904449536326150423365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509936299690884100282243 764904449536326150423365)
            ·
              refine ⟨143419584288061153204381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 764904449536326150423365 143419584288061153204381)
              ·
                refine ⟨53782344108022932451643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143419584288061153204381 53782344108022932451643)
                ·
                  rfl

theorem cell19_176750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_176750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176750 prefixEnd_176750 := by exact prefixLift 176750
  have htrace : WordTrace (prefixWord ++ tailWord_176750) baseStart_176750 baseEnd_176750 := by
    simpa [prefixWord, tailWord_176750, baseEnd_176750] using wordTrace_append hprefix tailTrace_176750
  have hstable : (prefixWord ++ tailWord_176750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176750).length < 2 ^ (prefixWord ++ tailWord_176750).sum := by decide
  have hdescent : baseEnd_176750 < baseStart_176750 := by decide
  rcases family_descends (prefixWord ++ tailWord_176750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176752 : List Nat := [2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_176752 : Nat := 118140960795 + 176752 * 2 ^ 59
def prefixEnd_176752 : Nat := 4983230072969 + 3 ^ 40 * 176752 * 2
def baseEnd_176752 : Nat := 53782952677687520407193

theorem tailTrace_176752 : CollatzResearch.WordTrace tailWord_176752 prefixEnd_176752 53782952677687520407193 := by
  unfold tailWord_176752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223337527832582841706255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4297783370443443788941673 3223337527832582841706255)
  ·
    refine ⟨4835006291748874262559383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223337527832582841706255 4835006291748874262559383)
    ·
      refine ⟨7252509437623311393839075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835006291748874262559383 7252509437623311393839075)
      ·
        refine ⟨10878764156434967090758613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7252509437623311393839075 10878764156434967090758613)
        ·
          refine ⟨254971034916444541189655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10878764156434967090758613 254971034916444541189655)
          ·
            refine ⟨382456552374666811784483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254971034916444541189655 382456552374666811784483)
            ·
              refine ⟨573684828562000217676725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382456552374666811784483 573684828562000217676725)
              ·
                refine ⟨53782952677687520407193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 573684828562000217676725 53782952677687520407193)
                ·
                  rfl

theorem cell19_176752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_176752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176752 prefixEnd_176752 := by exact prefixLift 176752
  have htrace : WordTrace (prefixWord ++ tailWord_176752) baseStart_176752 baseEnd_176752 := by
    simpa [prefixWord, tailWord_176752, baseEnd_176752] using wordTrace_append hprefix tailTrace_176752
  have hstable : (prefixWord ++ tailWord_176752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176752).length < 2 ^ (prefixWord ++ tailWord_176752).sum := by decide
  have hdescent : baseEnd_176752 < baseStart_176752 := by decide
  rcases family_descends (prefixWord ++ tailWord_176752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176773 : List Nat := [1, 3, 1, 1, 4, 2, 7]
def baseStart_176773 : Nat := 118140960795 + 176773 * 2 ^ 59
def prefixEnd_176773 : Nat := 4983230072969 + 3 ^ 40 * 176773 * 2
def baseEnd_176773 : Nat := 17929780886388564646823

theorem tailTrace_176773 : CollatzResearch.WordTrace tailWord_176773 prefixEnd_176773 17929780886388564646823 := by
  unfold tailWord_176773
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447440988589086269926973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4298293992392724179951315 6447440988589086269926973)
  ·
    refine ⟨2417790370720907351222615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6447440988589086269926973 2417790370720907351222615)
    ·
      refine ⟨3626685556081361026833923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417790370720907351222615 3626685556081361026833923)
      ·
        refine ⟨5440028334122041540250885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626685556081361026833923 5440028334122041540250885)
        ·
          refine ⟨1020005312647882788797041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5440028334122041540250885 1020005312647882788797041)
          ·
            refine ⟨765003984485912091597781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020005312647882788797041 765003984485912091597781)
            ·
              refine ⟨17929780886388564646823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 765003984485912091597781 17929780886388564646823)
              ·
                rfl

theorem cell19_176773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_176773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176773 prefixEnd_176773 := by exact prefixLift 176773
  have htrace : WordTrace (prefixWord ++ tailWord_176773) baseStart_176773 baseEnd_176773 := by
    simpa [prefixWord, tailWord_176773, baseEnd_176773] using wordTrace_append hprefix tailTrace_176773
  have hstable : (prefixWord ++ tailWord_176773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176773).length < 2 ^ (prefixWord ++ tailWord_176773).sum := by decide
  have hdescent : baseEnd_176773 < baseStart_176773 := by decide
  rcases family_descends (prefixWord ++ tailWord_176773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176788 : List Nat := [2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_176788 : Nat := 118140960795 + 176788 * 2 ^ 59
def prefixEnd_176788 : Nat := 4983230072969 + 3 ^ 40 * 176788 * 2
def baseEnd_176788 : Nat := 53793906931650103607095

theorem tailTrace_176788 : CollatzResearch.WordTrace tailWord_176788 prefixEnd_176788 53793906931650103607095 := by
  unfold tailWord_176788
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223994041767371915861509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4298658722356495887815345 3223994041767371915861509)
  ·
    refine ⟨604498882831382234224033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3223994041767371915861509 604498882831382234224033)
    ·
      refine ⟨453374162123536675668025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 604498882831382234224033 453374162123536675668025)
      ·
        refine ⟨340030621592652506751019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453374162123536675668025 340030621592652506751019)
        ·
          refine ⟨510045932388978760126529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340030621592652506751019 510045932388978760126529)
          ·
            refine ⟨382534449291734070094897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510045932388978760126529 382534449291734070094897)
            ·
              refine ⟨286900836968800552571173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382534449291734070094897 286900836968800552571173)
              ·
                refine ⟨53793906931650103607095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286900836968800552571173 53793906931650103607095)
                ·
                  rfl

theorem cell19_176788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_176788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176788 prefixEnd_176788 := by exact prefixLift 176788
  have htrace : WordTrace (prefixWord ++ tailWord_176788) baseStart_176788 baseEnd_176788 := by
    simpa [prefixWord, tailWord_176788, baseEnd_176788] using wordTrace_append hprefix tailTrace_176788
  have hstable : (prefixWord ++ tailWord_176788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176788).length < 2 ^ (prefixWord ++ tailWord_176788).sum := by decide
  have hdescent : baseEnd_176788 < baseStart_176788 := by decide
  rcases family_descends (prefixWord ++ tailWord_176788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176906 : List Nat := [3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_176906 : Nat := 118140960795 + 176906 * 2 ^ 59
def prefixEnd_176906 : Nat := 4983230072969 + 3 ^ 40 * 176906 * 2
def baseEnd_176906 : Nat := 53829812541860792984551

theorem tailTrace_176906 : CollatzResearch.WordTrace tailWord_176906 prefixEnd_176906 53829812541860792984551 := by
  unfold tailWord_176906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613072974276812496129643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4301527931404833323012381 1613072974276812496129643)
  ·
    refine ⟨2419609461415218744194465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1613072974276812496129643 2419609461415218744194465)
    ·
      refine ⟨1814707096061414058145849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419609461415218744194465 1814707096061414058145849)
      ·
        refine ⟨1361030322046060543609387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1814707096061414058145849 1361030322046060543609387)
        ·
          refine ⟨2041545483069090815414081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361030322046060543609387 2041545483069090815414081)
          ·
            refine ⟨1531159112301818111560561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041545483069090815414081 1531159112301818111560561)
            ·
              refine ⟨1148369334226363583670421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531159112301818111560561 1148369334226363583670421)
              ·
                refine ⟨53829812541860792984551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1148369334226363583670421 53829812541860792984551)
                ·
                  rfl

theorem cell19_176906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_176906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176906 prefixEnd_176906 := by exact prefixLift 176906
  have htrace : WordTrace (prefixWord ++ tailWord_176906) baseStart_176906 baseEnd_176906 := by
    simpa [prefixWord, tailWord_176906, baseEnd_176906] using wordTrace_append hprefix tailTrace_176906
  have hstable : (prefixWord ++ tailWord_176906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176906).length < 2 ^ (prefixWord ++ tailWord_176906).sum := by decide
  have hdescent : baseEnd_176906 < baseStart_176906 := by decide
  rcases family_descends (prefixWord ++ tailWord_176906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176919 : List Nat := [1, 1, 3, 4, 4, 1, 2, 3]
def baseStart_176919 : Nat := 118140960795 + 176919 * 2 ^ 59
def prefixEnd_176919 : Nat := 4983230072969 + 3 ^ 40 * 176919 * 2
def baseEnd_176919 : Nat := 53833768244680614695627

theorem tailTrace_176919 : CollatzResearch.WordTrace tailWord_176919 prefixEnd_176919 53833768244680614695627 := by
  unfold tailWord_176919
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452766046060153204741811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4301844030706768803161207 6452766046060153204741811)
  ·
    refine ⟨9679149069090229807112717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6452766046060153204741811 9679149069090229807112717)
    ·
      refine ⟨3629680900908836177667269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9679149069090229807112717 3629680900908836177667269)
      ·
        refine ⟨680565168920406783312613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3629680900908836177667269 680565168920406783312613)
        ·
          refine ⟨127605969172576271871115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 680565168920406783312613 127605969172576271871115)
          ·
            refine ⟨191408953758864407806673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127605969172576271871115 191408953758864407806673)
            ·
              refine ⟨143556715319148305855005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191408953758864407806673 143556715319148305855005)
              ·
                refine ⟨53833768244680614695627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143556715319148305855005 53833768244680614695627)
                ·
                  rfl

theorem cell19_176919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_176919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176919 prefixEnd_176919 := by exact prefixLift 176919
  have htrace : WordTrace (prefixWord ++ tailWord_176919) baseStart_176919 baseEnd_176919 := by
    simpa [prefixWord, tailWord_176919, baseEnd_176919] using wordTrace_append hprefix tailTrace_176919
  have hstable : (prefixWord ++ tailWord_176919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176919).length < 2 ^ (prefixWord ++ tailWord_176919).sum := by decide
  have hdescent : baseEnd_176919 < baseStart_176919 := by decide
  rcases family_descends (prefixWord ++ tailWord_176919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176938 : List Nat := [3, 1, 4, 3, 2, 1, 5]
def baseStart_176938 : Nat := 118140960795 + 176938 * 2 ^ 59
def prefixEnd_176938 : Nat := 4983230072969 + 3 ^ 40 * 176938 * 2
def baseEnd_176938 : Nat := 17946516552164733424451

theorem tailTrace_176938 : CollatzResearch.WordTrace tailWord_176938 prefixEnd_176938 17946516552164733424451 := by
  unfold tailWord_176938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613364758247829862420867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4302306021994212966455645 1613364758247829862420867)
  ·
    refine ⟨2420047137371744793631301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1613364758247829862420867 2420047137371744793631301)
    ·
      refine ⟨453758838257202148805869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2420047137371744793631301 453758838257202148805869)
      ·
        refine ⟨170159564346450805802201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453758838257202148805869 170159564346450805802201)
        ·
          refine ⟨127619673259838104351651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170159564346450805802201 127619673259838104351651)
          ·
            refine ⟨191429509889757156527477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127619673259838104351651 191429509889757156527477)
            ·
              refine ⟨17946516552164733424451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191429509889757156527477 17946516552164733424451)
              ·
                rfl

theorem cell19_176938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_176938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176938 prefixEnd_176938 := by exact prefixLift 176938
  have htrace : WordTrace (prefixWord ++ tailWord_176938) baseStart_176938 baseEnd_176938 := by
    simpa [prefixWord, tailWord_176938, baseEnd_176938] using wordTrace_append hprefix tailTrace_176938
  have hstable : (prefixWord ++ tailWord_176938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176938).length < 2 ^ (prefixWord ++ tailWord_176938).sum := by decide
  have hdescent : baseEnd_176938 < baseStart_176938 := by decide
  rcases family_descends (prefixWord ++ tailWord_176938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176942 : List Nat := [4, 1, 3, 2, 1, 1, 7]
def baseStart_176942 : Nat := 118140960795 + 176942 * 2 ^ 59
def prefixEnd_176942 : Nat := 4983230072969 + 3 ^ 40 * 176942 * 2
def baseEnd_176942 : Nat := 17946922265274458728151

theorem tailTrace_176942 : CollatzResearch.WordTrace tailWord_176942 prefixEnd_176942 17946922265274458728151 := by
  unfold tailWord_176942
  simp only [CollatzResearch.WordTrace]
  refine ⟨806700615622103516603635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4302403283317885421886053 806700615622103516603635)
  ·
    refine ⟨1210050923433155274905453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 806700615622103516603635 1210050923433155274905453)
    ·
      refine ⟨453769096287433228089545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1210050923433155274905453 453769096287433228089545)
      ·
        refine ⟨340326822215574921067159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453769096287433228089545 340326822215574921067159)
        ·
          refine ⟨510490233323362381600739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340326822215574921067159 510490233323362381600739)
          ·
            refine ⟨765735349985043572401109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510490233323362381600739 765735349985043572401109)
            ·
              refine ⟨17946922265274458728151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 765735349985043572401109 17946922265274458728151)
              ·
                rfl

theorem cell19_176942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_176942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176942 prefixEnd_176942 := by exact prefixLift 176942
  have htrace : WordTrace (prefixWord ++ tailWord_176942) baseStart_176942 baseEnd_176942 := by
    simpa [prefixWord, tailWord_176942, baseEnd_176942] using wordTrace_append hprefix tailTrace_176942
  have hstable : (prefixWord ++ tailWord_176942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176942).length < 2 ^ (prefixWord ++ tailWord_176942).sum := by decide
  have hdescent : baseEnd_176942 < baseStart_176942 := by decide
  rcases family_descends (prefixWord ++ tailWord_176942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176963 : List Nat := [1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_176963 : Nat := 118140960795 + 176963 * 2 ^ 59
def prefixEnd_176963 : Nat := 4983230072969 + 3 ^ 40 * 176963 * 2
def baseEnd_176963 : Nat := 53847156777301549717729

theorem tailTrace_176963 : CollatzResearch.WordTrace tailWord_176963 prefixEnd_176963 53847156777301549717729 := by
  unfold tailWord_176963
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454370857900748719343543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4302913905267165812895695 6454370857900748719343543)
  ·
    refine ⟨9681556286851123079015315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6454370857900748719343543 9681556286851123079015315)
    ·
      refine ⟨14522334430276684618522973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9681556286851123079015315 14522334430276684618522973)
      ·
        refine ⟨5445875411353756731946115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14522334430276684618522973 5445875411353756731946115)
        ·
          refine ⟨8168813117030635097919173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445875411353756731946115 8168813117030635097919173)
          ·
            refine ⟨1531652459443244080859845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8168813117030635097919173 1531652459443244080859845)
            ·
              refine ⟨287184836145608265161221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1531652459443244080859845 287184836145608265161221)
              ·
                refine ⟨53847156777301549717729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287184836145608265161221 53847156777301549717729)
                ·
                  rfl

theorem cell19_176963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_176963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_176963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_176963 prefixEnd_176963 := by exact prefixLift 176963
  have htrace : WordTrace (prefixWord ++ tailWord_176963) baseStart_176963 baseEnd_176963 := by
    simpa [prefixWord, tailWord_176963, baseEnd_176963] using wordTrace_append hprefix tailTrace_176963
  have hstable : (prefixWord ++ tailWord_176963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176963).length < 2 ^ (prefixWord ++ tailWord_176963).sum := by decide
  have hdescent : baseEnd_176963 < baseStart_176963 := by decide
  rcases family_descends (prefixWord ++ tailWord_176963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177077 : List Nat := [1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_177077 : Nat := 118140960795 + 177077 * 2 ^ 59
def prefixEnd_177077 : Nat := 4983230072969 + 3 ^ 40 * 177077 * 2
def baseEnd_177077 : Nat := 53881845248183063184085

theorem tailTrace_177077 : CollatzResearch.WordTrace tailWord_177077 prefixEnd_177077 53881845248183063184085 := by
  unfold tailWord_177077
  simp only [CollatzResearch.WordTrace]
  refine ⟨6458528779487746188993485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4305685852991830792662323 6458528779487746188993485)
  ·
    refine ⟨2421948292307904820872557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6458528779487746188993485 2421948292307904820872557)
    ·
      refine ⟨908230609615464307827209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2421948292307904820872557 908230609615464307827209)
      ·
        refine ⟨681172957211598230870407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908230609615464307827209 681172957211598230870407)
        ·
          refine ⟨1021759435817397346305611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681172957211598230870407 1021759435817397346305611)
          ·
            refine ⟨1532639153726096019458417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021759435817397346305611 1532639153726096019458417)
            ·
              refine ⟨1149479365294572014593813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532639153726096019458417 1149479365294572014593813)
              ·
                refine ⟨53881845248183063184085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1149479365294572014593813 53881845248183063184085)
                ·
                  rfl

theorem cell19_177077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_177077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177077 prefixEnd_177077 := by exact prefixLift 177077
  have htrace : WordTrace (prefixWord ++ tailWord_177077) baseStart_177077 baseEnd_177077 := by
    simpa [prefixWord, tailWord_177077, baseEnd_177077] using wordTrace_append hprefix tailTrace_177077
  have hstable : (prefixWord ++ tailWord_177077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177077).length < 2 ^ (prefixWord ++ tailWord_177077).sum := by decide
  have hdescent : baseEnd_177077 < baseStart_177077 := by decide
  rcases family_descends (prefixWord ++ tailWord_177077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177092 : List Nat := [2, 3, 3, 3, 1, 1, 1, 5]
def baseStart_177092 : Nat := 118140960795 + 177092 * 2 ^ 59
def prefixEnd_177092 : Nat := 4983230072969 + 3 ^ 40 * 177092 * 2
def baseEnd_177092 : Nat := 53886409520667472850711

theorem tailTrace_177092 : CollatzResearch.WordTrace tailWord_177092 prefixEnd_177092 53886409520667472850711 := by
  unfold tailWord_177092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3229537937216701875394765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4306050582955602500526353 3229537937216701875394765)
  ·
    refine ⟨1211076726456263203273037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3229537937216701875394765 1211076726456263203273037)
    ·
      refine ⟨454153772421098701227389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1211076726456263203273037 454153772421098701227389)
      ·
        refine ⟨170307664657912012960271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454153772421098701227389 170307664657912012960271)
        ·
          refine ⟨255461496986868019440407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170307664657912012960271 255461496986868019440407)
          ·
            refine ⟨383192245480302029160611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255461496986868019440407 383192245480302029160611)
            ·
              refine ⟨574788368220453043740917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383192245480302029160611 574788368220453043740917)
              ·
                refine ⟨53886409520667472850711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574788368220453043740917 53886409520667472850711)
                ·
                  rfl

theorem cell19_177092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_177092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177092 prefixEnd_177092 := by exact prefixLift 177092
  have htrace : WordTrace (prefixWord ++ tailWord_177092) baseStart_177092 baseEnd_177092 := by
    simpa [prefixWord, tailWord_177092, baseEnd_177092] using wordTrace_append hprefix tailTrace_177092
  have hstable : (prefixWord ++ tailWord_177092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177092).length < 2 ^ (prefixWord ++ tailWord_177092).sum := by decide
  have hdescent : baseEnd_177092 < baseStart_177092 := by decide
  rcases family_descends (prefixWord ++ tailWord_177092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177153 : List Nat := [1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_177153 : Nat := 118140960795 + 177153 * 2 ^ 59
def prefixEnd_177153 : Nat := 4983230072969 + 3 ^ 40 * 177153 * 2
def baseEnd_177153 : Nat := 53904970895437405494989

theorem tailTrace_177153 : CollatzResearch.WordTrace tailWord_177153 prefixEnd_177153 53904970895437405494989 := by
  unfold tailWord_177153
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461300727212411168760113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4307533818141607445840075 6461300727212411168760113)
  ·
    refine ⟨4845975545409308376570085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6461300727212411168760113 4845975545409308376570085)
    ·
      refine ⟨908620414764245320606891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4845975545409308376570085 908620414764245320606891)
      ·
        refine ⟨1362930622146367980910337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908620414764245320606891 1362930622146367980910337)
        ·
          refine ⟨1022197966609775985682753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1362930622146367980910337 1022197966609775985682753)
          ·
            refine ⟨766648474957331989262065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022197966609775985682753 766648474957331989262065)
            ·
              refine ⟨574986356217998991946549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766648474957331989262065 574986356217998991946549)
              ·
                refine ⟨53904970895437405494989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574986356217998991946549 53904970895437405494989)
                ·
                  rfl

theorem cell19_177153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_177153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177153 prefixEnd_177153 := by exact prefixLift 177153
  have htrace : WordTrace (prefixWord ++ tailWord_177153) baseStart_177153 baseEnd_177153 := by
    simpa [prefixWord, tailWord_177153, baseEnd_177153] using wordTrace_append hprefix tailTrace_177153
  have hstable : (prefixWord ++ tailWord_177153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177153).length < 2 ^ (prefixWord ++ tailWord_177153).sum := by decide
  have hdescent : baseEnd_177153 < baseStart_177153 := by decide
  rcases family_descends (prefixWord ++ tailWord_177153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177172 : List Nat := [2, 4, 3, 10]
def baseStart_177172 : Nat := 118140960795 + 177172 * 2 ^ 59
def prefixEnd_177172 : Nat := 4983230072969 + 3 ^ 40 * 177172 * 2
def baseEnd_177172 : Nat := 665564843299394951515

theorem tailTrace_177172 : CollatzResearch.WordTrace tailWord_177172 prefixEnd_177172 665564843299394951515 := by
  unfold tailWord_177172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3230996857071788706850885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4307995809429051609134513 3230996857071788706850885)
  ·
    refine ⟨605811910700960382534541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3230996857071788706850885 605811910700960382534541)
    ·
      refine ⟨227179466512860143450453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 605811910700960382534541 227179466512860143450453)
      ·
        refine ⟨665564843299394951515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 227179466512860143450453 665564843299394951515)
        ·
          rfl

theorem cell19_177172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 10].length) (baseStart_177172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177172 prefixEnd_177172 := by exact prefixLift 177172
  have htrace : WordTrace (prefixWord ++ tailWord_177172) baseStart_177172 baseEnd_177172 := by
    simpa [prefixWord, tailWord_177172, baseEnd_177172] using wordTrace_append hprefix tailTrace_177172
  have hstable : (prefixWord ++ tailWord_177172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177172).length < 2 ^ (prefixWord ++ tailWord_177172).sum := by decide
  have hdescent : baseEnd_177172 < baseStart_177172 := by decide
  rcases family_descends (prefixWord ++ tailWord_177172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177206 : List Nat := [5, 1, 2, 1, 1, 3, 3, 3]
def baseStart_177206 : Nat := 118140960795 + 177206 * 2 ^ 59
def prefixEnd_177206 : Nat := 4983230072969 + 3 ^ 40 * 177206 * 2
def baseEnd_177206 : Nat := 53921097991548986317067

theorem tailTrace_177206 : CollatzResearch.WordTrace tailWord_177206 prefixEnd_177206 53921097991548986317067 := by
  unfold tailWord_177206
  simp only [CollatzResearch.WordTrace]
  refine ⟨403952112251275076277467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4308822530680267480292981 403952112251275076277467)
  ·
    refine ⟨605928168376912614416201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403952112251275076277467 605928168376912614416201)
    ·
      refine ⟨454446126282684460812151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 605928168376912614416201 454446126282684460812151)
      ·
        refine ⟨681669189424026691218227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454446126282684460812151 681669189424026691218227)
        ·
          refine ⟨1022503784136040036827341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681669189424026691218227 1022503784136040036827341)
          ·
            refine ⟨383438919051015013810253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1022503784136040036827341 383438919051015013810253)
            ·
              refine ⟨143789594644130630178845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383438919051015013810253 143789594644130630178845)
              ·
                refine ⟨53921097991548986317067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143789594644130630178845 53921097991548986317067)
                ·
                  rfl

theorem cell19_177206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_177206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177206 prefixEnd_177206 := by exact prefixLift 177206
  have htrace : WordTrace (prefixWord ++ tailWord_177206) baseStart_177206 baseEnd_177206 := by
    simpa [prefixWord, tailWord_177206, baseEnd_177206] using wordTrace_append hprefix tailTrace_177206
  have hstable : (prefixWord ++ tailWord_177206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177206).length < 2 ^ (prefixWord ++ tailWord_177206).sum := by decide
  have hdescent : baseEnd_177206 < baseStart_177206 := by decide
  rcases family_descends (prefixWord ++ tailWord_177206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177208 : List Nat := [2, 1, 2, 1, 5, 2, 3, 3]
def baseStart_177208 : Nat := 118140960795 + 177208 * 2 ^ 59
def prefixEnd_177208 : Nat := 4983230072969 + 3 ^ 40 * 177208 * 2
def baseEnd_177208 : Nat := 53921706561213574272617

theorem tailTrace_177208 : CollatzResearch.WordTrace tailWord_177208 prefixEnd_177208 53921706561213574272617 := by
  unfold tailWord_177208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231653371006577781006139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4308871161342103708008185 3231653371006577781006139)
  ·
    refine ⟨4847480056509866671509209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231653371006577781006139 4847480056509866671509209)
    ·
      refine ⟨3635610042382400003631907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4847480056509866671509209 3635610042382400003631907)
      ·
        refine ⟨5453415063573600005447861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635610042382400003631907 5453415063573600005447861)
        ·
          refine ⟨511257662210025000510737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5453415063573600005447861 511257662210025000510737)
          ·
            refine ⟨383443246657518750383053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511257662210025000510737 383443246657518750383053)
            ·
              refine ⟨143791217496569531393645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383443246657518750383053 143791217496569531393645)
              ·
                refine ⟨53921706561213574272617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143791217496569531393645 53921706561213574272617)
                ·
                  rfl

theorem cell19_177208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_177208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177208 prefixEnd_177208 := by exact prefixLift 177208
  have htrace : WordTrace (prefixWord ++ tailWord_177208) baseStart_177208 baseEnd_177208 := by
    simpa [prefixWord, tailWord_177208, baseEnd_177208] using wordTrace_append hprefix tailTrace_177208
  have hstable : (prefixWord ++ tailWord_177208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177208).length < 2 ^ (prefixWord ++ tailWord_177208).sum := by decide
  have hdescent : baseEnd_177208 < baseStart_177208 := by decide
  rcases family_descends (prefixWord ++ tailWord_177208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177278 : List Nat := [4, 2, 4, 1, 2, 1, 5]
def baseStart_177278 : Nat := 118140960795 + 177278 * 2 ^ 59
def prefixEnd_177278 : Nat := 4983230072969 + 3 ^ 40 * 177278 * 2
def baseEnd_177278 : Nat := 17981002166491384238957

theorem tailTrace_177278 : CollatzResearch.WordTrace tailWord_177278 prefixEnd_177278 17981002166491384238957 := by
  unfold tailWord_177278
  simp only [CollatzResearch.WordTrace]
  refine ⟨808232481469944689632561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4310573234506371678040325 808232481469944689632561)
  ·
    refine ⟨606174361102458517224421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 808232481469944689632561 606174361102458517224421)
    ·
      refine ⟨113657692706710971979579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 606174361102458517224421 113657692706710971979579)
      ·
        refine ⟨170486539060066457969369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113657692706710971979579 170486539060066457969369)
        ·
          refine ⟨127864904295049843477027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170486539060066457969369 127864904295049843477027)
          ·
            refine ⟨191797356442574765215541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127864904295049843477027 191797356442574765215541)
            ·
              refine ⟨17981002166491384238957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191797356442574765215541 17981002166491384238957)
              ·
                rfl

theorem cell19_177278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_177278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177278 prefixEnd_177278 := by exact prefixLift 177278
  have htrace : WordTrace (prefixWord ++ tailWord_177278) baseStart_177278 baseEnd_177278 := by
    simpa [prefixWord, tailWord_177278, baseEnd_177278] using wordTrace_append hprefix tailTrace_177278
  have hstable : (prefixWord ++ tailWord_177278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177278).length < 2 ^ (prefixWord ++ tailWord_177278).sum := by decide
  have hdescent : baseEnd_177278 < baseStart_177278 := by decide
  rcases family_descends (prefixWord ++ tailWord_177278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177322 : List Nat := [3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_177322 : Nat := 118140960795 + 177322 * 2 ^ 59
def prefixEnd_177322 : Nat := 4983230072969 + 3 ^ 40 * 177322 * 2
def baseEnd_177322 : Nat := 53956395032095087738973

theorem tailTrace_177322 : CollatzResearch.WordTrace tailWord_177322 prefixEnd_177322 53956395032095087738973 := by
  unfold tailWord_177322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616866165900038257915555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4311643109066768687774813 1616866165900038257915555)
  ·
    refine ⟨2425299248850057386873333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1616866165900038257915555 2425299248850057386873333)
    ·
      refine ⟨227371804579692880019375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2425299248850057386873333 227371804579692880019375)
      ·
        refine ⟨341057706869539320029063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227371804579692880019375 341057706869539320029063)
        ·
          refine ⟨511586560304308980043595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341057706869539320029063 511586560304308980043595)
          ·
            refine ⟨767379840456463470065393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511586560304308980043595 767379840456463470065393)
            ·
              refine ⟨575534880342347602549045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767379840456463470065393 575534880342347602549045)
              ·
                refine ⟨53956395032095087738973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 575534880342347602549045 53956395032095087738973)
                ·
                  rfl

theorem cell19_177322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_177322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177322 prefixEnd_177322 := by exact prefixLift 177322
  have htrace : WordTrace (prefixWord ++ tailWord_177322) baseStart_177322 baseEnd_177322 := by
    simpa [prefixWord, tailWord_177322, baseEnd_177322] using wordTrace_append hprefix tailTrace_177322
  have hstable : (prefixWord ++ tailWord_177322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177322).length < 2 ^ (prefixWord ++ tailWord_177322).sum := by decide
  have hdescent : baseEnd_177322 < baseStart_177322 := by decide
  rcases family_descends (prefixWord ++ tailWord_177322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177358 : List Nat := [4, 1, 1, 1, 6, 1, 1, 4]
def baseStart_177358 : Nat := 118140960795 + 177358 * 2 ^ 59
def prefixEnd_177358 : Nat := 4983230072969 + 3 ^ 40 * 177358 * 2
def baseEnd_177358 : Nat := 53967349286057670938875

theorem tailTrace_177358 : CollatzResearch.WordTrace tailWord_177358 prefixEnd_177358 53967349286057670938875 := by
  unfold tailWord_177358
  simp only [CollatzResearch.WordTrace]
  refine ⟨808597211433716397496591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4312518460979820786648485 808597211433716397496591)
  ·
    refine ⟨1212895817150574596244887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 808597211433716397496591 1212895817150574596244887)
    ·
      refine ⟨1819343725725861894367331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212895817150574596244887 1819343725725861894367331)
      ·
        refine ⟨2729015588588792841550997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819343725725861894367331 2729015588588792841550997)
        ·
          refine ⟨127922605715099664447703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2729015588588792841550997 127922605715099664447703)
          ·
            refine ⟨191883908572649496671555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127922605715099664447703 191883908572649496671555)
            ·
              refine ⟨287825862858974245007333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191883908572649496671555 287825862858974245007333)
              ·
                refine ⟨53967349286057670938875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287825862858974245007333 53967349286057670938875)
                ·
                  rfl

theorem cell19_177358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_177358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177358 prefixEnd_177358 := by exact prefixLift 177358
  have htrace : WordTrace (prefixWord ++ tailWord_177358) baseStart_177358 baseEnd_177358 := by
    simpa [prefixWord, tailWord_177358, baseEnd_177358] using wordTrace_append hprefix tailTrace_177358
  have hstable : (prefixWord ++ tailWord_177358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177358).length < 2 ^ (prefixWord ++ tailWord_177358).sum := by decide
  have hdescent : baseEnd_177358 < baseStart_177358 := by decide
  rcases family_descends (prefixWord ++ tailWord_177358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177402 : List Nat := [3, 1, 1, 1, 1, 4, 8]
def baseStart_177402 : Nat := 118140960795 + 177402 * 2 ^ 59
def prefixEnd_177402 : Nat := 4983230072969 + 3 ^ 40 * 177402 * 2
def baseEnd_177402 : Nat := 17993579272892868653659

theorem tailTrace_177402 : CollatzResearch.WordTrace tailWord_177402 prefixEnd_177402 17993579272892868653659 := by
  unfold tailWord_177402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1617595625827581673643615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4313588335540217796382973 1617595625827581673643615)
  ·
    refine ⟨2426393438741372510465423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1617595625827581673643615 2426393438741372510465423)
    ·
      refine ⟨3639590158112058765698135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2426393438741372510465423 3639590158112058765698135)
      ·
        refine ⟨5459385237168088148547203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639590158112058765698135 5459385237168088148547203)
        ·
          refine ⟨8189077855752132222820805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5459385237168088148547203 8189077855752132222820805)
          ·
            refine ⟨1535452097953524791778901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8189077855752132222820805 1535452097953524791778901)
            ·
              refine ⟨17993579272892868653659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1535452097953524791778901 17993579272892868653659)
              ·
                rfl

theorem cell19_177402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_177402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177402 prefixEnd_177402 := by exact prefixLift 177402
  have htrace : WordTrace (prefixWord ++ tailWord_177402) baseStart_177402 baseEnd_177402 := by
    simpa [prefixWord, tailWord_177402, baseEnd_177402] using wordTrace_append hprefix tailTrace_177402
  have hstable : (prefixWord ++ tailWord_177402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177402).length < 2 ^ (prefixWord ++ tailWord_177402).sum := by decide
  have hdescent : baseEnd_177402 < baseStart_177402 := by decide
  rcases family_descends (prefixWord ++ tailWord_177402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177457 : List Nat := [1, 2, 2, 3, 3, 3, 5]
def baseStart_177457 : Nat := 118140960795 + 177457 * 2 ^ 59
def prefixEnd_177457 : Nat := 4983230072969 + 3 ^ 40 * 177457 * 2
def baseEnd_177457 : Nat := 17999157828151591579535

theorem tailTrace_177457 : CollatzResearch.WordTrace tailWord_177457 prefixEnd_177457 17999157828151591579535 := by
  unfold tailWord_177457
  simp only [CollatzResearch.WordTrace]
  refine ⟨6472388518111071087826625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4314925678740714058551083 6472388518111071087826625)
  ·
    refine ⟨4854291388583303315869969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6472388518111071087826625 4854291388583303315869969)
    ·
      refine ⟨3640718541437477486902477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4854291388583303315869969 3640718541437477486902477)
      ·
        refine ⟨1365269453039054057588429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3640718541437477486902477 1365269453039054057588429)
        ·
          refine ⟨511976044889645271595661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1365269453039054057588429 511976044889645271595661)
          ·
            refine ⟨191991016833616976848373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511976044889645271595661 191991016833616976848373)
            ·
              refine ⟨17999157828151591579535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191991016833616976848373 17999157828151591579535)
              ·
                rfl

theorem cell19_177457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_177457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177457 prefixEnd_177457 := by exact prefixLift 177457
  have htrace : WordTrace (prefixWord ++ tailWord_177457) baseStart_177457 baseEnd_177457 := by
    simpa [prefixWord, tailWord_177457, baseEnd_177457] using wordTrace_append hprefix tailTrace_177457
  have hstable : (prefixWord ++ tailWord_177457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177457).length < 2 ^ (prefixWord ++ tailWord_177457).sum := by decide
  have hdescent : baseEnd_177457 < baseStart_177457 := by decide
  rcases family_descends (prefixWord ++ tailWord_177457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177459 : List Nat := [1, 1, 1, 2, 5, 2, 7]
def baseStart_177459 : Nat := 118140960795 + 177459 * 2 ^ 59
def prefixEnd_177459 : Nat := 4983230072969 + 3 ^ 40 * 177459 * 2
def baseEnd_177459 : Nat := 17999360684706454231385

theorem tailTrace_177459 : CollatzResearch.WordTrace tailWord_177459 prefixEnd_177459 17999360684706454231385 := by
  unfold tailWord_177459
  simp only [CollatzResearch.WordTrace]
  refine ⟨6472461464103825429399431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4314974309402550286266287 6472461464103825429399431)
  ·
    refine ⟨9708692196155738144099147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6472461464103825429399431 9708692196155738144099147)
    ·
      refine ⟨14563038294233607216148721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9708692196155738144099147 14563038294233607216148721)
      ·
        refine ⟨10922278720675205412111541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14563038294233607216148721 10922278720675205412111541)
        ·
          refine ⟨1023963630063300507385457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10922278720675205412111541 1023963630063300507385457)
          ·
            refine ⟨767972722547475380539093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023963630063300507385457 767972722547475380539093)
            ·
              refine ⟨17999360684706454231385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 767972722547475380539093 17999360684706454231385)
              ·
                rfl

theorem cell19_177459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_177459 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177459 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177459 prefixEnd_177459 := by exact prefixLift 177459
  have htrace : WordTrace (prefixWord ++ tailWord_177459) baseStart_177459 baseEnd_177459 := by
    simpa [prefixWord, tailWord_177459, baseEnd_177459] using wordTrace_append hprefix tailTrace_177459
  have hstable : (prefixWord ++ tailWord_177459).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177459).length < 2 ^ (prefixWord ++ tailWord_177459).sum := by decide
  have hdescent : baseEnd_177459 < baseStart_177459 := by decide
  rcases family_descends (prefixWord ++ tailWord_177459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177497 : List Nat := [1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_177497 : Nat := 118140960795 + 177497 * 2 ^ 59
def prefixEnd_177497 : Nat := 4983230072969 + 3 ^ 40 * 177497 * 2
def baseEnd_177497 : Nat := 54009644877746533849607

theorem tailTrace_177497 : CollatzResearch.WordTrace tailWord_177497 prefixEnd_177497 54009644877746533849607 := by
  unfold tailWord_177497
  simp only [CollatzResearch.WordTrace]
  refine ⟨6473847437966157919282745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4315898291977438612855163 6473847437966157919282745)
  ·
    refine ⟨4855385578474618439462059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6473847437966157919282745 4855385578474618439462059)
    ·
      refine ⟨7283078367711927659193089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855385578474618439462059 7283078367711927659193089)
      ·
        refine ⟨5462308775783945744394817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7283078367711927659193089 5462308775783945744394817)
        ·
          refine ⟨4096731581837959308296113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5462308775783945744394817 4096731581837959308296113)
          ·
            refine ⟨3072548686378469481222085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4096731581837959308296113 3072548686378469481222085)
            ·
              refine ⟨576102878695963027729141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3072548686378469481222085 576102878695963027729141)
              ·
                refine ⟨54009644877746533849607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 576102878695963027729141 54009644877746533849607)
                ·
                  rfl

theorem cell19_177497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_177497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177497 prefixEnd_177497 := by exact prefixLift 177497
  have htrace : WordTrace (prefixWord ++ tailWord_177497) baseStart_177497 baseEnd_177497 := by
    simpa [prefixWord, tailWord_177497, baseEnd_177497] using wordTrace_append hprefix tailTrace_177497
  have hstable : (prefixWord ++ tailWord_177497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177497).length < 2 ^ (prefixWord ++ tailWord_177497).sum := by decide
  have hdescent : baseEnd_177497 < baseStart_177497 := by decide
  rcases family_descends (prefixWord ++ tailWord_177497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177514 : List Nat := [3, 1, 3, 3, 2, 7]
def baseStart_177514 : Nat := 118140960795 + 177514 * 2 ^ 59
def prefixEnd_177514 : Nat := 4983230072969 + 3 ^ 40 * 177514 * 2
def baseEnd_177514 : Nat := 6001646413321725719087

theorem tailTrace_177514 : CollatzResearch.WordTrace tailWord_177514 prefixEnd_177514 6001646413321725719087 := by
  unfold tailWord_177514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618616869726142455662899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4316311652603046548434397 1618616869726142455662899)
  ·
    refine ⟨2427925304589213683494349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1618616869726142455662899 2427925304589213683494349)
    ·
      refine ⟨910471989220955131310381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2427925304589213683494349 910471989220955131310381)
      ·
        refine ⟨341426995957858174241393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 910471989220955131310381 341426995957858174241393)
        ·
          refine ⟨256070246968393630681045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341426995957858174241393 256070246968393630681045)
          ·
            refine ⟨6001646413321725719087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 256070246968393630681045 6001646413321725719087)
            ·
              rfl

theorem cell19_177514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_177514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177514 prefixEnd_177514 := by exact prefixLift 177514
  have htrace : WordTrace (prefixWord ++ tailWord_177514) baseStart_177514 baseEnd_177514 := by
    simpa [prefixWord, tailWord_177514, baseEnd_177514] using wordTrace_append hprefix tailTrace_177514
  have hstable : (prefixWord ++ tailWord_177514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177514).length < 2 ^ (prefixWord ++ tailWord_177514).sum := by decide
  have hdescent : baseEnd_177514 < baseStart_177514 := by decide
  rcases family_descends (prefixWord ++ tailWord_177514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177516 : List Nat := [2, 2, 1, 1, 5, 8]
def baseStart_177516 : Nat := 118140960795 + 177516 * 2 ^ 59
def prefixEnd_177516 : Nat := 4983230072969 + 3 ^ 40 * 177516 * 2
def baseEnd_177516 : Nat := 6001714032173346603037

theorem tailTrace_177516 : CollatzResearch.WordTrace tailWord_177516 prefixEnd_177516 6001714032173346603037 := by
  unfold tailWord_177516
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237270212448662082112201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4316360283264882776149601 3237270212448662082112201)
  ·
    refine ⟨2427952659336496561584151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3237270212448662082112201 2427952659336496561584151)
    ·
      refine ⟨3641928989004744842376227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427952659336496561584151 3641928989004744842376227)
      ·
        refine ⟨5462893483507117263564341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641928989004744842376227 5462893483507117263564341)
        ·
          refine ⟨512146264078792243459157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5462893483507117263564341 512146264078792243459157)
          ·
            refine ⟨6001714032173346603037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 512146264078792243459157 6001714032173346603037)
            ·
              rfl

theorem cell19_177516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_177516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177516 prefixEnd_177516 := by exact prefixLift 177516
  have htrace : WordTrace (prefixWord ++ tailWord_177516) baseStart_177516 baseEnd_177516 := by
    simpa [prefixWord, tailWord_177516, baseEnd_177516] using wordTrace_append hprefix tailTrace_177516
  have hstable : (prefixWord ++ tailWord_177516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177516).length < 2 ^ (prefixWord ++ tailWord_177516).sum := by decide
  have hdescent : baseEnd_177516 < baseStart_177516 := by decide
  rcases family_descends (prefixWord ++ tailWord_177516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177645 : List Nat := [1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_177645 : Nat := 118140960795 + 177645 * 2 ^ 59
def prefixEnd_177645 : Nat := 4983230072969 + 3 ^ 40 * 177645 * 2
def baseEnd_177645 : Nat := 54054679032926042560315

theorem tailTrace_177645 : CollatzResearch.WordTrace tailWord_177645 prefixEnd_177645 54054679032926042560315 := by
  unfold tailWord_177645
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479245441429979195670389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4319496960953319463780259 6479245441429979195670389)
  ·
    refine ⟨607429260134060549594099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6479245441429979195670389 607429260134060549594099)
    ·
      refine ⟨911143890201090824391149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607429260134060549594099 911143890201090824391149)
      ·
        refine ⟨341678958825409059146681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 911143890201090824391149 341678958825409059146681)
        ·
          refine ⟨256259219119056794360011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341678958825409059146681 256259219119056794360011)
          ·
            refine ⟨384388828678585191540017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256259219119056794360011 384388828678585191540017)
            ·
              refine ⟨288291621508938893655013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384388828678585191540017 288291621508938893655013)
              ·
                refine ⟨54054679032926042560315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288291621508938893655013 54054679032926042560315)
                ·
                  rfl

theorem cell19_177645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_177645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177645 prefixEnd_177645 := by exact prefixLift 177645
  have htrace : WordTrace (prefixWord ++ tailWord_177645) baseStart_177645 baseEnd_177645 := by
    simpa [prefixWord, tailWord_177645, baseEnd_177645] using wordTrace_append hprefix tailTrace_177645
  have hstable : (prefixWord ++ tailWord_177645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177645).length < 2 ^ (prefixWord ++ tailWord_177645).sum := by decide
  have hdescent : baseEnd_177645 < baseStart_177645 := by decide
  rcases family_descends (prefixWord ++ tailWord_177645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177649 : List Nat := [1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_177649 : Nat := 118140960795 + 177649 * 2 ^ 59
def prefixEnd_177649 : Nat := 4983230072969 + 3 ^ 40 * 177649 * 2
def baseEnd_177649 : Nat := 54055896172255218471415

theorem tailTrace_177649 : CollatzResearch.WordTrace tailWord_177649 prefixEnd_177649 54055896172255218471415 := by
  unfold tailWord_177649
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479391333415487878816001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4319594222276991919210667 6479391333415487878816001)
  ·
    refine ⟨4859543500061615909112001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6479391333415487878816001 4859543500061615909112001)
    ·
      refine ⟨3644657625046211931834001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4859543500061615909112001 3644657625046211931834001)
      ·
        refine ⟨2733493218784658948875501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3644657625046211931834001 2733493218784658948875501)
        ·
          refine ⟨1025059957044247105828313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2733493218784658948875501 1025059957044247105828313)
          ·
            refine ⟨768794967783185329371235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025059957044247105828313 768794967783185329371235)
            ·
              refine ⟨1153192451674777994056853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768794967783185329371235 1153192451674777994056853)
              ·
                refine ⟨54055896172255218471415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1153192451674777994056853 54055896172255218471415)
                ·
                  rfl

theorem cell19_177649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_177649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177649 prefixEnd_177649 := by exact prefixLift 177649
  have htrace : WordTrace (prefixWord ++ tailWord_177649) baseStart_177649 baseEnd_177649 := by
    simpa [prefixWord, tailWord_177649, baseEnd_177649] using wordTrace_append hprefix tailTrace_177649
  have hstable : (prefixWord ++ tailWord_177649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177649).length < 2 ^ (prefixWord ++ tailWord_177649).sum := by decide
  have hdescent : baseEnd_177649 < baseStart_177649 := by decide
  rcases family_descends (prefixWord ++ tailWord_177649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177778 : List Nat := [3, 2, 1, 2, 3, 3, 2, 3]
def baseStart_177778 : Nat := 118140960795 + 177778 * 2 ^ 59
def prefixEnd_177778 : Nat := 4983230072969 + 3 ^ 40 * 177778 * 2
def baseEnd_177778 : Nat := 54095148915621141604397

theorem tailTrace_177778 : CollatzResearch.WordTrace tailWord_177778 prefixEnd_177778 54095148915621141604397 := by
  unfold tailWord_177778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621024087487035727565497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4322730899965428606841325 1621024087487035727565497)
  ·
    refine ⟨1215768065615276795674123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1621024087487035727565497 1215768065615276795674123)
    ·
      refine ⟨1823652098422915193511185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1215768065615276795674123 1823652098422915193511185)
      ·
        refine ⟨1367739073817186395133389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1823652098422915193511185 1367739073817186395133389)
        ·
          refine ⟨512902152681444898175021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1367739073817186395133389 512902152681444898175021)
          ·
            refine ⟨192338307255541836815633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 512902152681444898175021 192338307255541836815633)
            ·
              refine ⟨144253730441656377611725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192338307255541836815633 144253730441656377611725)
              ·
                refine ⟨54095148915621141604397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144253730441656377611725 54095148915621141604397)
                ·
                  rfl

theorem cell19_177778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_177778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177778 prefixEnd_177778 := by exact prefixLift 177778
  have htrace : WordTrace (prefixWord ++ tailWord_177778) baseStart_177778 baseEnd_177778 := by
    simpa [prefixWord, tailWord_177778, baseEnd_177778] using wordTrace_append hprefix tailTrace_177778
  have hstable : (prefixWord ++ tailWord_177778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177778).length < 2 ^ (prefixWord ++ tailWord_177778).sum := by decide
  have hdescent : baseEnd_177778 < baseStart_177778 := by decide
  rcases family_descends (prefixWord ++ tailWord_177778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177953 : List Nat := [1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_177953 : Nat := 118140960795 + 177953 * 2 ^ 59
def prefixEnd_177953 : Nat := 4983230072969 + 3 ^ 40 * 177953 * 2
def baseEnd_177953 : Nat := 54148398761272587715031

theorem tailTrace_177953 : CollatzResearch.WordTrace tailWord_177953 prefixEnd_177953 54148398761272587715031 := by
  unfold tailWord_177953
  simp only [CollatzResearch.WordTrace]
  refine ⟨6490479124314147797882513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4326986082876098531921675 6490479124314147797882513)
  ·
    refine ⟨4867859343235610848411885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6490479124314147797882513 4867859343235610848411885)
    ·
      refine ⟨1825447253713354068154457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4867859343235610848411885 1825447253713354068154457)
      ·
        refine ⟨1369085440285015551115843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1825447253713354068154457 1369085440285015551115843)
        ·
          refine ⟨2053628160427523326673765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369085440285015551115843 2053628160427523326673765)
          ·
            refine ⟨385055280080160623751331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2053628160427523326673765 385055280080160623751331)
            ·
              refine ⟨577582920120240935626997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385055280080160623751331 577582920120240935626997)
              ·
                refine ⟨54148398761272587715031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 577582920120240935626997 54148398761272587715031)
                ·
                  rfl

theorem cell19_177953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_177953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177953 prefixEnd_177953 := by exact prefixLift 177953
  have htrace : WordTrace (prefixWord ++ tailWord_177953) baseStart_177953 baseEnd_177953 := by
    simpa [prefixWord, tailWord_177953, baseEnd_177953] using wordTrace_append hprefix tailTrace_177953
  have hstable : (prefixWord ++ tailWord_177953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177953).length < 2 ^ (prefixWord ++ tailWord_177953).sum := by decide
  have hdescent : baseEnd_177953 < baseStart_177953 := by decide
  rcases family_descends (prefixWord ++ tailWord_177953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178124 : List Nat := [2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_178124 : Nat := 118140960795 + 178124 * 2 ^ 59
def prefixEnd_178124 : Nat := 4983230072969 + 3 ^ 40 * 178124 * 2
def baseEnd_178124 : Nat := 54200431467594857914565

theorem tailTrace_178124 : CollatzResearch.WordTrace tailWord_178124 prefixEnd_178124 54200431467594857914565 := by
  unfold tailWord_178124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248358003347322001178713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4331144004463096001571617 3248358003347322001178713)
  ·
    refine ⟨2436268502510491500884035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3248358003347322001178713 2436268502510491500884035)
    ·
      refine ⟨3654402753765737251326053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2436268502510491500884035 3654402753765737251326053)
      ·
        refine ⟨685200516331075734623635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3654402753765737251326053 685200516331075734623635)
        ·
          refine ⟨1027800774496613601935453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685200516331075734623635 1027800774496613601935453)
          ·
            refine ⟨385425290436230100725795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1027800774496613601935453 385425290436230100725795)
            ·
              refine ⟨578137935654345151088693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385425290436230100725795 578137935654345151088693)
              ·
                refine ⟨54200431467594857914565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 578137935654345151088693 54200431467594857914565)
                ·
                  rfl

theorem cell19_178124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_178124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178124 prefixEnd_178124 := by exact prefixLift 178124
  have htrace : WordTrace (prefixWord ++ tailWord_178124) baseStart_178124 baseEnd_178124 := by
    simpa [prefixWord, tailWord_178124, baseEnd_178124] using wordTrace_append hprefix tailTrace_178124
  have hstable : (prefixWord ++ tailWord_178124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178124).length < 2 ^ (prefixWord ++ tailWord_178124).sum := by decide
  have hdescent : baseEnd_178124 < baseStart_178124 := by decide
  rcases family_descends (prefixWord ++ tailWord_178124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178141 : List Nat := [1, 4, 3, 1, 3, 2, 5]
def baseStart_178141 : Nat := 118140960795 + 178141 * 2 ^ 59
def prefixEnd_178141 : Nat := 4983230072969 + 3 ^ 40 * 178141 * 2
def baseEnd_178141 : Nat := 18068534769914618512247

theorem tailTrace_178141 : CollatzResearch.WordTrace tailWord_178141 prefixEnd_178141 18068534769914618512247 := by
  unfold tailWord_178141
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497336047633055905726277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4331557365088703937150851 6497336047633055905726277)
  ·
    refine ⟨1218250508931197982323677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6497336047633055905726277 1218250508931197982323677)
    ·
      refine ⟨456843940849199243371379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1218250508931197982323677 456843940849199243371379)
      ·
        refine ⟨685265911273798865057069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456843940849199243371379 685265911273798865057069)
        ·
          refine ⟨256974716727674574396401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 685265911273798865057069 256974716727674574396401)
          ·
            refine ⟨192731037545755930797301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256974716727674574396401 192731037545755930797301)
            ·
              refine ⟨18068534769914618512247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192731037545755930797301 18068534769914618512247)
              ·
                rfl

theorem cell19_178141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_178141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178141 prefixEnd_178141 := by exact prefixLift 178141
  have htrace : WordTrace (prefixWord ++ tailWord_178141) baseStart_178141 baseEnd_178141 := by
    simpa [prefixWord, tailWord_178141, baseEnd_178141] using wordTrace_append hprefix tailTrace_178141
  have hstable : (prefixWord ++ tailWord_178141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178141).length < 2 ^ (prefixWord ++ tailWord_178141).sum := by decide
  have hdescent : baseEnd_178141 < baseStart_178141 := by decide
  rcases family_descends (prefixWord ++ tailWord_178141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178143 : List Nat := [1, 1, 2, 3, 4, 3, 5]
def baseStart_178143 : Nat := 118140960795 + 178143 * 2 ^ 59
def prefixEnd_178143 : Nat := 4983230072969 + 3 ^ 40 * 178143 * 2
def baseEnd_178143 : Nat := 18068737626469481164097

theorem tailTrace_178143 : CollatzResearch.WordTrace tailWord_178143 prefixEnd_178143 18068737626469481164097 := by
  unfold tailWord_178143
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497408993625810247299083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4331605995750540164866055 6497408993625810247299083)
  ·
    refine ⟨9746113490438715370948625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6497408993625810247299083 9746113490438715370948625)
    ·
      refine ⟨7309585117829036528211469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9746113490438715370948625 7309585117829036528211469)
      ·
        refine ⟨2741094419185888698079301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7309585117829036528211469 2741094419185888698079301)
        ·
          refine ⟨513955203597354130889869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2741094419185888698079301 513955203597354130889869)
          ·
            refine ⟨192733201349007799083701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513955203597354130889869 192733201349007799083701)
            ·
              refine ⟨18068737626469481164097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192733201349007799083701 18068737626469481164097)
              ·
                rfl

theorem cell19_178143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_178143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178143 prefixEnd_178143 := by exact prefixLift 178143
  have htrace : WordTrace (prefixWord ++ tailWord_178143) baseStart_178143 baseEnd_178143 := by
    simpa [prefixWord, tailWord_178143, baseEnd_178143] using wordTrace_append hprefix tailTrace_178143
  have hstable : (prefixWord ++ tailWord_178143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178143).length < 2 ^ (prefixWord ++ tailWord_178143).sum := by decide
  have hdescent : baseEnd_178143 < baseStart_178143 := by decide
  rcases family_descends (prefixWord ++ tailWord_178143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178145 : List Nat := [1, 2, 3, 1, 2, 1, 9]
def baseStart_178145 : Nat := 118140960795 + 178145 * 2 ^ 59
def prefixEnd_178145 : Nat := 4983230072969 + 3 ^ 40 * 178145 * 2
def baseEnd_178145 : Nat := 18068940483024343815947

theorem tailTrace_178145 : CollatzResearch.WordTrace tailWord_178145 prefixEnd_178145 18068940483024343815947 := by
  unfold tailWord_178145
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497481939618564588871889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4331654626412376392581259 6497481939618564588871889)
  ·
    refine ⟨4873111454713923441653917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6497481939618564588871889 4873111454713923441653917)
    ·
      refine ⟨1827416795517721290620219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4873111454713923441653917 1827416795517721290620219)
      ·
        refine ⟨2741125193276581935930329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827416795517721290620219 2741125193276581935930329)
        ·
          refine ⟨2055843894957436451947747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2741125193276581935930329 2055843894957436451947747)
          ·
            refine ⟨3083765842436154677921621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055843894957436451947747 3083765842436154677921621)
            ·
              refine ⟨18068940483024343815947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3083765842436154677921621 18068940483024343815947)
              ·
                rfl

theorem cell19_178145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_178145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178145 prefixEnd_178145 := by exact prefixLift 178145
  have htrace : WordTrace (prefixWord ++ tailWord_178145) baseStart_178145 baseEnd_178145 := by
    simpa [prefixWord, tailWord_178145, baseEnd_178145] using wordTrace_append hprefix tailTrace_178145
  have hstable : (prefixWord ++ tailWord_178145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178145).length < 2 ^ (prefixWord ++ tailWord_178145).sum := by decide
  have hdescent : baseEnd_178145 < baseStart_178145 := by decide
  rcases family_descends (prefixWord ++ tailWord_178145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178196 : List Nat := [2, 4, 3, 2, 2, 6]
def baseStart_178196 : Nat := 118140960795 + 178196 * 2 ^ 59
def prefixEnd_178196 : Nat := 4983230072969 + 3 ^ 40 * 178196 * 2
def baseEnd_178196 : Nat := 6024704441724447146041

theorem tailTrace_178196 : CollatzResearch.WordTrace tailWord_178196 prefixEnd_178196 6024704441724447146041 := by
  unfold tailWord_178196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3249671031216900149489221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4332894708289200199318961 3249671031216900149489221)
  ·
    refine ⟨609313318353168778029229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3249671031216900149489221 609313318353168778029229)
    ·
      refine ⟨228492494382438291760961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 609313318353168778029229 228492494382438291760961)
      ·
        refine ⟨171369370786828718820721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228492494382438291760961 171369370786828718820721)
        ·
          refine ⟨128527028090121539115541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171369370786828718820721 128527028090121539115541)
          ·
            refine ⟨6024704441724447146041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128527028090121539115541 6024704441724447146041)
            ·
              rfl

theorem cell19_178196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 6].length) (baseStart_178196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178196 prefixEnd_178196 := by exact prefixLift 178196
  have htrace : WordTrace (prefixWord ++ tailWord_178196) baseStart_178196 baseEnd_178196 := by
    simpa [prefixWord, tailWord_178196, baseEnd_178196] using wordTrace_append hprefix tailTrace_178196
  have hstable : (prefixWord ++ tailWord_178196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178196).length < 2 ^ (prefixWord ++ tailWord_178196).sum := by decide
  have hdescent : baseEnd_178196 < baseStart_178196 := by decide
  rcases family_descends (prefixWord ++ tailWord_178196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178202 : List Nat := [3, 1, 1, 3, 1, 10]
def baseStart_178202 : Nat := 118140960795 + 178202 * 2 ^ 59
def prefixEnd_178202 : Nat := 4983230072969 + 3 ^ 40 * 178202 * 2
def baseEnd_178202 : Nat := 6024907298279309797891

theorem tailTrace_178202 : CollatzResearch.WordTrace tailWord_178202 prefixEnd_178202 6024907298279309797891 := by
  unfold tailWord_178202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624890225103015830924215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4333040600274708882464573 1624890225103015830924215)
  ·
    refine ⟨2437335337654523746386323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1624890225103015830924215 2437335337654523746386323)
    ·
      refine ⟨3656003006481785619579485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2437335337654523746386323 3656003006481785619579485)
      ·
        refine ⟨1371001127430669607342307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3656003006481785619579485 1371001127430669607342307)
        ·
          refine ⟨2056501691146004411013461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371001127430669607342307 2056501691146004411013461)
          ·
            refine ⟨6024907298279309797891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2056501691146004411013461 6024907298279309797891)
            ·
              rfl

theorem cell19_178202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_178202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178202 prefixEnd_178202 := by exact prefixLift 178202
  have htrace : WordTrace (prefixWord ++ tailWord_178202) baseStart_178202 baseEnd_178202 := by
    simpa [prefixWord, tailWord_178202, baseEnd_178202] using wordTrace_append hprefix tailTrace_178202
  have hstable : (prefixWord ++ tailWord_178202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178202).length < 2 ^ (prefixWord ++ tailWord_178202).sum := by decide
  have hdescent : baseEnd_178202 < baseStart_178202 := by decide
  rcases family_descends (prefixWord ++ tailWord_178202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178215 : List Nat := [1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_178215 : Nat := 118140960795 + 178215 * 2 ^ 59
def prefixEnd_178215 : Nat := 4983230072969 + 3 ^ 40 * 178215 * 2
def baseEnd_178215 : Nat := 54228121387333609892095

theorem tailTrace_178215 : CollatzResearch.WordTrace tailWord_178215 prefixEnd_178215 54228121387333609892095 := by
  unfold tailWord_178215
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500035049364966543920099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4333356699576644362613399 6500035049364966543920099)
  ·
    refine ⟨9750052574047449815880149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6500035049364966543920099 9750052574047449815880149)
    ·
      refine ⟨228516857204237105059691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9750052574047449815880149 228516857204237105059691)
      ·
        refine ⟨342775285806355657589537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228516857204237105059691 342775285806355657589537)
        ·
          refine ⟨257081464354766743192153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342775285806355657589537 257081464354766743192153)
          ·
            refine ⟨192811098266075057394115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257081464354766743192153 192811098266075057394115)
            ·
              refine ⟨289216647399112586091173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192811098266075057394115 289216647399112586091173)
              ·
                refine ⟨54228121387333609892095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289216647399112586091173 54228121387333609892095)
                ·
                  rfl

theorem cell19_178215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_178215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178215 prefixEnd_178215 := by exact prefixLift 178215
  have htrace : WordTrace (prefixWord ++ tailWord_178215) baseStart_178215 baseEnd_178215 := by
    simpa [prefixWord, tailWord_178215, baseEnd_178215] using wordTrace_append hprefix tailTrace_178215
  have hstable : (prefixWord ++ tailWord_178215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178215).length < 2 ^ (prefixWord ++ tailWord_178215).sum := by decide
  have hdescent : baseEnd_178215 < baseStart_178215 := by decide
  rcases family_descends (prefixWord ++ tailWord_178215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178295 : List Nat := [1, 1, 3, 1, 1, 5, 4, 3]
def baseStart_178295 : Nat := 118140960795 + 178295 * 2 ^ 59
def prefixEnd_178295 : Nat := 4983230072969 + 3 ^ 40 * 178295 * 2
def baseEnd_178295 : Nat := 54252464173917128114099

theorem tailTrace_178295 : CollatzResearch.WordTrace tailWord_178295 prefixEnd_178295 54252464173917128114099 := by
  unfold tailWord_178295
  simp only [CollatzResearch.WordTrace]
  refine ⟨6502952889075140206832339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4335301926050093471221559 6502952889075140206832339)
  ·
    refine ⟨9754429333612710310248509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6502952889075140206832339 9754429333612710310248509)
    ·
      refine ⟨3657911000104766366343191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9754429333612710310248509 3657911000104766366343191)
      ·
        refine ⟨5486866500157149549514787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657911000104766366343191 5486866500157149549514787)
        ·
          refine ⟨8230299750235724324272181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486866500157149549514787 8230299750235724324272181)
          ·
            refine ⟨771590601584599155400517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8230299750235724324272181 771590601584599155400517)
            ·
              refine ⟨144673237797112341637597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 771590601584599155400517 144673237797112341637597)
              ·
                refine ⟨54252464173917128114099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144673237797112341637597 54252464173917128114099)
                ·
                  rfl

theorem cell19_178295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_178295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178295 prefixEnd_178295 := by exact prefixLift 178295
  have htrace : WordTrace (prefixWord ++ tailWord_178295) baseStart_178295 baseEnd_178295 := by
    simpa [prefixWord, tailWord_178295, baseEnd_178295] using wordTrace_append hprefix tailTrace_178295
  have hstable : (prefixWord ++ tailWord_178295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178295).length < 2 ^ (prefixWord ++ tailWord_178295).sum := by decide
  have hdescent : baseEnd_178295 < baseStart_178295 := by decide
  rcases family_descends (prefixWord ++ tailWord_178295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178314 : List Nat := [3, 1, 2, 3, 1, 4, 5]
def baseStart_178314 : Nat := 118140960795 + 178314 * 2 ^ 59
def prefixEnd_178314 : Nat := 4983230072969 + 3 ^ 40 * 178314 * 2
def baseEnd_178314 : Nat := 18086081861910237897275

theorem tailTrace_178314 : CollatzResearch.WordTrace tailWord_178314 prefixEnd_178314 18086081861910237897275 := by
  unfold tailWord_178314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625911469001576612943499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4335763917337537634515997 1625911469001576612943499)
  ·
    refine ⟨2438867203502364919415249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1625911469001576612943499 2438867203502364919415249)
    ·
      refine ⟨1829150402626773689561437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2438867203502364919415249 1829150402626773689561437)
      ·
        refine ⟨685931400985040133585539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1829150402626773689561437 685931400985040133585539)
        ·
          refine ⟨1028897101477560200378309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685931400985040133585539 1028897101477560200378309)
          ·
            refine ⟨192918206527042537570933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1028897101477560200378309 192918206527042537570933)
            ·
              refine ⟨18086081861910237897275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192918206527042537570933 18086081861910237897275)
              ·
                rfl

theorem cell19_178314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_178314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178314 prefixEnd_178314 := by exact prefixLift 178314
  have htrace : WordTrace (prefixWord ++ tailWord_178314) baseStart_178314 baseEnd_178314 := by
    simpa [prefixWord, tailWord_178314, baseEnd_178314] using wordTrace_append hprefix tailTrace_178314
  have hstable : (prefixWord ++ tailWord_178314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178314).length < 2 ^ (prefixWord ++ tailWord_178314).sum := by decide
  have hdescent : baseEnd_178314 < baseStart_178314 := by decide
  rcases family_descends (prefixWord ++ tailWord_178314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178333 : List Nat := [1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_178333 : Nat := 118140960795 + 178333 * 2 ^ 59
def prefixEnd_178333 : Nat := 4983230072969 + 3 ^ 40 * 178333 * 2
def baseEnd_178333 : Nat := 54264026997544299269551

theorem tailTrace_178333 : CollatzResearch.WordTrace tailWord_178333 prefixEnd_178333 54264026997544299269551 := by
  unfold tailWord_178333
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504338862937472696715653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4336225908624981797810435 6504338862937472696715653)
  ·
    refine ⟨1219563536800776130634185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6504338862937472696715653 1219563536800776130634185)
    ·
      refine ⟨914672652600582097975639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1219563536800776130634185 914672652600582097975639)
      ·
        refine ⟨1372008978900873146963459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914672652600582097975639 1372008978900873146963459)
        ·
          refine ⟨2058013468351309720445189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372008978900873146963459 2058013468351309720445189)
          ·
            refine ⟨385877525315870572583473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2058013468351309720445189 385877525315870572583473)
            ·
              refine ⟨289408143986902929437605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385877525315870572583473 289408143986902929437605)
              ·
                refine ⟨54264026997544299269551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289408143986902929437605 54264026997544299269551)
                ·
                  rfl

theorem cell19_178333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_178333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178333 prefixEnd_178333 := by exact prefixLift 178333
  have htrace : WordTrace (prefixWord ++ tailWord_178333) baseStart_178333 baseEnd_178333 := by
    simpa [prefixWord, tailWord_178333, baseEnd_178333] using wordTrace_append hprefix tailTrace_178333
  have hstable : (prefixWord ++ tailWord_178333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178333).length < 2 ^ (prefixWord ++ tailWord_178333).sum := by decide
  have hdescent : baseEnd_178333 < baseStart_178333 := by decide
  rcases family_descends (prefixWord ++ tailWord_178333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178354 : List Nat := [3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_178354 : Nat := 118140960795 + 178354 * 2 ^ 59
def prefixEnd_178354 : Nat := 4983230072969 + 3 ^ 40 * 178354 * 2
def baseEnd_178354 : Nat := 54270416979022472802827

theorem tailTrace_178354 : CollatzResearch.WordTrace tailWord_178354 prefixEnd_178354 54270416979022472802827 := by
  unfold tailWord_178354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626276198965348320807529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4336736530574262188820077 1626276198965348320807529)
  ·
    refine ⟨1219707149224011240605647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1626276198965348320807529 1219707149224011240605647)
    ·
      refine ⟨1829560723836016860908471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1219707149224011240605647 1829560723836016860908471)
      ·
        refine ⟨2744341085754025291362707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829560723836016860908471 2744341085754025291362707)
        ·
          refine ⟨4116511628631037937044061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744341085754025291362707 4116511628631037937044061)
          ·
            refine ⟨1543691860736639226391523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4116511628631037937044061 1543691860736639226391523)
            ·
              refine ⟨2315537791104958839587285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543691860736639226391523 2315537791104958839587285)
              ·
                refine ⟨54270416979022472802827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2315537791104958839587285 54270416979022472802827)
                ·
                  rfl

theorem cell19_178354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_178354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178354 prefixEnd_178354 := by exact prefixLift 178354
  have htrace : WordTrace (prefixWord ++ tailWord_178354) baseStart_178354 baseEnd_178354 := by
    simpa [prefixWord, tailWord_178354, baseEnd_178354] using wordTrace_append hprefix tailTrace_178354
  have hstable : (prefixWord ++ tailWord_178354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178354).length < 2 ^ (prefixWord ++ tailWord_178354).sum := by decide
  have hdescent : baseEnd_178354 < baseStart_178354 := by decide
  rcases family_descends (prefixWord ++ tailWord_178354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178369 : List Nat := [1, 2, 6, 1, 3, 6]
def baseStart_178369 : Nat := 118140960795 + 178369 * 2 ^ 59
def prefixEnd_178369 : Nat := 4983230072969 + 3 ^ 40 * 178369 * 2
def baseEnd_178369 : Nat := 6030553472389653607717

theorem tailTrace_178369 : CollatzResearch.WordTrace tailWord_178369 prefixEnd_178369 6030553472389653607717 := by
  unfold tailWord_178369
  simp only [CollatzResearch.WordTrace]
  refine ⟨6505651890807050845026161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4337101260538033896684107 6505651890807050845026161)
  ·
    refine ⟨4879238918105288133769621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6505651890807050845026161 4879238918105288133769621)
    ·
      refine ⟨228714324286185381270451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4879238918105288133769621 228714324286185381270451)
      ·
        refine ⟨343071486429278071905677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228714324286185381270451 343071486429278071905677)
        ·
          refine ⟨128651807410979276964629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343071486429278071905677 128651807410979276964629)
          ·
            refine ⟨6030553472389653607717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128651807410979276964629 6030553472389653607717)
            ·
              rfl

theorem cell19_178369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 6].length) (baseStart_178369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178369 prefixEnd_178369 := by exact prefixLift 178369
  have htrace : WordTrace (prefixWord ++ tailWord_178369) baseStart_178369 baseEnd_178369 := by
    simpa [prefixWord, tailWord_178369, baseEnd_178369] using wordTrace_append hprefix tailTrace_178369
  have hstable : (prefixWord ++ tailWord_178369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178369).length < 2 ^ (prefixWord ++ tailWord_178369).sum := by decide
  have hdescent : baseEnd_178369 < baseStart_178369 := by decide
  rcases family_descends (prefixWord ++ tailWord_178369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178407 : List Nat := [1, 1, 5, 3, 1, 2, 3, 3]
def baseStart_178407 : Nat := 118140960795 + 178407 * 2 ^ 59
def prefixEnd_178407 : Nat := 4983230072969 + 3 ^ 40 * 178407 * 2
def baseEnd_178407 : Nat := 54286544075134053624905

theorem tailTrace_178407 : CollatzResearch.WordTrace tailWord_178407 prefixEnd_178407 54286544075134053624905 := by
  unfold tailWord_178407
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507037864669383334909475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4338025243112922223272983 6507037864669383334909475)
  ·
    refine ⟨9760556797004075002364213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6507037864669383334909475 9760556797004075002364213)
    ·
      refine ⟨915052199719132031471645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9760556797004075002364213 915052199719132031471645)
      ·
        refine ⟨343144574894674511801867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 915052199719132031471645 343144574894674511801867)
        ·
          refine ⟨514716862342011767702801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343144574894674511801867 514716862342011767702801)
          ·
            refine ⟨386037646756508825777101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514716862342011767702801 386037646756508825777101)
            ·
              refine ⟨144764117533690809666413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386037646756508825777101 144764117533690809666413)
              ·
                refine ⟨54286544075134053624905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144764117533690809666413 54286544075134053624905)
                ·
                  rfl

theorem cell19_178407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_178407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178407 prefixEnd_178407 := by exact prefixLift 178407
  have htrace : WordTrace (prefixWord ++ tailWord_178407) baseStart_178407 baseEnd_178407 := by
    simpa [prefixWord, tailWord_178407, baseEnd_178407] using wordTrace_append hprefix tailTrace_178407
  have hstable : (prefixWord ++ tailWord_178407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178407).length < 2 ^ (prefixWord ++ tailWord_178407).sum := by decide
  have hdescent : baseEnd_178407 < baseStart_178407 := by decide
  rcases family_descends (prefixWord ++ tailWord_178407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178462 : List Nat := [4, 3, 2, 1, 1, 1, 4, 3]
def baseStart_178462 : Nat := 118140960795 + 178462 * 2 ^ 59
def prefixEnd_178462 : Nat := 4983230072969 + 3 ^ 40 * 178462 * 2
def baseEnd_178462 : Nat := 54303279740910222402533

theorem tailTrace_178462 : CollatzResearch.WordTrace tailWord_178462 prefixEnd_178462 54303279740910222402533 := by
  unfold tailWord_178462
  simp only [CollatzResearch.WordTrace]
  refine ⟨813630484933765966020205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4339362586313418485441093 813630484933765966020205)
  ·
    refine ⟨305111431850162237257577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 813630484933765966020205 305111431850162237257577)
    ·
      refine ⟨228833573887621677943183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305111431850162237257577 228833573887621677943183)
      ·
        refine ⟨343250360831432516914775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228833573887621677943183 343250360831432516914775)
        ·
          refine ⟨514875541247148775372163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343250360831432516914775 514875541247148775372163)
          ·
            refine ⟨772313311870723163058245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514875541247148775372163 772313311870723163058245)
            ·
              refine ⟨144808745975760593073421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 772313311870723163058245 144808745975760593073421)
              ·
                refine ⟨54303279740910222402533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144808745975760593073421 54303279740910222402533)
                ·
                  rfl

theorem cell19_178462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_178462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178462 prefixEnd_178462 := by exact prefixLift 178462
  have htrace : WordTrace (prefixWord ++ tailWord_178462) baseStart_178462 baseEnd_178462 := by
    simpa [prefixWord, tailWord_178462, baseEnd_178462] using wordTrace_append hprefix tailTrace_178462
  have hstable : (prefixWord ++ tailWord_178462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178462).length < 2 ^ (prefixWord ++ tailWord_178462).sum := by decide
  have hdescent : baseEnd_178462 < baseStart_178462 := by decide
  rcases family_descends (prefixWord ++ tailWord_178462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178464 : List Nat := [2, 1, 1, 5, 2, 3, 2, 3]
def baseStart_178464 : Nat := 118140960795 + 178464 * 2 ^ 59
def prefixEnd_178464 : Nat := 4983230072969 + 3 ^ 40 * 178464 * 2
def baseEnd_178464 : Nat := 54303888310574810358083

theorem tailTrace_178464 : CollatzResearch.WordTrace tailWord_178464 prefixEnd_178464 54303888310574810358083 := by
  unfold tailWord_178464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254558412731441034867223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4339411216975254713156297 3254558412731441034867223)
  ·
    refine ⟨4881837619097161552300835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254558412731441034867223 4881837619097161552300835)
    ·
      refine ⟨7322756428645742328451253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881837619097161552300835 7322756428645742328451253)
      ·
        refine ⟨686508415185538343292305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7322756428645742328451253 686508415185538343292305)
        ·
          refine ⟨514881311389153757469229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686508415185538343292305 514881311389153757469229)
          ·
            refine ⟨193080491770932659050961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514881311389153757469229 193080491770932659050961)
            ·
              refine ⟨144810368828199494288221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193080491770932659050961 144810368828199494288221)
              ·
                refine ⟨54303888310574810358083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144810368828199494288221 54303888310574810358083)
                ·
                  rfl

theorem cell19_178464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_178464 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178464 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178464 prefixEnd_178464 := by exact prefixLift 178464
  have htrace : WordTrace (prefixWord ++ tailWord_178464) baseStart_178464 baseEnd_178464 := by
    simpa [prefixWord, tailWord_178464, baseEnd_178464] using wordTrace_append hprefix tailTrace_178464
  have hstable : (prefixWord ++ tailWord_178464).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178464).length < 2 ^ (prefixWord ++ tailWord_178464).sum := by decide
  have hdescent : baseEnd_178464 < baseStart_178464 := by decide
  rcases family_descends (prefixWord ++ tailWord_178464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178466 : List Nat := [3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_178466 : Nat := 118140960795 + 178466 * 2 ^ 59
def prefixEnd_178466 : Nat := 4983230072969 + 3 ^ 40 * 178466 * 2
def baseEnd_178466 : Nat := 54304496880239398313633

theorem tailTrace_178466 : CollatzResearch.WordTrace tailWord_178466 prefixEnd_178466 54304496880239398313633 := by
  unfold tailWord_178466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627297442863909102826813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4339459847637090940871501 1627297442863909102826813)
  ·
    refine ⟨610236541073965913560055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1627297442863909102826813 610236541073965913560055)
    ·
      refine ⟨915354811610948870340083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610236541073965913560055 915354811610948870340083)
      ·
        refine ⟨1373032217416423305510125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915354811610948870340083 1373032217416423305510125)
        ·
          refine ⟨514887081531158739566297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1373032217416423305510125 514887081531158739566297)
          ·
            refine ⟨386165311148369054674723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514887081531158739566297 386165311148369054674723)
            ·
              refine ⟨579247966722553582012085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386165311148369054674723 579247966722553582012085)
              ·
                refine ⟨54304496880239398313633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 579247966722553582012085 54304496880239398313633)
                ·
                  rfl

theorem cell19_178466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_178466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178466 prefixEnd_178466 := by exact prefixLift 178466
  have htrace : WordTrace (prefixWord ++ tailWord_178466) baseStart_178466 baseEnd_178466 := by
    simpa [prefixWord, tailWord_178466, baseEnd_178466] using wordTrace_append hprefix tailTrace_178466
  have hstable : (prefixWord ++ tailWord_178466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178466).length < 2 ^ (prefixWord ++ tailWord_178466).sum := by decide
  have hdescent : baseEnd_178466 < baseStart_178466 := by decide
  rcases family_descends (prefixWord ++ tailWord_178466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178561 : List Nat := [1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_178561 : Nat := 118140960795 + 178561 * 2 ^ 59
def prefixEnd_178561 : Nat := 4983230072969 + 3 ^ 40 * 178561 * 2
def baseEnd_178561 : Nat := 54333403939307326202263

theorem tailTrace_178561 : CollatzResearch.WordTrace tailWord_178561 prefixEnd_178561 54333403939307326202263 := by
  unfold tailWord_178561
  simp only [CollatzResearch.WordTrace]
  refine ⟨6512654706111467636015537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4341769804074311757343691 6512654706111467636015537)
  ·
    refine ⟨4884491029583600727011653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6512654706111467636015537 4884491029583600727011653)
    ·
      refine ⟨915842068046925136314685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4884491029583600727011653 915842068046925136314685)
      ·
        refine ⟨343440775517596926118007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 915842068046925136314685 343440775517596926118007)
        ·
          refine ⟨515161163276395389177011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343440775517596926118007 515161163276395389177011)
          ·
            refine ⟨772741744914593083765517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515161163276395389177011 772741744914593083765517)
            ·
              refine ⟨289778154342972406412069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 772741744914593083765517 289778154342972406412069)
              ·
                refine ⟨54333403939307326202263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289778154342972406412069 54333403939307326202263)
                ·
                  rfl

theorem cell19_178561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_178561 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178561 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178561 prefixEnd_178561 := by exact prefixLift 178561
  have htrace : WordTrace (prefixWord ++ tailWord_178561) baseStart_178561 baseEnd_178561 := by
    simpa [prefixWord, tailWord_178561, baseEnd_178561] using wordTrace_append hprefix tailTrace_178561
  have hstable : (prefixWord ++ tailWord_178561).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178561).length < 2 ^ (prefixWord ++ tailWord_178561).sum := by decide
  have hdescent : baseEnd_178561 < baseStart_178561 := by decide
  rcases family_descends (prefixWord ++ tailWord_178561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178755 : List Nat := [1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_178755 : Nat := 118140960795 + 178755 * 2 ^ 59
def prefixEnd_178755 : Nat := 4983230072969 + 3 ^ 40 * 178755 * 2
def baseEnd_178755 : Nat := 54392435196772357890623

theorem tailTrace_178755 : CollatzResearch.WordTrace tailWord_178755 prefixEnd_178755 54392435196772357890623 := by
  unfold tailWord_178755
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519730467408638768577719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4346486978272425845718479 6519730467408638768577719)
  ·
    refine ⟨9779595701112958152866579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6519730467408638768577719 9779595701112958152866579)
    ·
      refine ⟨14669393551669437229299869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9779595701112958152866579 14669393551669437229299869)
      ·
        refine ⟨5501022581876038960987451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14669393551669437229299869 5501022581876038960987451)
        ·
          refine ⟨8251533872814058441481177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501022581876038960987451 8251533872814058441481177)
          ·
            refine ⟨6188650404610543831110883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8251533872814058441481177 6188650404610543831110883)
            ·
              refine ⟨9282975606915815746666325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188650404610543831110883 9282975606915815746666325)
              ·
                refine ⟨54392435196772357890623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9282975606915815746666325 54392435196772357890623)
                ·
                  rfl

theorem cell19_178755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_178755 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178755 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178755 prefixEnd_178755 := by exact prefixLift 178755
  have htrace : WordTrace (prefixWord ++ tailWord_178755) baseStart_178755 baseEnd_178755 := by
    simpa [prefixWord, tailWord_178755, baseEnd_178755] using wordTrace_append hprefix tailTrace_178755
  have hstable : (prefixWord ++ tailWord_178755).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178755).length < 2 ^ (prefixWord ++ tailWord_178755).sum := by decide
  have hdescent : baseEnd_178755 < baseStart_178755 := by decide
  rcases family_descends (prefixWord ++ tailWord_178755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178772 : List Nat := [2, 4, 1, 1, 1, 4, 6]
def baseStart_178772 : Nat := 118140960795 + 178772 * 2 ^ 59
def prefixEnd_178772 : Nat := 4983230072969 + 3 ^ 40 * 178772 * 2
def baseEnd_178772 : Nat := 18132536012973785170933

theorem tailTrace_178772 : CollatzResearch.WordTrace tailWord_178772 prefixEnd_178772 18132536012973785170933 := by
  unfold tailWord_178772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260175254173525335973285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4346900338898033781297713 3260175254173525335973285)
  ·
    refine ⟨611282860157536000494991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3260175254173525335973285 611282860157536000494991)
    ·
      refine ⟨916924290236304000742487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611282860157536000494991 916924290236304000742487)
      ·
        refine ⟨1375386435354456001113731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916924290236304000742487 1375386435354456001113731)
        ·
          refine ⟨2063079653031684001670597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375386435354456001113731 2063079653031684001670597)
          ·
            refine ⟨386827434943440750313237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2063079653031684001670597 386827434943440750313237)
            ·
              refine ⟨18132536012973785170933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 386827434943440750313237 18132536012973785170933)
              ·
                rfl

theorem cell19_178772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_178772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178772 prefixEnd_178772 := by exact prefixLift 178772
  have htrace : WordTrace (prefixWord ++ tailWord_178772) baseStart_178772 baseEnd_178772 := by
    simpa [prefixWord, tailWord_178772, baseEnd_178772] using wordTrace_append hprefix tailTrace_178772
  have hstable : (prefixWord ++ tailWord_178772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178772).length < 2 ^ (prefixWord ++ tailWord_178772).sum := by decide
  have hdescent : baseEnd_178772 < baseStart_178772 := by decide
  rcases family_descends (prefixWord ++ tailWord_178772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178793 : List Nat := [1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_178793 : Nat := 118140960795 + 178793 * 2 ^ 59
def prefixEnd_178793 : Nat := 4983230072969 + 3 ^ 40 * 178793 * 2
def baseEnd_178793 : Nat := 54403998020399529046075

theorem tailTrace_178793 : CollatzResearch.WordTrace tailWord_178793 prefixEnd_178793 54403998020399529046075 := by
  unfold tailWord_178793
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521116441270971258461033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4347410960847314172307355 6521116441270971258461033)
  ·
    refine ⟨4890837330953228443845775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6521116441270971258461033 4890837330953228443845775)
    ·
      refine ⟨7336255996429842665768663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4890837330953228443845775 7336255996429842665768663)
      ·
        refine ⟨11004383994644763998652995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7336255996429842665768663 11004383994644763998652995)
        ·
          refine ⟨16506575991967145997979493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11004383994644763998652995 16506575991967145997979493)
          ·
            refine ⟨3094982998493839874621155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16506575991967145997979493 3094982998493839874621155)
            ·
              refine ⟨4642474497740759811931733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094982998493839874621155 4642474497740759811931733)
              ·
                refine ⟨54403998020399529046075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4642474497740759811931733 54403998020399529046075)
                ·
                  rfl

theorem cell19_178793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_178793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178793 prefixEnd_178793 := by exact prefixLift 178793
  have htrace : WordTrace (prefixWord ++ tailWord_178793) baseStart_178793 baseEnd_178793 := by
    simpa [prefixWord, tailWord_178793, baseEnd_178793] using wordTrace_append hprefix tailTrace_178793
  have hstable : (prefixWord ++ tailWord_178793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178793).length < 2 ^ (prefixWord ++ tailWord_178793).sum := by decide
  have hdescent : baseEnd_178793 < baseStart_178793 := by decide
  rcases family_descends (prefixWord ++ tailWord_178793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178846 : List Nat := [4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_178846 : Nat := 118140960795 + 178846 * 2 ^ 59
def prefixEnd_178846 : Nat := 4983230072969 + 3 ^ 40 * 178846 * 2
def baseEnd_178846 : Nat := 54420125116511109868153

theorem tailTrace_178846 : CollatzResearch.WordTrace tailWord_178846 prefixEnd_178846 54420125116511109868153 := by
  unfold tailWord_178846
  simp only [CollatzResearch.WordTrace]
  refine ⟨815381188759870163767549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4348699673385974206760261 815381188759870163767549)
  ·
    refine ⟨305767945784951311412831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 815381188759870163767549 305767945784951311412831)
    ·
      refine ⟨458651918677426967119247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305767945784951311412831 458651918677426967119247)
      ·
        refine ⟨687977878016140450678871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458651918677426967119247 687977878016140450678871)
        ·
          refine ⟨1031966817024210676018307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687977878016140450678871 1031966817024210676018307)
          ·
            refine ⟨1547950225536316014027461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031966817024210676018307 1547950225536316014027461)
            ·
              refine ⟨290240667288059252630149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1547950225536316014027461 290240667288059252630149)
              ·
                refine ⟨54420125116511109868153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290240667288059252630149 54420125116511109868153)
                ·
                  rfl

theorem cell19_178846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_178846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178846 prefixEnd_178846 := by exact prefixLift 178846
  have htrace : WordTrace (prefixWord ++ tailWord_178846) baseStart_178846 baseEnd_178846 := by
    simpa [prefixWord, tailWord_178846, baseEnd_178846] using wordTrace_append hprefix tailTrace_178846
  have hstable : (prefixWord ++ tailWord_178846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178846).length < 2 ^ (prefixWord ++ tailWord_178846).sum := by decide
  have hdescent : baseEnd_178846 < baseStart_178846 := by decide
  rcases family_descends (prefixWord ++ tailWord_178846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178888 : List Nat := [2, 1, 3, 1, 2, 10]
def baseStart_178888 : Nat := 118140960795 + 178888 * 2 ^ 59
def prefixEnd_178888 : Nat := 4983230072969 + 3 ^ 40 * 178888 * 2
def baseEnd_178888 : Nat := 6048100564385272992745

theorem tailTrace_178888 : CollatzResearch.WordTrace tailWord_178888 prefixEnd_178888 6048100564385272992745 := by
  unfold tailWord_178888
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262290687963401241584659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4349720917284534988779545 3262290687963401241584659)
  ·
    refine ⟨4893436031945101862376989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262290687963401241584659 4893436031945101862376989)
    ·
      refine ⟨1835038511979413198391371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4893436031945101862376989 1835038511979413198391371)
      ·
        refine ⟨2752557767969119797587057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835038511979413198391371 2752557767969119797587057)
        ·
          refine ⟨2064418325976839848190293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2752557767969119797587057 2064418325976839848190293)
          ·
            refine ⟨6048100564385272992745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2064418325976839848190293 6048100564385272992745)
            ·
              rfl

theorem cell19_178888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_178888 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178888 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178888 prefixEnd_178888 := by exact prefixLift 178888
  have htrace : WordTrace (prefixWord ++ tailWord_178888) baseStart_178888 baseEnd_178888 := by
    simpa [prefixWord, tailWord_178888, baseEnd_178888] using wordTrace_append hprefix tailTrace_178888
  have hstable : (prefixWord ++ tailWord_178888).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178888).length < 2 ^ (prefixWord ++ tailWord_178888).sum := by decide
  have hdescent : baseEnd_178888 < baseStart_178888 := by decide
  rcases family_descends (prefixWord ++ tailWord_178888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178901 : List Nat := [1, 3, 2, 5, 1, 2, 1, 4]
def baseStart_178901 : Nat := 118140960795 + 178901 * 2 ^ 59
def prefixEnd_178901 : Nat := 4983230072969 + 3 ^ 40 * 178901 * 2
def baseEnd_178901 : Nat := 54436860782287278645781

theorem tailTrace_178901 : CollatzResearch.WordTrace tailWord_178901 prefixEnd_178901 54436860782287278645781 := by
  unfold tailWord_178901
  simp only [CollatzResearch.WordTrace]
  refine ⟨6525055524879705703392557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4350037016586470468928371 6525055524879705703392557)
  ·
    refine ⟨2446895821829889638772209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6525055524879705703392557 2446895821829889638772209)
    ·
      refine ⟨1835171866372417229079157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2446895821829889638772209 1835171866372417229079157)
      ·
        refine ⟨172047362472414115226171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1835171866372417229079157 172047362472414115226171)
        ·
          refine ⟨258071043708621172839257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172047362472414115226171 258071043708621172839257)
          ·
            refine ⟨193553282781465879629443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258071043708621172839257 193553282781465879629443)
            ·
              refine ⟨290329924172198819444165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193553282781465879629443 290329924172198819444165)
              ·
                refine ⟨54436860782287278645781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290329924172198819444165 54436860782287278645781)
                ·
                  rfl

theorem cell19_178901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_178901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178901 prefixEnd_178901 := by exact prefixLift 178901
  have htrace : WordTrace (prefixWord ++ tailWord_178901) baseStart_178901 baseEnd_178901 := by
    simpa [prefixWord, tailWord_178901, baseEnd_178901] using wordTrace_append hprefix tailTrace_178901
  have hstable : (prefixWord ++ tailWord_178901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178901).length < 2 ^ (prefixWord ++ tailWord_178901).sum := by decide
  have hdescent : baseEnd_178901 < baseStart_178901 := by decide
  rcases family_descends (prefixWord ++ tailWord_178901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178996 : List Nat := [2, 5, 1, 1, 4, 1, 5]
def baseStart_178996 : Nat := 118140960795 + 178996 * 2 ^ 59
def prefixEnd_178996 : Nat := 4983230072969 + 3 ^ 40 * 178996 * 2
def baseEnd_178996 : Nat := 18155255947118402178137

theorem tailTrace_178996 : CollatzResearch.WordTrace tailWord_178996 prefixEnd_178996 18155255947118402178137 := by
  unfold tailWord_178996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264260229767768464050421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4352346973023691285400561 3264260229767768464050421)
  ·
    refine ⟨306024396540728293504727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3264260229767768464050421 306024396540728293504727)
    ·
      refine ⟨459036594811092440257091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306024396540728293504727 459036594811092440257091)
      ·
        refine ⟨688554892216638660385637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459036594811092440257091 688554892216638660385637)
        ·
          refine ⟨129104042290619748822307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 688554892216638660385637 129104042290619748822307)
          ·
            refine ⟨193656063435929623233461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129104042290619748822307 193656063435929623233461)
            ·
              refine ⟨18155255947118402178137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193656063435929623233461 18155255947118402178137)
              ·
                rfl

theorem cell19_178996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_178996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_178996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_178996 prefixEnd_178996 := by exact prefixLift 178996
  have htrace : WordTrace (prefixWord ++ tailWord_178996) baseStart_178996 baseEnd_178996 := by
    simpa [prefixWord, tailWord_178996, baseEnd_178996] using wordTrace_append hprefix tailTrace_178996
  have hstable : (prefixWord ++ tailWord_178996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178996).length < 2 ^ (prefixWord ++ tailWord_178996).sum := by decide
  have hdescent : baseEnd_178996 < baseStart_178996 := by decide
  rcases family_descends (prefixWord ++ tailWord_178996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179040 : List Nat := [2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_179040 : Nat := 118140960795 + 179040 * 2 ^ 59
def prefixEnd_179040 : Nat := 4983230072969 + 3 ^ 40 * 179040 * 2
def baseEnd_179040 : Nat := 54479156373976141556513

theorem tailTrace_179040 : CollatzResearch.WordTrace tailWord_179040 prefixEnd_179040 54479156373976141556513 := by
  unfold tailWord_179040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265062635688066221351287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4353416847584088295135049 3265062635688066221351287)
  ·
    refine ⟨4897593953532099332026931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3265062635688066221351287 4897593953532099332026931)
    ·
      refine ⟨7346390930298148998040397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4897593953532099332026931 7346390930298148998040397)
      ·
        refine ⟨2754896598861805874265149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7346390930298148998040397 2754896598861805874265149)
        ·
          refine ⟨1033086224573177202849431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2754896598861805874265149 1033086224573177202849431)
          ·
            refine ⟨1549629336859765804274147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033086224573177202849431 1549629336859765804274147)
            ·
              refine ⟨2324444005289648706411221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549629336859765804274147 2324444005289648706411221)
              ·
                refine ⟨54479156373976141556513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2324444005289648706411221 54479156373976141556513)
                ·
                  rfl

theorem cell19_179040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_179040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179040 prefixEnd_179040 := by exact prefixLift 179040
  have htrace : WordTrace (prefixWord ++ tailWord_179040) baseStart_179040 baseEnd_179040 := by
    simpa [prefixWord, tailWord_179040, baseEnd_179040] using wordTrace_append hprefix tailTrace_179040
  have hstable : (prefixWord ++ tailWord_179040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179040).length < 2 ^ (prefixWord ++ tailWord_179040).sum := by decide
  have hdescent : baseEnd_179040 < baseStart_179040 := by decide
  rcases family_descends (prefixWord ++ tailWord_179040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179070 : List Nat := [4, 2, 3, 1, 3, 1, 1, 4]
def baseStart_179070 : Nat := 118140960795 + 179070 * 2 ^ 59
def prefixEnd_179070 : Nat := 4983230072969 + 3 ^ 40 * 179070 * 2
def baseEnd_179070 : Nat := 54488284918944960889765

theorem tailTrace_179070 : CollatzResearch.WordTrace tailWord_179070 prefixEnd_179070 54488284918944960889765 := by
  unfold tailWord_179070
  simp only [CollatzResearch.WordTrace]
  refine ⟨816402432658430945786833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4354146307511631710863109 816402432658430945786833)
  ·
    refine ⟨612301824493823209340125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816402432658430945786833 612301824493823209340125)
    ·
      refine ⟨229613184185183703502547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 612301824493823209340125 229613184185183703502547)
      ·
        refine ⟨344419776277775555253821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229613184185183703502547 344419776277775555253821)
        ·
          refine ⟨129157416104165833220183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344419776277775555253821 129157416104165833220183)
          ·
            refine ⟨193736124156248749830275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129157416104165833220183 193736124156248749830275)
            ·
              refine ⟨290604186234373124745413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193736124156248749830275 290604186234373124745413)
              ·
                refine ⟨54488284918944960889765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290604186234373124745413 54488284918944960889765)
                ·
                  rfl

theorem cell19_179070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_179070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179070 prefixEnd_179070 := by exact prefixLift 179070
  have htrace : WordTrace (prefixWord ++ tailWord_179070) baseStart_179070 baseEnd_179070 := by
    simpa [prefixWord, tailWord_179070, baseEnd_179070] using wordTrace_append hprefix tailTrace_179070
  have hstable : (prefixWord ++ tailWord_179070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179070).length < 2 ^ (prefixWord ++ tailWord_179070).sum := by decide
  have hdescent : baseEnd_179070 < baseStart_179070 := by decide
  rcases family_descends (prefixWord ++ tailWord_179070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179095 : List Nat := [1, 1, 3, 3, 1, 2, 5, 3]
def baseStart_179095 : Nat := 118140960795 + 179095 * 2 ^ 59
def prefixEnd_179095 : Nat := 4983230072969 + 3 ^ 40 * 179095 * 2
def baseEnd_179095 : Nat := 54495892039752310334141

theorem tailTrace_179095 : CollatzResearch.WordTrace tailWord_179095 prefixEnd_179095 54495892039752310334141 := by
  unfold tailWord_179095
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532131286176876835954739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4354754190784584557303159 6532131286176876835954739)
  ·
    refine ⟨9798196929265315253932109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6532131286176876835954739 9798196929265315253932109)
    ·
      refine ⟨3674323848474493220224541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9798196929265315253932109 3674323848474493220224541)
      ·
        refine ⟨1377871443177934957584203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3674323848474493220224541 1377871443177934957584203)
        ·
          refine ⟨2066807164766902436376305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377871443177934957584203 2066807164766902436376305)
          ·
            refine ⟨1550105373575176827282229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2066807164766902436376305 1550105373575176827282229)
            ·
              refine ⟨145322378772672827557709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1550105373575176827282229 145322378772672827557709)
              ·
                refine ⟨54495892039752310334141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145322378772672827557709 54495892039752310334141)
                ·
                  rfl

theorem cell19_179095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_179095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179095 prefixEnd_179095 := by exact prefixLift 179095
  have htrace : WordTrace (prefixWord ++ tailWord_179095) baseStart_179095 baseEnd_179095 := by
    simpa [prefixWord, tailWord_179095, baseEnd_179095] using wordTrace_append hprefix tailTrace_179095
  have hstable : (prefixWord ++ tailWord_179095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179095).length < 2 ^ (prefixWord ++ tailWord_179095).sum := by decide
  have hdescent : baseEnd_179095 < baseStart_179095 := by decide
  rcases family_descends (prefixWord ++ tailWord_179095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179142 : List Nat := [6, 1, 3, 1, 1, 2, 2, 3]
def baseStart_179142 : Nat := 118140960795 + 179142 * 2 ^ 59
def prefixEnd_179142 : Nat := 4983230072969 + 3 ^ 40 * 179142 * 2
def baseEnd_179142 : Nat := 54510193426870127289569

theorem tailTrace_179142 : CollatzResearch.WordTrace tailWord_179142 prefixEnd_179142 54510193426870127289569 := by
  unfold tailWord_179142
  simp only [CollatzResearch.WordTrace]
  refine ⟨204182672406456370716115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4355897011337735908610453 204182672406456370716115)
  ·
    refine ⟨306274008609684556074173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204182672406456370716115 306274008609684556074173)
    ·
      refine ⟨114852753228631708527815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306274008609684556074173 114852753228631708527815)
      ·
        refine ⟨172279129842947562791723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114852753228631708527815 172279129842947562791723)
        ·
          refine ⟨258418694764421344187585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172279129842947562791723 258418694764421344187585)
          ·
            refine ⟨193814021073316008140689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258418694764421344187585 193814021073316008140689)
            ·
              refine ⟨145360515804987006105517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193814021073316008140689 145360515804987006105517)
              ·
                refine ⟨54510193426870127289569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145360515804987006105517 54510193426870127289569)
                ·
                  rfl

theorem cell19_179142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_179142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179142 prefixEnd_179142 := by exact prefixLift 179142
  have htrace : WordTrace (prefixWord ++ tailWord_179142) baseStart_179142 baseEnd_179142 := by
    simpa [prefixWord, tailWord_179142, baseEnd_179142] using wordTrace_append hprefix tailTrace_179142
  have hstable : (prefixWord ++ tailWord_179142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179142).length < 2 ^ (prefixWord ++ tailWord_179142).sum := by decide
  have hdescent : baseEnd_179142 < baseStart_179142 := by decide
  rcases family_descends (prefixWord ++ tailWord_179142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179150 : List Nat := [4, 1, 1, 1, 2, 5, 2, 3]
def baseStart_179150 : Nat := 118140960795 + 179150 * 2 ^ 59
def prefixEnd_179150 : Nat := 4983230072969 + 3 ^ 40 * 179150 * 2
def baseEnd_179150 : Nat := 54512627705528479111769

theorem tailTrace_179150 : CollatzResearch.WordTrace tailWord_179150 prefixEnd_179150 54512627705528479111769 := by
  unfold tailWord_179150
  simp only [CollatzResearch.WordTrace]
  refine ⟨816767162622202653650863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4356091533985080819471269 816767162622202653650863)
  ·
    refine ⟨1225150743933303980476295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816767162622202653650863 1225150743933303980476295)
    ·
      refine ⟨1837726115899955970714443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1225150743933303980476295 1837726115899955970714443)
      ·
        refine ⟨2756589173849933956071665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837726115899955970714443 2756589173849933956071665)
        ·
          refine ⟨2067441880387450467053749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2756589173849933956071665 2067441880387450467053749)
          ·
            refine ⟨193822676286323481286289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2067441880387450467053749 193822676286323481286289)
            ·
              refine ⟨145367007214742610964717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193822676286323481286289 145367007214742610964717)
              ·
                refine ⟨54512627705528479111769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145367007214742610964717 54512627705528479111769)
                ·
                  rfl

theorem cell19_179150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_179150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179150 prefixEnd_179150 := by exact prefixLift 179150
  have htrace : WordTrace (prefixWord ++ tailWord_179150) baseStart_179150 baseEnd_179150 := by
    simpa [prefixWord, tailWord_179150, baseEnd_179150] using wordTrace_append hprefix tailTrace_179150
  have hstable : (prefixWord ++ tailWord_179150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179150).length < 2 ^ (prefixWord ++ tailWord_179150).sum := by decide
  have hdescent : baseEnd_179150 < baseStart_179150 := by decide
  rcases family_descends (prefixWord ++ tailWord_179150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179190 : List Nat := [5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_179190 : Nat := 118140960795 + 179190 * 2 ^ 59
def prefixEnd_179190 : Nat := 4983230072969 + 3 ^ 40 * 179190 * 2
def baseEnd_179190 : Nat := 54524799098820238222771

theorem tailTrace_179190 : CollatzResearch.WordTrace tailWord_179190 prefixEnd_179190 54524799098820238222771 := by
  unfold tailWord_179190
  simp only [CollatzResearch.WordTrace]
  refine ⟨408474763802044253791439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4357064147221805373775349 408474763802044253791439)
  ·
    refine ⟨612712145703066380687159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 408474763802044253791439 612712145703066380687159)
    ·
      refine ⟨919068218554599571030739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612712145703066380687159 919068218554599571030739)
      ·
        refine ⟨1378602327831899356546109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919068218554599571030739 1378602327831899356546109)
        ·
          refine ⟨516975872936962258704791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1378602327831899356546109 516975872936962258704791)
          ·
            refine ⟨775463809405443388057187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516975872936962258704791 775463809405443388057187)
            ·
              refine ⟨1163195714108165082085781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775463809405443388057187 1163195714108165082085781)
              ·
                refine ⟨54524799098820238222771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1163195714108165082085781 54524799098820238222771)
                ·
                  rfl

theorem cell19_179190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_179190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179190 prefixEnd_179190 := by exact prefixLift 179190
  have htrace : WordTrace (prefixWord ++ tailWord_179190) baseStart_179190 baseEnd_179190 := by
    simpa [prefixWord, tailWord_179190, baseEnd_179190] using wordTrace_append hprefix tailTrace_179190
  have hstable : (prefixWord ++ tailWord_179190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179190).length < 2 ^ (prefixWord ++ tailWord_179190).sum := by decide
  have hdescent : baseEnd_179190 < baseStart_179190 := by decide
  rcases family_descends (prefixWord ++ tailWord_179190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179211 : List Nat := [1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_179211 : Nat := 118140960795 + 179211 * 2 ^ 59
def prefixEnd_179211 : Nat := 4983230072969 + 3 ^ 40 * 179211 * 2
def baseEnd_179211 : Nat := 54531189080298411756047

theorem tailTrace_179211 : CollatzResearch.WordTrace tailWord_179211 prefixEnd_179211 54531189080298411756047 := by
  unfold tailWord_179211
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536362153756628647177487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4357574769171085764784991 6536362153756628647177487)
  ·
    refine ⟨9804543230634942970766231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6536362153756628647177487 9804543230634942970766231)
    ·
      refine ⟨14706814845952414456149347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9804543230634942970766231 14706814845952414456149347)
      ·
        refine ⟨22060222268928621684224021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14706814845952414456149347 22060222268928621684224021)
        ·
          refine ⟨1034072918856029141448001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22060222268928621684224021 1034072918856029141448001)
          ·
            refine ⟨775554689142021856086001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034072918856029141448001 775554689142021856086001)
            ·
              refine ⟨581666016856516392064501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775554689142021856086001 581666016856516392064501)
              ·
                refine ⟨54531189080298411756047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 581666016856516392064501 54531189080298411756047)
                ·
                  rfl

theorem cell19_179211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_179211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179211 prefixEnd_179211 := by exact prefixLift 179211
  have htrace : WordTrace (prefixWord ++ tailWord_179211) baseStart_179211 baseEnd_179211 := by
    simpa [prefixWord, tailWord_179211, baseEnd_179211] using wordTrace_append hprefix tailTrace_179211
  have hstable : (prefixWord ++ tailWord_179211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179211).length < 2 ^ (prefixWord ++ tailWord_179211).sum := by decide
  have hdescent : baseEnd_179211 < baseStart_179211 := by decide
  rcases family_descends (prefixWord ++ tailWord_179211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179228 : List Nat := [2, 2, 3, 1, 5, 6]
def baseStart_179228 : Nat := 118140960795 + 179228 * 2 ^ 59
def prefixEnd_179228 : Nat := 4983230072969 + 3 ^ 40 * 179228 * 2
def baseEnd_179228 : Nat := 6059595769160823264247

theorem tailTrace_179228 : CollatzResearch.WordTrace tailWord_179228 prefixEnd_179228 6059595769160823264247 := by
  unfold tailWord_179228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3268491097347520275273169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4357988129796693700364225 3268491097347520275273169)
  ·
    refine ⟨2451368323010640206454877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3268491097347520275273169 2451368323010640206454877)
    ·
      refine ⟨919263121128990077420579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2451368323010640206454877 919263121128990077420579)
      ·
        refine ⟨1378894681693485116130869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919263121128990077420579 1378894681693485116130869)
        ·
          refine ⟨129271376408764229637269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1378894681693485116130869 129271376408764229637269)
          ·
            refine ⟨6059595769160823264247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129271376408764229637269 6059595769160823264247)
            ·
              rfl

theorem cell19_179228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 6].length) (baseStart_179228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179228 prefixEnd_179228 := by exact prefixLift 179228
  have htrace : WordTrace (prefixWord ++ tailWord_179228) baseStart_179228 baseEnd_179228 := by
    simpa [prefixWord, tailWord_179228, baseEnd_179228] using wordTrace_append hprefix tailTrace_179228
  have hstable : (prefixWord ++ tailWord_179228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179228).length < 2 ^ (prefixWord ++ tailWord_179228).sum := by decide
  have hdescent : baseEnd_179228 < baseStart_179228 := by decide
  rcases family_descends (prefixWord ++ tailWord_179228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179230 : List Nat := [4, 3, 12]
def baseStart_179230 : Nat := 118140960795 + 179230 * 2 ^ 59
def prefixEnd_179230 : Nat := 4983230072969 + 3 ^ 40 * 179230 * 2
def baseEnd_179230 : Nat := 224431977333794227711

theorem tailTrace_179230 : CollatzResearch.WordTrace tailWord_179230 prefixEnd_179230 224431977333794227711 := by
  unfold tailWord_179230
  simp only [CollatzResearch.WordTrace]
  refine ⟨817131892585974361514893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4358036760458529928079429 817131892585974361514893)
  ·
    refine ⟨306424459719740385568085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 817131892585974361514893 306424459719740385568085)
    ·
      refine ⟨224431977333794227711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 306424459719740385568085 224431977333794227711)
      ·
        rfl

theorem cell19_179230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 12].length) (baseStart_179230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179230 prefixEnd_179230 := by exact prefixLift 179230
  have htrace : WordTrace (prefixWord ++ tailWord_179230) baseStart_179230 baseEnd_179230 := by
    simpa [prefixWord, tailWord_179230, baseEnd_179230] using wordTrace_append hprefix tailTrace_179230
  have hstable : (prefixWord ++ tailWord_179230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179230).length < 2 ^ (prefixWord ++ tailWord_179230).sum := by decide
  have hdescent : baseEnd_179230 < baseStart_179230 := by decide
  rcases family_descends (prefixWord ++ tailWord_179230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179317 : List Nat := [1, 3, 4, 3, 2, 1, 2, 3]
def baseStart_179317 : Nat := 118140960795 + 179317 * 2 ^ 59
def prefixEnd_179317 : Nat := 4983230072969 + 3 ^ 40 * 179317 * 2
def baseEnd_179317 : Nat := 54563443272521573400203

theorem tailTrace_179317 : CollatzResearch.WordTrace tailWord_179317 prefixEnd_179317 54563443272521573400203 := by
  unfold tailWord_179317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540228291372608750536205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4360152194248405833690803 6540228291372608750536205)
  ·
    refine ⟨2452585609264728281451077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6540228291372608750536205 2452585609264728281451077)
    ·
      refine ⟨459859801737136552772077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2452585609264728281451077 459859801737136552772077)
      ·
        refine ⟨172447425651426207289529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459859801737136552772077 172447425651426207289529)
        ·
          refine ⟨129335569238569655467147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172447425651426207289529 129335569238569655467147)
          ·
            refine ⟨194003353857854483200721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129335569238569655467147 194003353857854483200721)
            ·
              refine ⟨145502515393390862400541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194003353857854483200721 145502515393390862400541)
              ·
                refine ⟨54563443272521573400203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145502515393390862400541 54563443272521573400203)
                ·
                  rfl

theorem cell19_179317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_179317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179317 prefixEnd_179317 := by exact prefixLift 179317
  have htrace : WordTrace (prefixWord ++ tailWord_179317) baseStart_179317 baseEnd_179317 := by
    simpa [prefixWord, tailWord_179317, baseEnd_179317] using wordTrace_append hprefix tailTrace_179317
  have hstable : (prefixWord ++ tailWord_179317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179317).length < 2 ^ (prefixWord ++ tailWord_179317).sum := by decide
  have hdescent : baseEnd_179317 < baseStart_179317 := by decide
  rcases family_descends (prefixWord ++ tailWord_179317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179321 : List Nat := [1, 2, 1, 3, 5, 2, 2, 3]
def baseStart_179321 : Nat := 118140960795 + 179321 * 2 ^ 59
def prefixEnd_179321 : Nat := 4983230072969 + 3 ^ 40 * 179321 * 2
def baseEnd_179321 : Nat := 54564660411850749311303

theorem tailTrace_179321 : CollatzResearch.WordTrace tailWord_179321 prefixEnd_179321 54564660411850749311303 := by
  unfold tailWord_179321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540374183358117433681817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4360249455572078289121211 6540374183358117433681817)
  ·
    refine ⟨4905280637518588075261363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6540374183358117433681817 4905280637518588075261363)
    ·
      refine ⟨7357920956277882112892045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4905280637518588075261363 7357920956277882112892045)
      ·
        refine ⟨2759220358604205792334517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7357920956277882112892045 2759220358604205792334517)
        ·
          refine ⟨258676908619144293031361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2759220358604205792334517 258676908619144293031361)
          ·
            refine ⟨194007681464358219773521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258676908619144293031361 194007681464358219773521)
            ·
              refine ⟨145505761098268664830141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194007681464358219773521 145505761098268664830141)
              ·
                refine ⟨54564660411850749311303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145505761098268664830141 54564660411850749311303)
                ·
                  rfl

theorem cell19_179321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_179321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179321 prefixEnd_179321 := by exact prefixLift 179321
  have htrace : WordTrace (prefixWord ++ tailWord_179321) baseStart_179321 baseEnd_179321 := by
    simpa [prefixWord, tailWord_179321, baseEnd_179321] using wordTrace_append hprefix tailTrace_179321
  have hstable : (prefixWord ++ tailWord_179321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179321).length < 2 ^ (prefixWord ++ tailWord_179321).sum := by decide
  have hdescent : baseEnd_179321 < baseStart_179321 := by decide
  rcases family_descends (prefixWord ++ tailWord_179321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179325 : List Nat := [1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_179325 : Nat := 118140960795 + 179325 * 2 ^ 59
def prefixEnd_179325 : Nat := 4983230072969 + 3 ^ 40 * 179325 * 2
def baseEnd_179325 : Nat := 54565877551179925222403

theorem tailTrace_179325 : CollatzResearch.WordTrace tailWord_179325 prefixEnd_179325 54565877551179925222403 := by
  unfold tailWord_179325
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540520075343626116827429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4360346716895750744551619 6540520075343626116827429)
  ·
    refine ⟨1226347514126929896905143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6540520075343626116827429 1226347514126929896905143)
    ·
      refine ⟨1839521271190394845357715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226347514126929896905143 1839521271190394845357715)
      ·
        refine ⟨2759281906785592268036573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839521271190394845357715 2759281906785592268036573)
        ·
          refine ⟨1034730715044597100513715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2759281906785592268036573 1034730715044597100513715)
          ·
            refine ⟨1552096072566895650770573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034730715044597100513715 1552096072566895650770573)
            ·
              refine ⟨582036027212585869038965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1552096072566895650770573 582036027212585869038965)
              ·
                refine ⟨54565877551179925222403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 582036027212585869038965 54565877551179925222403)
                ·
                  rfl

theorem cell19_179325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_179325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179325 prefixEnd_179325 := by exact prefixLift 179325
  have htrace : WordTrace (prefixWord ++ tailWord_179325) baseStart_179325 baseEnd_179325 := by
    simpa [prefixWord, tailWord_179325, baseEnd_179325] using wordTrace_append hprefix tailTrace_179325
  have hstable : (prefixWord ++ tailWord_179325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179325).length < 2 ^ (prefixWord ++ tailWord_179325).sum := by decide
  have hdescent : baseEnd_179325 < baseStart_179325 := by decide
  rcases family_descends (prefixWord ++ tailWord_179325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179342 : List Nat := [4, 1, 1, 3, 2, 3, 5]
def baseStart_179342 : Nat := 118140960795 + 179342 * 2 ^ 59
def prefixEnd_179342 : Nat := 4983230072969 + 3 ^ 40 * 179342 * 2
def baseEnd_179342 : Nat := 18190350131109640948193

theorem tailTrace_179342 : CollatzResearch.WordTrace tailWord_179342 prefixEnd_179342 18190350131109640948193 := by
  unfold tailWord_179342
  simp only [CollatzResearch.WordTrace]
  refine ⟨817642514535254752524535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4360760077521358680130853 817642514535254752524535)
  ·
    refine ⟨1226463771802882128786803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 817642514535254752524535 1226463771802882128786803)
    ·
      refine ⟨1839695657704323193180205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226463771802882128786803 1839695657704323193180205)
      ·
        refine ⟨689885871639121197442577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1839695657704323193180205 689885871639121197442577)
        ·
          refine ⟨517414403729340898081933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689885871639121197442577 517414403729340898081933)
          ·
            refine ⟨194030401398502836780725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517414403729340898081933 194030401398502836780725)
            ·
              refine ⟨18190350131109640948193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194030401398502836780725 18190350131109640948193)
              ·
                rfl

theorem cell19_179342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_179342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179342 prefixEnd_179342 := by exact prefixLift 179342
  have htrace : WordTrace (prefixWord ++ tailWord_179342) baseStart_179342 baseEnd_179342 := by
    simpa [prefixWord, tailWord_179342, baseEnd_179342] using wordTrace_append hprefix tailTrace_179342
  have hstable : (prefixWord ++ tailWord_179342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179342).length < 2 ^ (prefixWord ++ tailWord_179342).sum := by decide
  have hdescent : baseEnd_179342 < baseStart_179342 := by decide
  rcases family_descends (prefixWord ++ tailWord_179342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179414 : List Nat := [5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_179414 : Nat := 118140960795 + 179414 * 2 ^ 59
def prefixEnd_179414 : Nat := 4983230072969 + 3 ^ 40 * 179414 * 2
def baseEnd_179414 : Nat := 54592958901254089244383

theorem tailTrace_179414 : CollatzResearch.WordTrace tailWord_179414 prefixEnd_179414 54592958901254089244383 := by
  unfold tailWord_179414
  simp only [CollatzResearch.WordTrace]
  refine ⟨408985385751324644801081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4362510781347462877878197 408985385751324644801081)
  ·
    refine ⟨306739039313493483600811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 408985385751324644801081 306739039313493483600811)
    ·
      refine ⟨460108558970240225401217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306739039313493483600811 460108558970240225401217)
      ·
        refine ⟨345081419227680169050913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460108558970240225401217 345081419227680169050913)
        ·
          refine ⟨258811064420760126788185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345081419227680169050913 258811064420760126788185)
          ·
            refine ⟨194108298315570095091139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258811064420760126788185 194108298315570095091139)
            ·
              refine ⟨291162447473355142636709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194108298315570095091139 291162447473355142636709)
              ·
                refine ⟨54592958901254089244383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291162447473355142636709 54592958901254089244383)
                ·
                  rfl

theorem cell19_179414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_179414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179414 prefixEnd_179414 := by exact prefixLift 179414
  have htrace : WordTrace (prefixWord ++ tailWord_179414) baseStart_179414 baseEnd_179414 := by
    simpa [prefixWord, tailWord_179414, baseEnd_179414] using wordTrace_append hprefix tailTrace_179414
  have hstable : (prefixWord ++ tailWord_179414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179414).length < 2 ^ (prefixWord ++ tailWord_179414).sum := by decide
  have hdescent : baseEnd_179414 < baseStart_179414 := by decide
  rcases family_descends (prefixWord ++ tailWord_179414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179416 : List Nat := [2, 1, 2, 2, 6, 1, 1, 4]
def baseStart_179416 : Nat := 118140960795 + 179416 * 2 ^ 59
def prefixEnd_179416 : Nat := 4983230072969 + 3 ^ 40 * 179416 * 2
def baseEnd_179416 : Nat := 54593567470918677199933

theorem tailTrace_179416 : CollatzResearch.WordTrace tailWord_179416 prefixEnd_179416 54593567470918677199933 := by
  unfold tailWord_179416
  simp only [CollatzResearch.WordTrace]
  refine ⟨3271919559006974329195051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4362559412009299105593401 3271919559006974329195051)
  ·
    refine ⟨4907879338510461493792577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3271919559006974329195051 4907879338510461493792577)
    ·
      refine ⟨3680909503882846120344433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4907879338510461493792577 3680909503882846120344433)
      ·
        refine ⟨2760682127912134590258325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3680909503882846120344433 2760682127912134590258325)
        ·
          refine ⟨129406974745881308918359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2760682127912134590258325 129406974745881308918359)
          ·
            refine ⟨194110462118821963377539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129406974745881308918359 194110462118821963377539)
            ·
              refine ⟨291165693178232945066309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194110462118821963377539 291165693178232945066309)
              ·
                refine ⟨54593567470918677199933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291165693178232945066309 54593567470918677199933)
                ·
                  rfl

theorem cell19_179416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_179416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179416 prefixEnd_179416 := by exact prefixLift 179416
  have htrace : WordTrace (prefixWord ++ tailWord_179416) baseStart_179416 baseEnd_179416 := by
    simpa [prefixWord, tailWord_179416, baseEnd_179416] using wordTrace_append hprefix tailTrace_179416
  have hstable : (prefixWord ++ tailWord_179416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179416).length < 2 ^ (prefixWord ++ tailWord_179416).sum := by decide
  have hdescent : baseEnd_179416 < baseStart_179416 := by decide
  rcases family_descends (prefixWord ++ tailWord_179416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179490 : List Nat := [3, 3, 1, 1, 5, 1, 2, 3]
def baseStart_179490 : Nat := 118140960795 + 179490 * 2 ^ 59
def prefixEnd_179490 : Nat := 4983230072969 + 3 ^ 40 * 179490 * 2
def baseEnd_179490 : Nat := 54616084548508431555287

theorem tailTrace_179490 : CollatzResearch.WordTrace tailWord_179490 prefixEnd_179490 54616084548508431555287 := by
  unfold tailWord_179490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636634529936464824145981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4364358746497239531055949 1636634529936464824145981)
  ·
    refine ⟨613737948726174309054743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1636634529936464824145981 613737948726174309054743)
    ·
      refine ⟨920606923089261463582115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613737948726174309054743 920606923089261463582115)
      ·
        refine ⟨1380910384633892195373173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920606923089261463582115 1380910384633892195373173)
        ·
          refine ⟨129460348559427393316235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1380910384633892195373173 129460348559427393316235)
          ·
            refine ⟨194190522839141089974353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129460348559427393316235 194190522839141089974353)
            ·
              refine ⟨145642892129355817480765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194190522839141089974353 145642892129355817480765)
              ·
                refine ⟨54616084548508431555287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145642892129355817480765 54616084548508431555287)
                ·
                  rfl

theorem cell19_179490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_179490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179490 prefixEnd_179490 := by exact prefixLift 179490
  have htrace : WordTrace (prefixWord ++ tailWord_179490) baseStart_179490 baseEnd_179490 := by
    simpa [prefixWord, tailWord_179490, baseEnd_179490] using wordTrace_append hprefix tailTrace_179490
  have hstable : (prefixWord ++ tailWord_179490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179490).length < 2 ^ (prefixWord ++ tailWord_179490).sum := by decide
  have hdescent : baseEnd_179490 < baseStart_179490 := by decide
  rcases family_descends (prefixWord ++ tailWord_179490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179513 : List Nat := [1, 2, 1, 6, 2, 2, 5]
def baseStart_179513 : Nat := 118140960795 + 179513 * 2 ^ 59
def prefixEnd_179513 : Nat := 4983230072969 + 3 ^ 40 * 179513 * 2
def baseEnd_179513 : Nat := 18207694366550397681371

theorem tailTrace_179513 : CollatzResearch.WordTrace tailWord_179513 prefixEnd_179513 18207694366550397681371 := by
  unfold tailWord_179513
  simp only [CollatzResearch.WordTrace]
  refine ⟨6547376998662534224671193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4364917999108356149780795 6547376998662534224671193)
  ·
    refine ⟨4910532748996900668503395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6547376998662534224671193 4910532748996900668503395)
    ·
      refine ⟨7365799123495351002755093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4910532748996900668503395 7365799123495351002755093)
      ·
        refine ⟨345271833913844578254145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7365799123495351002755093 345271833913844578254145)
        ·
          refine ⟨258953875435383433690609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345271833913844578254145 258953875435383433690609)
          ·
            refine ⟨194215406576537575267957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258953875435383433690609 194215406576537575267957)
            ·
              refine ⟨18207694366550397681371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194215406576537575267957 18207694366550397681371)
              ·
                rfl

theorem cell19_179513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_179513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179513 prefixEnd_179513 := by exact prefixLift 179513
  have htrace : WordTrace (prefixWord ++ tailWord_179513) baseStart_179513 baseEnd_179513 := by
    simpa [prefixWord, tailWord_179513, baseEnd_179513] using wordTrace_append hprefix tailTrace_179513
  have hstable : (prefixWord ++ tailWord_179513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179513).length < 2 ^ (prefixWord ++ tailWord_179513).sum := by decide
  have hdescent : baseEnd_179513 < baseStart_179513 := by decide
  rcases family_descends (prefixWord ++ tailWord_179513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179534 : List Nat := [4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_179534 : Nat := 118140960795 + 179534 * 2 ^ 59
def prefixEnd_179534 : Nat := 4983230072969 + 3 ^ 40 * 179534 * 2
def baseEnd_179534 : Nat := 54629473081129366577389

theorem tailTrace_179534 : CollatzResearch.WordTrace tailWord_179534 prefixEnd_179534 54629473081129366577389 := by
  unfold tailWord_179534
  simp only [CollatzResearch.WordTrace]
  refine ⟨818517866448306851398207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4365428621057636540790437 818517866448306851398207)
  ·
    refine ⟨1227776799672460277097311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 818517866448306851398207 1227776799672460277097311)
    ·
      refine ⟨1841665199508690415645967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227776799672460277097311 1841665199508690415645967)
      ·
        refine ⟨2762497799263035623468951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841665199508690415645967 2762497799263035623468951)
        ·
          refine ⟨4143746698894553435203427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762497799263035623468951 4143746698894553435203427)
          ·
            refine ⟨6215620048341830152805141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143746698894553435203427 6215620048341830152805141)
            ·
              refine ⟨291357189766023288412741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6215620048341830152805141 291357189766023288412741)
              ·
                refine ⟨54629473081129366577389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291357189766023288412741 54629473081129366577389)
                ·
                  rfl

theorem cell19_179534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_179534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179534 prefixEnd_179534 := by exact prefixLift 179534
  have htrace : WordTrace (prefixWord ++ tailWord_179534) baseStart_179534 baseEnd_179534 := by
    simpa [prefixWord, tailWord_179534, baseEnd_179534] using wordTrace_append hprefix tailTrace_179534
  have hstable : (prefixWord ++ tailWord_179534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179534).length < 2 ^ (prefixWord ++ tailWord_179534).sum := by decide
  have hdescent : baseEnd_179534 < baseStart_179534 := by decide
  rcases family_descends (prefixWord ++ tailWord_179534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179591 : List Nat := [1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_179591 : Nat := 118140960795 + 179591 * 2 ^ 59
def prefixEnd_179591 : Nat := 4983230072969 + 3 ^ 40 * 179591 * 2
def baseEnd_179591 : Nat := 54646817316570123310567

theorem tailTrace_179591 : CollatzResearch.WordTrace tailWord_179591 prefixEnd_179591 54646817316570123310567 := by
  unfold tailWord_179591
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550221892379953546010627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4366814594919969030673751 6550221892379953546010627)
  ·
    refine ⟨9825332838569930319015941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6550221892379953546010627 9825332838569930319015941)
    ·
      refine ⟨1842249907231861934815489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9825332838569930319015941 1842249907231861934815489)
      ·
        refine ⟨1381687430423896451111617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1842249907231861934815489 1381687430423896451111617)
        ·
          refine ⟨1036265572817922338333713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1381687430423896451111617 1036265572817922338333713)
          ·
            refine ⟨777199179613441753750285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036265572817922338333713 777199179613441753750285)
            ·
              refine ⟨291449692355040657656357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 777199179613441753750285 291449692355040657656357)
              ·
                refine ⟨54646817316570123310567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291449692355040657656357 54646817316570123310567)
                ·
                  rfl

theorem cell19_179591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_179591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179591 prefixEnd_179591 := by exact prefixLift 179591
  have htrace : WordTrace (prefixWord ++ tailWord_179591) baseStart_179591 baseEnd_179591 := by
    simpa [prefixWord, tailWord_179591, baseEnd_179591] using wordTrace_append hprefix tailTrace_179591
  have hstable : (prefixWord ++ tailWord_179591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179591).length < 2 ^ (prefixWord ++ tailWord_179591).sum := by decide
  have hdescent : baseEnd_179591 < baseStart_179591 := by decide
  rcases family_descends (prefixWord ++ tailWord_179591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179745 : List Nat := [1, 2, 3, 2, 2, 9]
def baseStart_179745 : Nat := 118140960795 + 179745 * 2 ^ 59
def prefixEnd_179745 : Nat := 4983230072969 + 3 ^ 40 * 179745 * 2
def baseEnd_179745 : Nat := 6077075242304821765325

theorem tailTrace_179745 : CollatzResearch.WordTrace tailWord_179745 prefixEnd_179745 6077075242304821765325 := by
  unfold tailWord_179745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555838733822037847116689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4370559155881358564744459 6555838733822037847116689)
  ·
    refine ⟨4916879050366528385337517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6555838733822037847116689 4916879050366528385337517)
    ·
      refine ⟨1843829643887448144501569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4916879050366528385337517 1843829643887448144501569)
      ·
        refine ⟨1382872232915586108376177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1843829643887448144501569 1382872232915586108376177)
        ·
          refine ⟨1037154174686689581282133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1382872232915586108376177 1037154174686689581282133)
          ·
            refine ⟨6077075242304821765325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1037154174686689581282133 6077075242304821765325)
            ·
              rfl

theorem cell19_179745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_179745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179745 prefixEnd_179745 := by exact prefixLift 179745
  have htrace : WordTrace (prefixWord ++ tailWord_179745) baseStart_179745 baseEnd_179745 := by
    simpa [prefixWord, tailWord_179745, baseEnd_179745] using wordTrace_append hprefix tailTrace_179745
  have hstable : (prefixWord ++ tailWord_179745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179745).length < 2 ^ (prefixWord ++ tailWord_179745).sum := by decide
  have hdescent : baseEnd_179745 < baseStart_179745 := by decide
  rcases family_descends (prefixWord ++ tailWord_179745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179781 : List Nat := [1, 3, 1, 1, 1, 4, 5, 3]
def baseStart_179781 : Nat := 118140960795 + 179781 * 2 ^ 59
def prefixEnd_179781 : Nat := 4983230072969 + 3 ^ 40 * 179781 * 2
def baseEnd_179781 : Nat := 54704631434705979087827

theorem tailTrace_179781 : CollatzResearch.WordTrace tailWord_179781 prefixEnd_179781 54704631434705979087827 := by
  unfold tailWord_179781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6557151761691615995427197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4371434507794410663618131 6557151761691615995427197)
  ·
    refine ⟨2458931910634355998285199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6557151761691615995427197 2458931910634355998285199)
    ·
      refine ⟨3688397865951533997427799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458931910634355998285199 3688397865951533997427799)
      ·
        refine ⟨5532596798927300996141699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688397865951533997427799 5532596798927300996141699)
        ·
          refine ⟨8298895198390951494212549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532596798927300996141699 8298895198390951494212549)
          ·
            refine ⟨1556042849698303405164853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8298895198390951494212549 1556042849698303405164853)
            ·
              refine ⟨145879017159215944234205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1556042849698303405164853 145879017159215944234205)
              ·
                refine ⟨54704631434705979087827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145879017159215944234205 54704631434705979087827)
                ·
                  rfl

theorem cell19_179781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_179781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179781 prefixEnd_179781 := by exact prefixLift 179781
  have htrace : WordTrace (prefixWord ++ tailWord_179781) baseStart_179781 baseEnd_179781 := by
    simpa [prefixWord, tailWord_179781, baseEnd_179781] using wordTrace_append hprefix tailTrace_179781
  have hstable : (prefixWord ++ tailWord_179781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179781).length < 2 ^ (prefixWord ++ tailWord_179781).sum := by decide
  have hdescent : baseEnd_179781 < baseStart_179781 := by decide
  rcases family_descends (prefixWord ++ tailWord_179781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179840 : List Nat := [2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_179840 : Nat := 118140960795 + 179840 * 2 ^ 59
def prefixEnd_179840 : Nat := 4983230072969 + 3 ^ 40 * 179840 * 2
def baseEnd_179840 : Nat := 54722584239811323776555

theorem tailTrace_179840 : CollatzResearch.WordTrace tailWord_179840 prefixEnd_179840 54722584239811323776555 := by
  unfold tailWord_179840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279651834238934535912487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4372869112318579381216649 3279651834238934535912487)
  ·
    refine ⟨4919477751358401803868731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3279651834238934535912487 4919477751358401803868731)
    ·
      refine ⟨7379216627037602705803097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919477751358401803868731 7379216627037602705803097)
      ·
        refine ⟨5534412470278202029352323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7379216627037602705803097 5534412470278202029352323)
        ·
          refine ⟨8301618705417303044028485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5534412470278202029352323 8301618705417303044028485)
          ·
            refine ⟨1556553507265744320755341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8301618705417303044028485 1556553507265744320755341)
            ·
              refine ⟨583707565224654120283253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1556553507265744320755341 583707565224654120283253)
              ·
                refine ⟨54722584239811323776555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 583707565224654120283253 54722584239811323776555)
                ·
                  rfl

theorem cell19_179840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_179840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179840 prefixEnd_179840 := by exact prefixLift 179840
  have htrace : WordTrace (prefixWord ++ tailWord_179840) baseStart_179840 baseEnd_179840 := by
    simpa [prefixWord, tailWord_179840, baseEnd_179840] using wordTrace_append hprefix tailTrace_179840
  have hstable : (prefixWord ++ tailWord_179840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179840).length < 2 ^ (prefixWord ++ tailWord_179840).sum := by decide
  have hdescent : baseEnd_179840 < baseStart_179840 := by decide
  rcases family_descends (prefixWord ++ tailWord_179840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179876 : List Nat := [2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_179876 : Nat := 118140960795 + 179876 * 2 ^ 59
def prefixEnd_179876 : Nat := 4983230072969 + 3 ^ 40 * 179876 * 2
def baseEnd_179876 : Nat := 54733538493773906976457

theorem tailTrace_179876 : CollatzResearch.WordTrace tailWord_179876 prefixEnd_179876 54733538493773906976457 := by
  unfold tailWord_179876
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280308348173723610067741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4373744464231631480090321 3280308348173723610067741)
  ·
    refine ⟨1230115630565146353775403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3280308348173723610067741 1230115630565146353775403)
    ·
      refine ⟨1845173445847719530663105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230115630565146353775403 1845173445847719530663105)
      ·
        refine ⟨1383880084385789647997329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845173445847719530663105 1383880084385789647997329)
        ·
          refine ⟨1037910063289342235997997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383880084385789647997329 1037910063289342235997997)
          ·
            refine ⟨389216273733503338499249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037910063289342235997997 389216273733503338499249)
            ·
              refine ⟨291912205300127503874437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389216273733503338499249 291912205300127503874437)
              ·
                refine ⟨54733538493773906976457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291912205300127503874437 54733538493773906976457)
                ·
                  rfl

theorem cell19_179876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_179876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179876 prefixEnd_179876 := by exact prefixLift 179876
  have htrace : WordTrace (prefixWord ++ tailWord_179876) baseStart_179876 baseEnd_179876 := by
    simpa [prefixWord, tailWord_179876, baseEnd_179876] using wordTrace_append hprefix tailTrace_179876
  have hstable : (prefixWord ++ tailWord_179876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179876).length < 2 ^ (prefixWord ++ tailWord_179876).sum := by decide
  have hdescent : baseEnd_179876 < baseStart_179876 := by decide
  rcases family_descends (prefixWord ++ tailWord_179876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179897 : List Nat := [1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_179897 : Nat := 118140960795 + 179897 * 2 ^ 59
def prefixEnd_179897 : Nat := 4983230072969 + 3 ^ 40 * 179897 * 2
def baseEnd_179897 : Nat := 54739928475252080509733

theorem tailTrace_179897 : CollatzResearch.WordTrace tailWord_179897 prefixEnd_179897 54739928475252080509733 := by
  unfold tailWord_179897
  simp only [CollatzResearch.WordTrace]
  refine ⟨6561382629271367806649945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4374255086180911871099963 6561382629271367806649945)
  ·
    refine ⟨4921036971953525854987459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6561382629271367806649945 4921036971953525854987459)
    ·
      refine ⟨7381555457930288782481189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4921036971953525854987459 7381555457930288782481189)
      ·
        refine ⟨1384041648361929146715223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7381555457930288782481189 1384041648361929146715223)
        ·
          refine ⟨2076062472542893720072835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384041648361929146715223 2076062472542893720072835)
          ·
            refine ⟨3114093708814340580109253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2076062472542893720072835 3114093708814340580109253)
            ·
              refine ⟨583892570402688858770485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3114093708814340580109253 583892570402688858770485)
              ·
                refine ⟨54739928475252080509733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 583892570402688858770485 54739928475252080509733)
                ·
                  rfl

theorem cell19_179897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_179897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179897 prefixEnd_179897 := by exact prefixLift 179897
  have htrace : WordTrace (prefixWord ++ tailWord_179897) baseStart_179897 baseEnd_179897 := by
    simpa [prefixWord, tailWord_179897, baseEnd_179897] using wordTrace_append hprefix tailTrace_179897
  have hstable : (prefixWord ++ tailWord_179897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179897).length < 2 ^ (prefixWord ++ tailWord_179897).sum := by decide
  have hdescent : baseEnd_179897 < baseStart_179897 := by decide
  rcases family_descends (prefixWord ++ tailWord_179897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179914 : List Nat := [3, 1, 2, 1, 6, 6]
def baseStart_179914 : Nat := 118140960795 + 179914 * 2 ^ 59
def prefixEnd_179914 : Nat := 4983230072969 + 3 ^ 40 * 179914 * 2
def baseEnd_179914 : Nat := 6082789035266786459101

theorem tailTrace_179914 : CollatzResearch.WordTrace tailWord_179914 prefixEnd_179914 6082789035266786459101 := by
  unfold tailWord_179914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640500667552444927504699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4374668446806519806679197 1640500667552444927504699)
  ·
    refine ⟨2460751001328667391257049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1640500667552444927504699 2460751001328667391257049)
    ·
      refine ⟨1845563250996500543442787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2460751001328667391257049 1845563250996500543442787)
      ·
        refine ⟨2768344876494750815164181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845563250996500543442787 2768344876494750815164181)
        ·
          refine ⟨129766166085691444460821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2768344876494750815164181 129766166085691444460821)
          ·
            refine ⟨6082789035266786459101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129766166085691444460821 6082789035266786459101)
            ·
              rfl

theorem cell19_179914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 6].length) (baseStart_179914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179914 prefixEnd_179914 := by exact prefixLift 179914
  have htrace : WordTrace (prefixWord ++ tailWord_179914) baseStart_179914 baseEnd_179914 := by
    simpa [prefixWord, tailWord_179914, baseEnd_179914] using wordTrace_append hprefix tailTrace_179914
  have hstable : (prefixWord ++ tailWord_179914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179914).length < 2 ^ (prefixWord ++ tailWord_179914).sum := by decide
  have hdescent : baseEnd_179914 < baseStart_179914 := by decide
  rcases family_descends (prefixWord ++ tailWord_179914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179916 : List Nat := [2, 2, 1, 5, 9]
def baseStart_179916 : Nat := 118140960795 + 179916 * 2 ^ 59
def prefixEnd_179916 : Nat := 4983230072969 + 3 ^ 40 * 179916 * 2
def baseEnd_179916 : Nat := 2027618884706135781017

theorem tailTrace_179916 : CollatzResearch.WordTrace tailWord_179916 prefixEnd_179916 2027618884706135781017 := by
  unfold tailWord_179916
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281037808101267025795801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4374717077468356034394401 3281037808101267025795801)
  ·
    refine ⟨2460778356075950269346851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3281037808101267025795801 2460778356075950269346851)
    ·
      refine ⟨3691167534113925404020277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460778356075950269346851 3691167534113925404020277)
      ·
        refine ⟨346046956323180506626901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3691167534113925404020277 346046956323180506626901)
        ·
          refine ⟨2027618884706135781017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 346046956323180506626901 2027618884706135781017)
          ·
            rfl

theorem cell19_179916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 9].length) (baseStart_179916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_179916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_179916 prefixEnd_179916 := by exact prefixLift 179916
  have htrace : WordTrace (prefixWord ++ tailWord_179916) baseStart_179916 baseEnd_179916 := by
    simpa [prefixWord, tailWord_179916, baseEnd_179916] using wordTrace_append hprefix tailTrace_179916
  have hstable : (prefixWord ++ tailWord_179916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179916).length < 2 ^ (prefixWord ++ tailWord_179916).sum := by decide
  have hdescent : baseEnd_179916 < baseStart_179916 := by decide
  rcases family_descends (prefixWord ++ tailWord_179916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180045 : List Nat := [1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_180045 : Nat := 118140960795 + 180045 * 2 ^ 59
def prefixEnd_180045 : Nat := 4983230072969 + 3 ^ 40 * 180045 * 2
def baseEnd_180045 : Nat := 54784962630431589220441

theorem tailTrace_180045 : CollatzResearch.WordTrace tailWord_180045 prefixEnd_180045 54784962630431589220441 := by
  unfold tailWord_180045
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566780632735189083037589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4377853755156792722025059 6566780632735189083037589)
  ·
    refine ⟨307817842159461988267387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6566780632735189083037589 307817842159461988267387)
    ·
      refine ⟨461726763239192982401081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307817842159461988267387 461726763239192982401081)
      ·
        refine ⟨346295072429394736800811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461726763239192982401081 346295072429394736800811)
        ·
          refine ⟨519442608644092105201217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346295072429394736800811 519442608644092105201217)
          ·
            refine ⟨389581956483069078900913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519442608644092105201217 389581956483069078900913)
            ·
              refine ⟨292186467362301809175685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389581956483069078900913 292186467362301809175685)
              ·
                refine ⟨54784962630431589220441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292186467362301809175685 54784962630431589220441)
                ·
                  rfl

theorem cell19_180045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_180045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180045 prefixEnd_180045 := by exact prefixLift 180045
  have htrace : WordTrace (prefixWord ++ tailWord_180045) baseStart_180045 baseEnd_180045 := by
    simpa [prefixWord, tailWord_180045, baseEnd_180045] using wordTrace_append hprefix tailTrace_180045
  have hstable : (prefixWord ++ tailWord_180045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180045).length < 2 ^ (prefixWord ++ tailWord_180045).sum := by decide
  have hdescent : baseEnd_180045 < baseStart_180045 := by decide
  rcases family_descends (prefixWord ++ tailWord_180045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180049 : List Nat := [1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_180049 : Nat := 118140960795 + 180049 * 2 ^ 59
def prefixEnd_180049 : Nat := 4983230072969 + 3 ^ 40 * 180049 * 2
def baseEnd_180049 : Nat := 54786179769760765131541

theorem tailTrace_180049 : CollatzResearch.WordTrace tailWord_180049 prefixEnd_180049 54786179769760765131541 := by
  unfold tailWord_180049
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566926524720697766183201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4377951016480465177455467 6566926524720697766183201)
  ·
    refine ⟨4925194893540523324637401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6566926524720697766183201 4925194893540523324637401)
    ·
      refine ⟨3693896170155392493478051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4925194893540523324637401 3693896170155392493478051)
      ·
        refine ⟨5540844255233088740217077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693896170155392493478051 5540844255233088740217077)
        ·
          refine ⟨519454148928102069395351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5540844255233088740217077 519454148928102069395351)
          ·
            refine ⟨779181223392153104093027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519454148928102069395351 779181223392153104093027)
            ·
              refine ⟨1168771835088229656139541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779181223392153104093027 1168771835088229656139541)
              ·
                refine ⟨54786179769760765131541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1168771835088229656139541 54786179769760765131541)
                ·
                  rfl

theorem cell19_180049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_180049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180049 prefixEnd_180049 := by exact prefixLift 180049
  have htrace : WordTrace (prefixWord ++ tailWord_180049) baseStart_180049 baseEnd_180049 := by
    simpa [prefixWord, tailWord_180049, baseEnd_180049] using wordTrace_append hprefix tailTrace_180049
  have hstable : (prefixWord ++ tailWord_180049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180049).length < 2 ^ (prefixWord ++ tailWord_180049).sum := by decide
  have hdescent : baseEnd_180049 < baseStart_180049 := by decide
  rcases family_descends (prefixWord ++ tailWord_180049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180066 : List Nat := [3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_180066 : Nat := 118140960795 + 180066 * 2 ^ 59
def prefixEnd_180066 : Nat := 4983230072969 + 3 ^ 40 * 180066 * 2
def baseEnd_180066 : Nat := 54791352611909762753717

theorem tailTrace_180066 : CollatzResearch.WordTrace tailWord_180066 prefixEnd_180066 54791352611909762753717 := by
  unfold tailWord_180066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641886641414777417388013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4378364377106073113034701 1641886641414777417388013)
  ·
    refine ⟨615707490530541531520505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1641886641414777417388013 615707490530541531520505)
    ·
      refine ⟨461780617897906148640379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 615707490530541531520505 461780617897906148640379)
      ·
        refine ⟨692670926846859222960569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461780617897906148640379 692670926846859222960569)
        ·
          refine ⟨519503195135144417220427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692670926846859222960569 519503195135144417220427)
          ·
            refine ⟨779254792702716625830641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519503195135144417220427 779254792702716625830641)
            ·
              refine ⟨584441094527037469372981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779254792702716625830641 584441094527037469372981)
              ·
                refine ⟨54791352611909762753717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 584441094527037469372981 54791352611909762753717)
                ·
                  rfl

theorem cell19_180066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_180066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180066 prefixEnd_180066 := by exact prefixLift 180066
  have htrace : WordTrace (prefixWord ++ tailWord_180066) baseStart_180066 baseEnd_180066 := by
    simpa [prefixWord, tailWord_180066, baseEnd_180066] using wordTrace_append hprefix tailTrace_180066
  have hstable : (prefixWord ++ tailWord_180066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180066).length < 2 ^ (prefixWord ++ tailWord_180066).sum := by decide
  have hdescent : baseEnd_180066 < baseStart_180066 := by decide
  rcases family_descends (prefixWord ++ tailWord_180066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180199 : List Nat := [1, 1, 5, 2, 3, 2, 5]
def baseStart_180199 : Nat := 118140960795 + 180199 * 2 ^ 59
def prefixEnd_180199 : Nat := 4983230072969 + 3 ^ 40 * 180199 * 2
def baseEnd_180199 : Nat := 18277274164868287265933

theorem tailTrace_180199 : CollatzResearch.WordTrace tailWord_180199 prefixEnd_180199 18277274164868287265933 := by
  unfold tailWord_180199
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572397474177273384143651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4381598316118182256095767 6572397474177273384143651)
  ·
    refine ⟨9858596211265910076215477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6572397474177273384143651 9858596211265910076215477)
    ·
      refine ⟨924243394806179069645201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9858596211265910076215477 924243394806179069645201)
      ·
        refine ⟨693182546104634302233901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 924243394806179069645201 693182546104634302233901)
        ·
          refine ⟨259943454789237863337713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693182546104634302233901 259943454789237863337713)
          ·
            refine ⟨194957591091928397503285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259943454789237863337713 194957591091928397503285)
            ·
              refine ⟨18277274164868287265933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194957591091928397503285 18277274164868287265933)
              ·
                rfl

theorem cell19_180199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_180199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180199 prefixEnd_180199 := by exact prefixLift 180199
  have htrace : WordTrace (prefixWord ++ tailWord_180199) baseStart_180199 baseEnd_180199 := by
    simpa [prefixWord, tailWord_180199, baseEnd_180199] using wordTrace_append hprefix tailTrace_180199
  have hstable : (prefixWord ++ tailWord_180199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180199).length < 2 ^ (prefixWord ++ tailWord_180199).sum := by decide
  have hdescent : baseEnd_180199 < baseStart_180199 := by decide
  rcases family_descends (prefixWord ++ tailWord_180199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180220 : List Nat := [2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_180220 : Nat := 118140960795 + 180220 * 2 ^ 59
def prefixEnd_180220 : Nat := 4983230072969 + 3 ^ 40 * 180220 * 2
def baseEnd_180220 : Nat := 54838212476083035331075

theorem tailTrace_180220 : CollatzResearch.WordTrace tailWord_180220 prefixEnd_180220 54838212476083035331075 := by
  unfold tailWord_180220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286581703550596985329057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4382108938067462647105409 3286581703550596985329057)
  ·
    refine ⟨2464936277662947738996793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3286581703550596985329057 2464936277662947738996793)
    ·
      refine ⟨1848702208247210804247595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2464936277662947738996793 1848702208247210804247595)
      ·
        refine ⟨2773053312370816206371393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848702208247210804247595 2773053312370816206371393)
        ·
          refine ⟨2079789984278112154778545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2773053312370816206371393 2079789984278112154778545)
          ·
            refine ⟨1559842488208584116083909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079789984278112154778545 1559842488208584116083909)
            ·
              refine ⟨292470466539109521765733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1559842488208584116083909 292470466539109521765733)
              ·
                refine ⟨54838212476083035331075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292470466539109521765733 54838212476083035331075)
                ·
                  rfl

theorem cell19_180220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_180220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180220 prefixEnd_180220 := by exact prefixLift 180220
  have htrace : WordTrace (prefixWord ++ tailWord_180220) baseStart_180220 baseEnd_180220 := by
    simpa [prefixWord, tailWord_180220, baseEnd_180220] using wordTrace_append hprefix tailTrace_180220
  have hstable : (prefixWord ++ tailWord_180220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180220).length < 2 ^ (prefixWord ++ tailWord_180220).sum := by decide
  have hdescent : baseEnd_180220 < baseStart_180220 := by decide
  rcases family_descends (prefixWord ++ tailWord_180220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180277 : List Nat := [1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_180277 : Nat := 118140960795 + 180277 * 2 ^ 59
def prefixEnd_180277 : Nat := 4983230072969 + 3 ^ 40 * 180277 * 2
def baseEnd_180277 : Nat := 54855556711523792064253

theorem tailTrace_180277 : CollatzResearch.WordTrace tailWord_180277 prefixEnd_180277 54855556711523792064253 := by
  unfold tailWord_180277
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575242367894692705483085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4383494911929795136988723 6575242367894692705483085)
  ·
    refine ⟨2465715887960509764556157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6575242367894692705483085 2465715887960509764556157)
    ·
      refine ⟨924643457985191161708559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2465715887960509764556157 924643457985191161708559)
      ·
        refine ⟨1386965186977786742562839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924643457985191161708559 1386965186977786742562839)
        ·
          refine ⟨2080447780466680113844259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386965186977786742562839 2080447780466680113844259)
          ·
            refine ⟨3120671670700020170766389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080447780466680113844259 3120671670700020170766389)
            ·
              refine ⟨292562969128126891009349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3120671670700020170766389 292562969128126891009349)
              ·
                refine ⟨54855556711523792064253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292562969128126891009349 54855556711523792064253)
                ·
                  rfl

theorem cell19_180277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_180277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180277 prefixEnd_180277 := by exact prefixLift 180277
  have htrace : WordTrace (prefixWord ++ tailWord_180277) baseStart_180277 baseEnd_180277 := by
    simpa [prefixWord, tailWord_180277, baseEnd_180277] using wordTrace_append hprefix tailTrace_180277
  have hstable : (prefixWord ++ tailWord_180277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180277).length < 2 ^ (prefixWord ++ tailWord_180277).sum := by decide
  have hdescent : baseEnd_180277 < baseStart_180277 := by decide
  rcases family_descends (prefixWord ++ tailWord_180277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180334 : List Nat := [4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_180334 : Nat := 118140960795 + 180334 * 2 ^ 59
def prefixEnd_180334 : Nat := 4983230072969 + 3 ^ 40 * 180334 * 2
def baseEnd_180334 : Nat := 54872900946964548797431

theorem tailTrace_180334 : CollatzResearch.WordTrace tailWord_180334 prefixEnd_180334 54872900946964548797431 := by
  unfold tailWord_180334
  simp only [CollatzResearch.WordTrace]
  refine ⟨822165166086023930038507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4384880885792127626872037 822165166086023930038507)
  ·
    refine ⟨1233247749129035895057761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 822165166086023930038507 1233247749129035895057761)
    ·
      refine ⟨924935811846776921293321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1233247749129035895057761 924935811846776921293321)
      ·
        refine ⟨693701858885082690969991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 924935811846776921293321 693701858885082690969991)
        ·
          refine ⟨1040552788327624036454987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693701858885082690969991 1040552788327624036454987)
          ·
            refine ⟨1560829182491436054682481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040552788327624036454987 1560829182491436054682481)
            ·
              refine ⟨1170621886868577041011861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560829182491436054682481 1170621886868577041011861)
              ·
                refine ⟨54872900946964548797431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1170621886868577041011861 54872900946964548797431)
                ·
                  rfl

theorem cell19_180334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_180334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180334 prefixEnd_180334 := by exact prefixLift 180334
  have htrace : WordTrace (prefixWord ++ tailWord_180334) baseStart_180334 baseEnd_180334 := by
    simpa [prefixWord, tailWord_180334, baseEnd_180334] using wordTrace_append hprefix tailTrace_180334
  have hstable : (prefixWord ++ tailWord_180334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180334).length < 2 ^ (prefixWord ++ tailWord_180334).sum := by decide
  have hdescent : baseEnd_180334 < baseStart_180334 := by decide
  rcases family_descends (prefixWord ++ tailWord_180334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180429 : List Nat := [1, 6, 2, 10]
def baseStart_180429 : Nat := 118140960795 + 180429 * 2 ^ 59
def prefixEnd_180429 : Nat := 4983230072969 + 3 ^ 40 * 180429 * 2
def baseEnd_180429 : Nat := 677800098839907119581

theorem tailTrace_180429 : CollatzResearch.WordTrace tailWord_180429 prefixEnd_180429 677800098839907119581 := by
  unfold tailWord_180429
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580786263344022665016341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4387190842229348443344227 6580786263344022665016341)
  ·
    refine ⟨308474356094251062422641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6580786263344022665016341 308474356094251062422641)
    ·
      refine ⟨231355767070688296816981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308474356094251062422641 231355767070688296816981)
      ·
        refine ⟨677800098839907119581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 231355767070688296816981 677800098839907119581)
        ·
          rfl

theorem cell19_180429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 10].length) (baseStart_180429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180429 prefixEnd_180429 := by exact prefixLift 180429
  have htrace : WordTrace (prefixWord ++ tailWord_180429) baseStart_180429 baseEnd_180429 := by
    simpa [prefixWord, tailWord_180429, baseEnd_180429] using wordTrace_append hprefix tailTrace_180429
  have hstable : (prefixWord ++ tailWord_180429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180429).length < 2 ^ (prefixWord ++ tailWord_180429).sum := by decide
  have hdescent : baseEnd_180429 < baseStart_180429 := by decide
  rcases family_descends (prefixWord ++ tailWord_180429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180467 : List Nat := [1, 1, 1, 2, 2, 4, 5, 3]
def baseStart_180467 : Nat := 118140960795 + 180467 * 2 ^ 59
def prefixEnd_180467 : Nat := 4983230072969 + 3 ^ 40 * 180467 * 2
def baseEnd_180467 : Nat := 54913370829659647841513

theorem tailTrace_180467 : CollatzResearch.WordTrace tailWord_180467 prefixEnd_180467 54913370829659647841513 := by
  unfold tailWord_180467
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582172237206355154899655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4388114824804236769933103 6582172237206355154899655)
  ·
    refine ⟨9873258355809532732349483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582172237206355154899655 9873258355809532732349483)
    ·
      refine ⟨14809887533714299098524225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9873258355809532732349483 14809887533714299098524225)
      ·
        refine ⟨11107415650285724323893169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14809887533714299098524225 11107415650285724323893169)
        ·
          refine ⟨8330561737714293242919877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11107415650285724323893169 8330561737714293242919877)
          ·
            refine ⟨1561980325821429983047477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8330561737714293242919877 1561980325821429983047477)
            ·
              refine ⟨146435655545759060910701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1561980325821429983047477 146435655545759060910701)
              ·
                refine ⟨54913370829659647841513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146435655545759060910701 54913370829659647841513)
                ·
                  rfl

theorem cell19_180467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_180467 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180467 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180467 prefixEnd_180467 := by exact prefixLift 180467
  have htrace : WordTrace (prefixWord ++ tailWord_180467) baseStart_180467 baseEnd_180467 := by
    simpa [prefixWord, tailWord_180467, baseEnd_180467] using wordTrace_append hprefix tailTrace_180467
  have hstable : (prefixWord ++ tailWord_180467).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180467).length < 2 ^ (prefixWord ++ tailWord_180467).sum := by decide
  have hdescent : baseEnd_180467 < baseStart_180467 := by decide
  rcases family_descends (prefixWord ++ tailWord_180467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180520 : List Nat := [2, 1, 5, 1, 3, 2, 2, 3]
def baseStart_180520 : Nat := 118140960795 + 180520 * 2 ^ 59
def prefixEnd_180520 : Nat := 4983230072969 + 3 ^ 40 * 180520 * 2
def baseEnd_180520 : Nat := 54929497925771228663591

theorem tailTrace_180520 : CollatzResearch.WordTrace tailWord_180520 prefixEnd_180520 54929497925771228663591 := by
  unfold tailWord_180520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292052653007172603289507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4389403537342896804386009 3292052653007172603289507)
  ·
    refine ⟨4938078979510758904934261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3292052653007172603289507 4938078979510758904934261)
    ·
      refine ⟨462944904329133647337587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4938078979510758904934261 462944904329133647337587)
      ·
        refine ⟨694417356493700471006381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462944904329133647337587 694417356493700471006381)
        ·
          refine ⟨260406508685137676627393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 694417356493700471006381 260406508685137676627393)
          ·
            refine ⟨195304881513853257470545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260406508685137676627393 195304881513853257470545)
            ·
              refine ⟨146478661135389943102909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195304881513853257470545 146478661135389943102909)
              ·
                refine ⟨54929497925771228663591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146478661135389943102909 54929497925771228663591)
                ·
                  rfl

theorem cell19_180520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_180520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180520 prefixEnd_180520 := by exact prefixLift 180520
  have htrace : WordTrace (prefixWord ++ tailWord_180520) baseStart_180520 baseEnd_180520 := by
    simpa [prefixWord, tailWord_180520, baseEnd_180520] using wordTrace_append hprefix tailTrace_180520
  have hstable : (prefixWord ++ tailWord_180520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180520).length < 2 ^ (prefixWord ++ tailWord_180520).sum := by decide
  have hdescent : baseEnd_180520 < baseStart_180520 := by decide
  rcases family_descends (prefixWord ++ tailWord_180520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180522 : List Nat := [3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_180522 : Nat := 118140960795 + 180522 * 2 ^ 59
def prefixEnd_180522 : Nat := 4983230072969 + 3 ^ 40 * 180522 * 2
def baseEnd_180522 : Nat := 54930106495435816619141

theorem tailTrace_180522 : CollatzResearch.WordTrace tailWord_180522 prefixEnd_180522 54930106495435816619141 := by
  unfold tailWord_180522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646044563001774887037955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4389452168004733032101213 1646044563001774887037955)
  ·
    refine ⟨2469066844502662330556933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1646044563001774887037955 2469066844502662330556933)
    ·
      refine ⟨462950033344249186979425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2469066844502662330556933 462950033344249186979425)
      ·
        refine ⟨347212525008186890234569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462950033344249186979425 347212525008186890234569)
        ·
          refine ⟨260409393756140167675927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347212525008186890234569 260409393756140167675927)
          ·
            refine ⟨390614090634210251513891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260409393756140167675927 390614090634210251513891)
            ·
              refine ⟨585921135951315377270837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390614090634210251513891 585921135951315377270837)
              ·
                refine ⟨54930106495435816619141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 585921135951315377270837 54930106495435816619141)
                ·
                  rfl

theorem cell19_180522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_180522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180522 prefixEnd_180522 := by exact prefixLift 180522
  have htrace : WordTrace (prefixWord ++ tailWord_180522) baseStart_180522 baseEnd_180522 := by
    simpa [prefixWord, tailWord_180522, baseEnd_180522] using wordTrace_append hprefix tailTrace_180522
  have hstable : (prefixWord ++ tailWord_180522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180522).length < 2 ^ (prefixWord ++ tailWord_180522).sum := by decide
  have hdescent : baseEnd_180522 < baseStart_180522 := by decide
  rcases family_descends (prefixWord ++ tailWord_180522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180524 : List Nat := [2, 2, 1, 1, 1, 3, 6, 3]
def baseStart_180524 : Nat := 118140960795 + 180524 * 2 ^ 59
def prefixEnd_180524 : Nat := 4983230072969 + 3 ^ 40 * 180524 * 2
def baseEnd_180524 : Nat := 54930715065100404574691

theorem tailTrace_180524 : CollatzResearch.WordTrace tailWord_180524 prefixEnd_180524 54930715065100404574691 := by
  unfold tailWord_180524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292125598999926944862313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4389500798666569259816417 3292125598999926944862313)
  ·
    refine ⟨2469094199249945208646735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3292125598999926944862313 2469094199249945208646735)
    ·
      refine ⟨3703641298874917812970103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469094199249945208646735 3703641298874917812970103)
      ·
        refine ⟨5555461948312376719455155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703641298874917812970103 5555461948312376719455155)
        ·
          refine ⟨8333192922468565079182733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555461948312376719455155 8333192922468565079182733)
          ·
            refine ⟨3124947345925711904693525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8333192922468565079182733 3124947345925711904693525)
            ·
              refine ⟨146481906840267745532509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3124947345925711904693525 146481906840267745532509)
              ·
                refine ⟨54930715065100404574691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146481906840267745532509 54930715065100404574691)
                ·
                  rfl

theorem cell19_180524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_180524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180524 prefixEnd_180524 := by exact prefixLift 180524
  have htrace : WordTrace (prefixWord ++ tailWord_180524) baseStart_180524 baseEnd_180524 := by
    simpa [prefixWord, tailWord_180524, baseEnd_180524] using wordTrace_append hprefix tailTrace_180524
  have hstable : (prefixWord ++ tailWord_180524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180524).length < 2 ^ (prefixWord ++ tailWord_180524).sum := by decide
  have hdescent : baseEnd_180524 < baseStart_180524 := by decide
  rcases family_descends (prefixWord ++ tailWord_180524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180598 : List Nat := [5, 1, 1, 4, 1, 7]
def baseStart_180598 : Nat := 118140960795 + 180598 * 2 ^ 59
def prefixEnd_180598 : Nat := 4983230072969 + 3 ^ 40 * 180598 * 2
def baseEnd_180598 : Nat := 6105914682521128770005

theorem tailTrace_180598 : CollatzResearch.WordTrace tailWord_180598 prefixEnd_180598 6105914682521128770005 := by
  unfold tailWord_180598
  simp only [CollatzResearch.WordTrace]
  refine ⟨411684387483235282994903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4391300133154509685278965 411684387483235282994903)
  ·
    refine ⟨617526581224852924492355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 411684387483235282994903 617526581224852924492355)
    ·
      refine ⟨926289871837279386738533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617526581224852924492355 926289871837279386738533)
      ·
        refine ⟨173679350969489885013475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 926289871837279386738533 173679350969489885013475)
        ·
          refine ⟨260519026454234827520213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173679350969489885013475 260519026454234827520213)
          ·
            refine ⟨6105914682521128770005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 260519026454234827520213 6105914682521128770005)
            ·
              rfl

theorem cell19_180598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 7].length) (baseStart_180598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180598 prefixEnd_180598 := by exact prefixLift 180598
  have htrace : WordTrace (prefixWord ++ tailWord_180598) baseStart_180598 baseEnd_180598 := by
    simpa [prefixWord, tailWord_180598, baseEnd_180598] using wordTrace_append hprefix tailTrace_180598
  have hstable : (prefixWord ++ tailWord_180598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180598).length < 2 ^ (prefixWord ++ tailWord_180598).sum := by decide
  have hdescent : baseEnd_180598 < baseStart_180598 := by decide
  rcases family_descends (prefixWord ++ tailWord_180598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180619 : List Nat := [1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_180619 : Nat := 118140960795 + 180619 * 2 ^ 59
def prefixEnd_180619 : Nat := 4983230072969 + 3 ^ 40 * 180619 * 2
def baseEnd_180619 : Nat := 54959622124168332463321

theorem tailTrace_180619 : CollatzResearch.WordTrace tailWord_180619 prefixEnd_180619 54959622124168332463321 := by
  unfold tailWord_180619
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587716132655685114432911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4391810755103790076288607 6587716132655685114432911)
  ·
    refine ⟨9881574198983527671649367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6587716132655685114432911 9881574198983527671649367)
    ·
      refine ⟨14822361298475291507474051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9881574198983527671649367 14822361298475291507474051)
      ·
        refine ⟨22233541947712937261211077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14822361298475291507474051 22233541947712937261211077)
        ·
          refine ⟨4168789115196175736477077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22233541947712937261211077 4168789115196175736477077)
          ·
            refine ⟨195411989774820737647363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4168789115196175736477077 195411989774820737647363)
            ·
              refine ⟨293117984662231106471045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195411989774820737647363 293117984662231106471045)
              ·
                refine ⟨54959622124168332463321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293117984662231106471045 54959622124168332463321)
                ·
                  rfl

theorem cell19_180619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_180619 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180619 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180619 prefixEnd_180619 := by exact prefixLift 180619
  have htrace : WordTrace (prefixWord ++ tailWord_180619) baseStart_180619 baseEnd_180619 := by
    simpa [prefixWord, tailWord_180619, baseEnd_180619] using wordTrace_append hprefix tailTrace_180619
  have hstable : (prefixWord ++ tailWord_180619).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180619).length < 2 ^ (prefixWord ++ tailWord_180619).sum := by decide
  have hdescent : baseEnd_180619 < baseStart_180619 := by decide
  rcases family_descends (prefixWord ++ tailWord_180619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180630 : List Nat := [5, 3, 1, 2, 1, 1, 3, 3]
def baseStart_180630 : Nat := 118140960795 + 180630 * 2 ^ 59
def prefixEnd_180630 : Nat := 4983230072969 + 3 ^ 40 * 180630 * 2
def baseEnd_180630 : Nat := 54962969257323566218847

theorem tailTrace_180630 : CollatzResearch.WordTrace tailWord_180630 prefixEnd_180630 54962969257323566218847 := by
  unfold tailWord_180630
  simp only [CollatzResearch.WordTrace]
  refine ⟨411757333475989624567709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4392078223743889328722229 411757333475989624567709)
  ·
    refine ⟨154409000053496109212891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 411757333475989624567709 154409000053496109212891)
    ·
      refine ⟨231613500080244163819337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154409000053496109212891 231613500080244163819337)
      ·
        refine ⟨173710125060183122864503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231613500080244163819337 173710125060183122864503)
        ·
          refine ⟨260565187590274684296755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173710125060183122864503 260565187590274684296755)
          ·
            refine ⟨390847781385412026445133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260565187590274684296755 390847781385412026445133)
            ·
              refine ⟨146567918019529509916925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390847781385412026445133 146567918019529509916925)
              ·
                refine ⟨54962969257323566218847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146567918019529509916925 54962969257323566218847)
                ·
                  rfl

theorem cell19_180630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_180630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180630 prefixEnd_180630 := by exact prefixLift 180630
  have htrace : WordTrace (prefixWord ++ tailWord_180630) baseStart_180630 baseEnd_180630 := by
    simpa [prefixWord, tailWord_180630, baseEnd_180630] using wordTrace_append hprefix tailTrace_180630
  have hstable : (prefixWord ++ tailWord_180630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180630).length < 2 ^ (prefixWord ++ tailWord_180630).sum := by decide
  have hdescent : baseEnd_180630 < baseStart_180630 := by decide
  rcases family_descends (prefixWord ++ tailWord_180630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180693 : List Nat := [1, 3, 2, 3, 1, 4, 2, 3]
def baseStart_180693 : Nat := 118140960795 + 180693 * 2 ^ 59
def prefixEnd_180693 : Nat := 4983230072969 + 3 ^ 40 * 180693 * 2
def baseEnd_180693 : Nat := 54982139201758086818675

theorem tailTrace_180693 : CollatzResearch.WordTrace tailWord_180693 prefixEnd_180693 54982139201758086818675 := by
  unfold tailWord_180693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590415134387595752626733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4393610089591730501751155 6590415134387595752626733)
  ·
    refine ⟨2471405675395348407235025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6590415134387595752626733 2471405675395348407235025)
    ·
      refine ⟨1853554256546511305426269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2471405675395348407235025 1853554256546511305426269)
      ·
        refine ⟨695082846204941739534851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1853554256546511305426269 695082846204941739534851)
        ·
          refine ⟨1042624269307412609302277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695082846204941739534851 1042624269307412609302277)
          ·
            refine ⟨195492050495139864244177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1042624269307412609302277 195492050495139864244177)
            ·
              refine ⟨146619037871354898183133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195492050495139864244177 146619037871354898183133)
              ·
                refine ⟨54982139201758086818675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146619037871354898183133 54982139201758086818675)
                ·
                  rfl

theorem cell19_180693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_180693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180693 prefixEnd_180693 := by exact prefixLift 180693
  have htrace : WordTrace (prefixWord ++ tailWord_180693) baseStart_180693 baseEnd_180693 := by
    simpa [prefixWord, tailWord_180693, baseEnd_180693] using wordTrace_append hprefix tailTrace_180693
  have hstable : (prefixWord ++ tailWord_180693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180693).length < 2 ^ (prefixWord ++ tailWord_180693).sum := by decide
  have hdescent : baseEnd_180693 < baseStart_180693 := by decide
  rcases family_descends (prefixWord ++ tailWord_180693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180697 : List Nat := [1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_180697 : Nat := 118140960795 + 180697 * 2 ^ 59
def prefixEnd_180697 : Nat := 4983230072969 + 3 ^ 40 * 180697 * 2
def baseEnd_180697 : Nat := 54983356341087262729775

theorem tailTrace_180697 : CollatzResearch.WordTrace tailWord_180697 prefixEnd_180697 54983356341087262729775 := by
  unfold tailWord_180697
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590561026373104435772345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4393707350915402957181563 6590561026373104435772345)
  ·
    refine ⟨4942920769779828326829259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6590561026373104435772345 4942920769779828326829259)
    ·
      refine ⟨7414381154669742490243889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4942920769779828326829259 7414381154669742490243889)
      ·
        refine ⟨5560785866002306867682917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7414381154669742490243889 5560785866002306867682917)
        ·
          refine ⟨1042647349875432537690547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5560785866002306867682917 1042647349875432537690547)
          ·
            refine ⟨1563971024813148806535821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042647349875432537690547 1563971024813148806535821)
            ·
              refine ⟨586489134304930802450933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1563971024813148806535821 586489134304930802450933)
              ·
                refine ⟨54983356341087262729775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 586489134304930802450933 54983356341087262729775)
                ·
                  rfl

theorem cell19_180697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_180697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180697 prefixEnd_180697 := by exact prefixLift 180697
  have htrace : WordTrace (prefixWord ++ tailWord_180697) baseStart_180697 baseEnd_180697 := by
    simpa [prefixWord, tailWord_180697, baseEnd_180697] using wordTrace_append hprefix tailTrace_180697
  have hstable : (prefixWord ++ tailWord_180697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180697).length < 2 ^ (prefixWord ++ tailWord_180697).sum := by decide
  have hdescent : baseEnd_180697 < baseStart_180697 := by decide
  rcases family_descends (prefixWord ++ tailWord_180697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180714 : List Nat := [3, 1, 3, 1, 3, 3, 5]
def baseStart_180714 : Nat := 118140960795 + 180714 * 2 ^ 59
def prefixEnd_180714 : Nat := 4983230072969 + 3 ^ 40 * 180714 * 2
def baseEnd_180714 : Nat := 18329509727745420117317

theorem tailTrace_180714 : CollatzResearch.WordTrace tailWord_180714 prefixEnd_180714 18329509727745420117317 := by
  unfold tailWord_180714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647795266827879084785299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4394120711541010892760797 1647795266827879084785299)
  ·
    refine ⟨2471692900241818627177949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1647795266827879084785299 2471692900241818627177949)
    ·
      refine ⟨926884837590681985191731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2471692900241818627177949 926884837590681985191731)
      ·
        refine ⟨1390327256386022977787597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926884837590681985191731 1390327256386022977787597)
        ·
          refine ⟨521372721144758616670349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1390327256386022977787597 521372721144758616670349)
          ·
            refine ⟨195514770429284481251381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 521372721144758616670349 195514770429284481251381)
            ·
              refine ⟨18329509727745420117317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195514770429284481251381 18329509727745420117317)
              ·
                rfl

theorem cell19_180714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_180714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180714 prefixEnd_180714 := by exact prefixLift 180714
  have htrace : WordTrace (prefixWord ++ tailWord_180714) baseStart_180714 baseEnd_180714 := by
    simpa [prefixWord, tailWord_180714, baseEnd_180714] using wordTrace_append hprefix tailTrace_180714
  have hstable : (prefixWord ++ tailWord_180714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180714).length < 2 ^ (prefixWord ++ tailWord_180714).sum := by decide
  have hdescent : baseEnd_180714 < baseStart_180714 := by decide
  rcases family_descends (prefixWord ++ tailWord_180714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180735 : List Nat := [1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_180735 : Nat := 118140960795 + 180735 * 2 ^ 59
def prefixEnd_180735 : Nat := 4983230072969 + 3 ^ 40 * 180735 * 2
def baseEnd_180735 : Nat := 54994919164714433885227

theorem tailTrace_180735 : CollatzResearch.WordTrace tailWord_180735 prefixEnd_180735 54994919164714433885227 := by
  unfold tailWord_180735
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591947000235436925655659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4394631333490291283770439 6591947000235436925655659)
  ·
    refine ⟨9887920500353155388483489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6591947000235436925655659 9887920500353155388483489)
    ·
      refine ⟨7415940375264866541362617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9887920500353155388483489 7415940375264866541362617)
      ·
        refine ⟨5561955281448649906021963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7415940375264866541362617 5561955281448649906021963)
        ·
          refine ⟨8342932922172974859032945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561955281448649906021963 8342932922172974859032945)
          ·
            refine ⟨6257199691629731144274709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342932922172974859032945 6257199691629731144274709)
            ·
              refine ⟨293306235545143647387877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6257199691629731144274709 293306235545143647387877)
              ·
                refine ⟨54994919164714433885227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293306235545143647387877 54994919164714433885227)
                ·
                  rfl

theorem cell19_180735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_180735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180735 prefixEnd_180735 := by exact prefixLift 180735
  have htrace : WordTrace (prefixWord ++ tailWord_180735) baseStart_180735 baseEnd_180735 := by
    simpa [prefixWord, tailWord_180735, baseEnd_180735] using wordTrace_append hprefix tailTrace_180735
  have hstable : (prefixWord ++ tailWord_180735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180735).length < 2 ^ (prefixWord ++ tailWord_180735).sum := by decide
  have hdescent : baseEnd_180735 < baseStart_180735 := by decide
  rcases family_descends (prefixWord ++ tailWord_180735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180828 : List Nat := [2, 2, 4, 1, 3, 1, 6]
def baseStart_180828 : Nat := 118140960795 + 180828 * 2 ^ 59
def prefixEnd_180828 : Nat := 4983230072969 + 3 ^ 40 * 180828 * 2
def baseEnd_180828 : Nat := 18341072551372591272769

theorem tailTrace_180828 : CollatzResearch.WordTrace tailWord_180828 prefixEnd_180828 18341072551372591272769 := by
  unfold tailWord_180828
  simp only [CollatzResearch.WordTrace]
  refine ⟨3297669494449256904395569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4396892659265675872527425 3297669494449256904395569)
  ·
    refine ⟨2473252120836942678296677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3297669494449256904395569 2473252120836942678296677)
    ·
      refine ⟨463734772656926752180627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2473252120836942678296677 463734772656926752180627)
      ·
        refine ⟨695602158985390128270941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463734772656926752180627 695602158985390128270941)
        ·
          refine ⟨260850809619521298101603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695602158985390128270941 260850809619521298101603)
          ·
            refine ⟨391276214429281947152405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260850809619521298101603 391276214429281947152405)
            ·
              refine ⟨18341072551372591272769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 391276214429281947152405 18341072551372591272769)
              ·
                rfl

theorem cell19_180828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_180828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180828 prefixEnd_180828 := by exact prefixLift 180828
  have htrace : WordTrace (prefixWord ++ tailWord_180828) baseStart_180828 baseEnd_180828 := by
    simpa [prefixWord, tailWord_180828, baseEnd_180828] using wordTrace_append hprefix tailTrace_180828
  have hstable : (prefixWord ++ tailWord_180828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180828).length < 2 ^ (prefixWord ++ tailWord_180828).sum := by decide
  have hdescent : baseEnd_180828 < baseStart_180828 := by decide
  rcases family_descends (prefixWord ++ tailWord_180828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180925 : List Nat := [1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_180925 : Nat := 118140960795 + 180925 * 2 ^ 59
def prefixEnd_180925 : Nat := 4983230072969 + 3 ^ 40 * 180925 * 2
def baseEnd_180925 : Nat := 55052733282850289662487

theorem tailTrace_180925 : CollatzResearch.WordTrace tailWord_180925 prefixEnd_180925 55052733282850289662487 := by
  unfold tailWord_180925
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598876869547099375072229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4399251246364732916714819 6598876869547099375072229)
  ·
    refine ⟨1237289413040081132826043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6598876869547099375072229 1237289413040081132826043)
    ·
      refine ⟨1855934119560121699239065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1237289413040081132826043 1855934119560121699239065)
      ·
        refine ⟨1391950589670091274429299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1855934119560121699239065 1391950589670091274429299)
        ·
          refine ⟨2087925884505136911643949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391950589670091274429299 2087925884505136911643949)
          ·
            refine ⟨782972206689426341866481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2087925884505136911643949 782972206689426341866481)
            ·
              refine ⟨587229155017069756399861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782972206689426341866481 587229155017069756399861)
              ·
                refine ⟨55052733282850289662487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587229155017069756399861 55052733282850289662487)
                ·
                  rfl

theorem cell19_180925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_180925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180925 prefixEnd_180925 := by exact prefixLift 180925
  have htrace : WordTrace (prefixWord ++ tailWord_180925) baseStart_180925 baseEnd_180925 := by
    simpa [prefixWord, tailWord_180925, baseEnd_180925] using wordTrace_append hprefix tailTrace_180925
  have hstable : (prefixWord ++ tailWord_180925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180925).length < 2 ^ (prefixWord ++ tailWord_180925).sum := by decide
  have hdescent : baseEnd_180925 < baseStart_180925 := by decide
  rcases family_descends (prefixWord ++ tailWord_180925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180961 : List Nat := [1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_180961 : Nat := 118140960795 + 180961 * 2 ^ 59
def prefixEnd_180961 : Nat := 4983230072969 + 3 ^ 40 * 180961 * 2
def baseEnd_180961 : Nat := 55063687536812872862389

theorem tailTrace_180961 : CollatzResearch.WordTrace tailWord_180961 prefixEnd_180961 55063687536812872862389 := by
  unfold tailWord_180961
  simp only [CollatzResearch.WordTrace]
  refine ⟨6600189897416677523382737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4400126598277785015588491 6600189897416677523382737)
  ·
    refine ⟨4950142423062508142537053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6600189897416677523382737 4950142423062508142537053)
    ·
      refine ⟨1856303408648440553451395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4950142423062508142537053 1856303408648440553451395)
      ·
        refine ⟨2784455112972660830177093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856303408648440553451395 2784455112972660830177093)
        ·
          refine ⟨522085333682373905658205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2784455112972660830177093 522085333682373905658205)
          ·
            refine ⟨195782000130890214621827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522085333682373905658205 195782000130890214621827)
            ·
              refine ⟨293673000196335321932741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195782000130890214621827 293673000196335321932741)
              ·
                refine ⟨55063687536812872862389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293673000196335321932741 55063687536812872862389)
                ·
                  rfl

theorem cell19_180961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_180961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_180961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_180961 prefixEnd_180961 := by exact prefixLift 180961
  have htrace : WordTrace (prefixWord ++ tailWord_180961) baseStart_180961 baseEnd_180961 := by
    simpa [prefixWord, tailWord_180961, baseEnd_180961] using wordTrace_append hprefix tailTrace_180961
  have hstable : (prefixWord ++ tailWord_180961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180961).length < 2 ^ (prefixWord ++ tailWord_180961).sum := by decide
  have hdescent : baseEnd_180961 < baseStart_180961 := by decide
  rcases family_descends (prefixWord ++ tailWord_180961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181054 : List Nat := [4, 2, 1, 2, 4, 1, 5]
def baseStart_181054 : Nat := 118140960795 + 181054 * 2 ^ 59
def prefixEnd_181054 : Nat := 4983230072969 + 3 ^ 40 * 181054 * 2
def baseEnd_181054 : Nat := 18363995342072070931823

theorem tailTrace_181054 : CollatzResearch.WordTrace tailWord_181054 prefixEnd_181054 18363995342072070931823 := by
  unfold tailWord_181054
  simp only [CollatzResearch.WordTrace]
  refine ⟨825447735759969300814777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4402387924053169604345477 825447735759969300814777)
  ·
    refine ⟨619085801819976975611083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 825447735759969300814777 619085801819976975611083)
    ·
      refine ⟨928628702729965463416625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619085801819976975611083 928628702729965463416625)
      ·
        refine ⟨696471527047474097562469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928628702729965463416625 696471527047474097562469)
        ·
          refine ⟨130588411321401393292963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 696471527047474097562469 130588411321401393292963)
          ·
            refine ⟨195882616982102089939445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130588411321401393292963 195882616982102089939445)
            ·
              refine ⟨18363995342072070931823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195882616982102089939445 18363995342072070931823)
              ·
                rfl

theorem cell19_181054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_181054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181054 prefixEnd_181054 := by exact prefixLift 181054
  have htrace : WordTrace (prefixWord ++ tailWord_181054) baseStart_181054 baseEnd_181054 := by
    simpa [prefixWord, tailWord_181054, baseEnd_181054] using wordTrace_append hprefix tailTrace_181054
  have hstable : (prefixWord ++ tailWord_181054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181054).length < 2 ^ (prefixWord ++ tailWord_181054).sum := by decide
  have hdescent : baseEnd_181054 < baseStart_181054 := by decide
  rcases family_descends (prefixWord ++ tailWord_181054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181077 : List Nat := [1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_181077 : Nat := 118140960795 + 181077 * 2 ^ 59
def prefixEnd_181077 : Nat := 4983230072969 + 3 ^ 40 * 181077 * 2
def baseEnd_181077 : Nat := 55098984577358974284295

theorem tailTrace_181077 : CollatzResearch.WordTrace tailWord_181077 prefixEnd_181077 55098984577358974284295 := by
  unfold tailWord_181077
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604420764996429334605485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4402947176664286223070323 6604420764996429334605485)
  ·
    refine ⟨2476657786873661000477057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6604420764996429334605485 2476657786873661000477057)
    ·
      refine ⟨1857493340155245750357793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2476657786873661000477057 1857493340155245750357793)
      ·
        refine ⟨1393120005116434312768345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857493340155245750357793 1393120005116434312768345)
        ·
          refine ⟨1044840003837325734576259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393120005116434312768345 1044840003837325734576259)
          ·
            refine ⟨1567260005755988601864389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044840003837325734576259 1567260005755988601864389)
            ·
              refine ⟨293861251079247862849573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1567260005755988601864389 293861251079247862849573)
              ·
                refine ⟨55098984577358974284295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293861251079247862849573 55098984577358974284295)
                ·
                  rfl

theorem cell19_181077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_181077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181077 prefixEnd_181077 := by exact prefixLift 181077
  have htrace : WordTrace (prefixWord ++ tailWord_181077) baseStart_181077 baseEnd_181077 := by
    simpa [prefixWord, tailWord_181077, baseEnd_181077] using wordTrace_append hprefix tailTrace_181077
  have hstable : (prefixWord ++ tailWord_181077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181077).length < 2 ^ (prefixWord ++ tailWord_181077).sum := by decide
  have hdescent : baseEnd_181077 < baseStart_181077 := by decide
  rcases family_descends (prefixWord ++ tailWord_181077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181096 : List Nat := [2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_181096 : Nat := 118140960795 + 181096 * 2 ^ 59
def prefixEnd_181096 : Nat := 4983230072969 + 3 ^ 40 * 181096 * 2
def baseEnd_181096 : Nat := 55104765989172559862021

theorem tailTrace_181096 : CollatzResearch.WordTrace tailWord_181096 prefixEnd_181096 55104765989172559862021 := by
  unfold tailWord_181096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302556875963797789773571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4403409167951730386364761 3302556875963797789773571)
  ·
    refine ⟨4953835313945696684660357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3302556875963797789773571 4953835313945696684660357)
    ·
      refine ⟨928844121364818128373817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4953835313945696684660357 928844121364818128373817)
      ·
        refine ⟨696633091023613596280363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928844121364818128373817 696633091023613596280363)
        ·
          refine ⟨1044949636535420394420545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696633091023613596280363 1044949636535420394420545)
          ·
            refine ⟨783712227401565295815409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044949636535420394420545 783712227401565295815409)
            ·
              refine ⟨587784170551173971861557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783712227401565295815409 587784170551173971861557)
              ·
                refine ⟨55104765989172559862021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587784170551173971861557 55104765989172559862021)
                ·
                  rfl

theorem cell19_181096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_181096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181096 prefixEnd_181096 := by exact prefixLift 181096
  have htrace : WordTrace (prefixWord ++ tailWord_181096) baseStart_181096 baseEnd_181096 := by
    simpa [prefixWord, tailWord_181096, baseEnd_181096] using wordTrace_append hprefix tailTrace_181096
  have hstable : (prefixWord ++ tailWord_181096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181096).length < 2 ^ (prefixWord ++ tailWord_181096).sum := by decide
  have hdescent : baseEnd_181096 < baseStart_181096 := by decide
  rcases family_descends (prefixWord ++ tailWord_181096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181151 : List Nat := [1, 1, 2, 5, 2, 2, 3, 3]
def baseStart_181151 : Nat := 118140960795 + 181151 * 2 ^ 59
def prefixEnd_181151 : Nat := 4983230072969 + 3 ^ 40 * 181151 * 2
def baseEnd_181151 : Nat := 55121501654948728639649

theorem tailTrace_181151 : CollatzResearch.WordTrace tailWord_181151 prefixEnd_181151 55121501654948728639649 := by
  unfold tailWord_181151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6607119766728339972799307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4404746511152226648532871 6607119766728339972799307)
  ·
    refine ⟨9910679650092509959198961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6607119766728339972799307 9910679650092509959198961)
    ·
      refine ⟨7433009737569382469399221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9910679650092509959198961 7433009737569382469399221)
      ·
        refine ⟨696844662897129606506177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7433009737569382469399221 696844662897129606506177)
        ·
          refine ⟨522633497172847204879633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696844662897129606506177 522633497172847204879633)
          ·
            refine ⟨391975122879635403659725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522633497172847204879633 391975122879635403659725)
            ·
              refine ⟨146990671079863276372397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 391975122879635403659725 146990671079863276372397)
              ·
                refine ⟨55121501654948728639649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146990671079863276372397 55121501654948728639649)
                ·
                  rfl

theorem cell19_181151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_181151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181151 prefixEnd_181151 := by exact prefixLift 181151
  have htrace : WordTrace (prefixWord ++ tailWord_181151) baseStart_181151 baseEnd_181151 := by
    simpa [prefixWord, tailWord_181151, baseEnd_181151] using wordTrace_append hprefix tailTrace_181151
  have hstable : (prefixWord ++ tailWord_181151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181151).length < 2 ^ (prefixWord ++ tailWord_181151).sum := by decide
  have hdescent : baseEnd_181151 < baseStart_181151 := by decide
  rcases family_descends (prefixWord ++ tailWord_181151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181155 : List Nat := [1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_181155 : Nat := 118140960795 + 181155 * 2 ^ 59
def prefixEnd_181155 : Nat := 4983230072969 + 3 ^ 40 * 181155 * 2
def baseEnd_181155 : Nat := 55122718794277904550749

theorem tailTrace_181155 : CollatzResearch.WordTrace tailWord_181155 prefixEnd_181155 55122718794277904550749 := by
  unfold tailWord_181155
  simp only [CollatzResearch.WordTrace]
  refine ⟨6607265658713848655944919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4404843772475899103963279 6607265658713848655944919)
  ·
    refine ⟨9910898488070772983917379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6607265658713848655944919 9910898488070772983917379)
    ·
      refine ⟨14866347732106159475876069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9910898488070772983917379 14866347732106159475876069)
      ·
        refine ⟨2787440199769904901726763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14866347732106159475876069 2787440199769904901726763)
        ·
          refine ⟨4181160299654857352590145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2787440199769904901726763 4181160299654857352590145)
          ·
            refine ⟨3135870224741143014442609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4181160299654857352590145 3135870224741143014442609)
            ·
              refine ⟨2351902668555857260831957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135870224741143014442609 2351902668555857260831957)
              ·
                refine ⟨55122718794277904550749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2351902668555857260831957 55122718794277904550749)
                ·
                  rfl

theorem cell19_181155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_181155 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181155 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181155 prefixEnd_181155 := by exact prefixLift 181155
  have htrace : WordTrace (prefixWord ++ tailWord_181155) baseStart_181155 baseEnd_181155 := by
    simpa [prefixWord, tailWord_181155, baseEnd_181155] using wordTrace_append hprefix tailTrace_181155
  have hstable : (prefixWord ++ tailWord_181155).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181155).length < 2 ^ (prefixWord ++ tailWord_181155).sum := by decide
  have hdescent : baseEnd_181155 < baseStart_181155 := by decide
  rcases family_descends (prefixWord ++ tailWord_181155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181206 : List Nat := [5, 2, 1, 1, 2, 1, 4, 3]
def baseStart_181206 : Nat := 118140960795 + 181206 * 2 ^ 59
def prefixEnd_181206 : Nat := 4983230072969 + 3 ^ 40 * 181206 * 2
def baseEnd_181206 : Nat := 55138237320724897417277

theorem tailTrace_181206 : CollatzResearch.WordTrace tailWord_181206 prefixEnd_181206 55138237320724897417277 := by
  unfold tailWord_181206
  simp only [CollatzResearch.WordTrace]
  refine ⟨413070361345567772878217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4406083854352722910700981 413070361345567772878217)
  ·
    refine ⟨309802771009175829658663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 413070361345567772878217 309802771009175829658663)
    ·
      refine ⟨464704156513763744487995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309802771009175829658663 464704156513763744487995)
      ·
        refine ⟨697056234770645616731993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464704156513763744487995 697056234770645616731993)
        ·
          refine ⟨522792176077984212548995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697056234770645616731993 522792176077984212548995)
          ·
            refine ⟨784188264116976318823493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522792176077984212548995 784188264116976318823493)
            ·
              refine ⟨147035299521933059779405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 784188264116976318823493 147035299521933059779405)
              ·
                refine ⟨55138237320724897417277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147035299521933059779405 55138237320724897417277)
                ·
                  rfl

theorem cell19_181206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_181206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181206 prefixEnd_181206 := by exact prefixLift 181206
  have htrace : WordTrace (prefixWord ++ tailWord_181206) baseStart_181206 baseEnd_181206 := by
    simpa [prefixWord, tailWord_181206, baseEnd_181206] using wordTrace_append hprefix tailTrace_181206
  have hstable : (prefixWord ++ tailWord_181206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181206).length < 2 ^ (prefixWord ++ tailWord_181206).sum := by decide
  have hdescent : baseEnd_181206 < baseStart_181206 := by decide
  rcases family_descends (prefixWord ++ tailWord_181206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181208 : List Nat := [2, 1, 2, 2, 2, 5, 2, 3]
def baseStart_181208 : Nat := 118140960795 + 181208 * 2 ^ 59
def prefixEnd_181208 : Nat := 4983230072969 + 3 ^ 40 * 181208 * 2
def baseEnd_181208 : Nat := 55138845890389485372827

theorem tailTrace_181208 : CollatzResearch.WordTrace tailWord_181208 prefixEnd_181208 55138845890389485372827 := by
  unfold tailWord_181208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3304599363760919353812139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4406132485014559138416185 3304599363760919353812139)
  ·
    refine ⟨4956899045641379030718209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3304599363760919353812139 4956899045641379030718209)
    ·
      refine ⟨3717674284231034273038657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4956899045641379030718209 3717674284231034273038657)
      ·
        refine ⟨2788255713173275704778993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3717674284231034273038657 2788255713173275704778993)
        ·
          refine ⟨2091191784879956778584245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788255713173275704778993 2091191784879956778584245)
          ·
            refine ⟨196049229832495947992273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2091191784879956778584245 196049229832495947992273)
            ·
              refine ⟨147036922374371960994205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196049229832495947992273 147036922374371960994205)
              ·
                refine ⟨55138845890389485372827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147036922374371960994205 55138845890389485372827)
                ·
                  rfl

theorem cell19_181208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_181208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181208 prefixEnd_181208 := by exact prefixLift 181208
  have htrace : WordTrace (prefixWord ++ tailWord_181208) baseStart_181208 baseEnd_181208 := by
    simpa [prefixWord, tailWord_181208, baseEnd_181208] using wordTrace_append hprefix tailTrace_181208
  have hstable : (prefixWord ++ tailWord_181208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181208).length < 2 ^ (prefixWord ++ tailWord_181208).sum := by decide
  have hdescent : baseEnd_181208 < baseStart_181208 := by decide
  rcases family_descends (prefixWord ++ tailWord_181208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181210 : List Nat := [3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_181210 : Nat := 118140960795 + 181210 * 2 ^ 59
def prefixEnd_181210 : Nat := 4983230072969 + 3 ^ 40 * 181210 * 2
def baseEnd_181210 : Nat := 55139454460054073328377

theorem tailTrace_181210 : CollatzResearch.WordTrace tailWord_181210 prefixEnd_181210 55139454460054073328377 := by
  unfold tailWord_181210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652317918378648262299271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4406181115676395366131389 1652317918378648262299271)
  ·
    refine ⟨2478476877567972393448907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652317918378648262299271 2478476877567972393448907)
    ·
      refine ⟨3717715316351958590173361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478476877567972393448907 3717715316351958590173361)
      ·
        refine ⟨2788286487263968942630021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3717715316351958590173361 2788286487263968942630021)
        ·
          refine ⟨522803716361994176743129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2788286487263968942630021 522803716361994176743129)
          ·
            refine ⟨392102787271495632557347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522803716361994176743129 392102787271495632557347)
            ·
              refine ⟨588154180907243448836021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392102787271495632557347 588154180907243448836021)
              ·
                refine ⟨55139454460054073328377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 588154180907243448836021 55139454460054073328377)
                ·
                  rfl

theorem cell19_181210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_181210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181210 prefixEnd_181210 := by exact prefixLift 181210
  have htrace : WordTrace (prefixWord ++ tailWord_181210) baseStart_181210 baseEnd_181210 := by
    simpa [prefixWord, tailWord_181210, baseEnd_181210] using wordTrace_append hprefix tailTrace_181210
  have hstable : (prefixWord ++ tailWord_181210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181210).length < 2 ^ (prefixWord ++ tailWord_181210).sum := by decide
  have hdescent : baseEnd_181210 < baseStart_181210 := by decide
  rcases family_descends (prefixWord ++ tailWord_181210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181231 : List Nat := [1, 1, 2, 1, 4, 3, 7]
def baseStart_181231 : Nat := 118140960795 + 181231 * 2 ^ 59
def prefixEnd_181231 : Nat := 4983230072969 + 3 ^ 40 * 181231 * 2
def baseEnd_181231 : Nat := 18381948147177415620551

theorem tailTrace_181231 : CollatzResearch.WordTrace tailWord_181231 prefixEnd_181231 18381948147177415620551 := by
  unfold tailWord_181231
  simp only [CollatzResearch.WordTrace]
  refine ⟨6610037606438513635711547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4406691737625675757141031 6610037606438513635711547)
  ·
    refine ⟨9915056409657770453567321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6610037606438513635711547 9915056409657770453567321)
    ·
      refine ⟨7436292307243327840175491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9915056409657770453567321 7436292307243327840175491)
      ·
        refine ⟨11154438460864991760263237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7436292307243327840175491 11154438460864991760263237)
        ·
          refine ⟨2091457211412185955049357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11154438460864991760263237 2091457211412185955049357)
          ·
            refine ⟨784296454279569733143509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2091457211412185955049357 784296454279569733143509)
            ·
              refine ⟨18381948147177415620551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 784296454279569733143509 18381948147177415620551)
              ·
                rfl

theorem cell19_181231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_181231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181231 prefixEnd_181231 := by exact prefixLift 181231
  have htrace : WordTrace (prefixWord ++ tailWord_181231) baseStart_181231 baseEnd_181231 := by
    simpa [prefixWord, tailWord_181231, baseEnd_181231] using wordTrace_append hprefix tailTrace_181231
  have hstable : (prefixWord ++ tailWord_181231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181231).length < 2 ^ (prefixWord ++ tailWord_181231).sum := by decide
  have hdescent : baseEnd_181231 < baseStart_181231 := by decide
  rcases family_descends (prefixWord ++ tailWord_181231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181288 : List Nat := [2, 1, 5, 11]
def baseStart_181288 : Nat := 118140960795 + 181288 * 2 ^ 59
def prefixEnd_181288 : Nat := 4983230072969 + 3 ^ 40 * 181288 * 2
def baseEnd_181288 : Nat := 681027020703370414751

theorem tailTrace_181288 : CollatzResearch.WordTrace tailWord_181288 prefixEnd_181288 681027020703370414751 := by
  unfold tailWord_181288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306058283616006185268259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4408077711488008247024345 3306058283616006185268259)
  ·
    refine ⟨4959087425424009277902389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3306058283616006185268259 4959087425424009277902389)
    ·
      refine ⟨464914446133500869803349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4959087425424009277902389 464914446133500869803349)
      ·
        refine ⟨681027020703370414751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 464914446133500869803349 681027020703370414751)
        ·
          rfl

theorem cell19_181288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 11].length) (baseStart_181288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181288 prefixEnd_181288 := by exact prefixLift 181288
  have htrace : WordTrace (prefixWord ++ tailWord_181288) baseStart_181288 baseEnd_181288 := by
    simpa [prefixWord, tailWord_181288, baseEnd_181288] using wordTrace_append hprefix tailTrace_181288
  have hstable : (prefixWord ++ tailWord_181288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181288).length < 2 ^ (prefixWord ++ tailWord_181288).sum := by decide
  have hdescent : baseEnd_181288 < baseStart_181288 := by decide
  rcases family_descends (prefixWord ++ tailWord_181288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181305 : List Nat := [1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_181305 : Nat := 118140960795 + 181305 * 2 ^ 59
def prefixEnd_181305 : Nat := 4983230072969 + 3 ^ 40 * 181305 * 2
def baseEnd_181305 : Nat := 55168361519122001217007

theorem tailTrace_181305 : CollatzResearch.WordTrace tailWord_181305 prefixEnd_181305 55168361519122001217007 := by
  unfold tailWord_181305
  simp only [CollatzResearch.WordTrace]
  refine ⟨6612736608170424273905369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4408491072113616182603579 6612736608170424273905369)
  ·
    refine ⟨4959552456127818205429027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6612736608170424273905369 4959552456127818205429027)
    ·
      refine ⟨7439328684191727308143541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959552456127818205429027 7439328684191727308143541)
      ·
        refine ⟨697437064142974435138457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7439328684191727308143541 697437064142974435138457)
        ·
          refine ⟨523077798107230826353843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697437064142974435138457 523077798107230826353843)
          ·
            refine ⟨784616697160846239530765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523077798107230826353843 784616697160846239530765)
            ·
              refine ⟨294231261435317339824037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784616697160846239530765 294231261435317339824037)
              ·
                refine ⟨55168361519122001217007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294231261435317339824037 55168361519122001217007)
                ·
                  rfl

theorem cell19_181305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_181305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181305 prefixEnd_181305 := by exact prefixLift 181305
  have htrace : WordTrace (prefixWord ++ tailWord_181305) baseStart_181305 baseEnd_181305 := by
    simpa [prefixWord, tailWord_181305, baseEnd_181305] using wordTrace_append hprefix tailTrace_181305
  have hstable : (prefixWord ++ tailWord_181305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181305).length < 2 ^ (prefixWord ++ tailWord_181305).sum := by decide
  have hdescent : baseEnd_181305 < baseStart_181305 := by decide
  rcases family_descends (prefixWord ++ tailWord_181305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181341 : List Nat := [1, 4, 4, 1, 2, 1, 6]
def baseStart_181341 : Nat := 118140960795 + 181341 * 2 ^ 59
def prefixEnd_181341 : Nat := 4983230072969 + 3 ^ 40 * 181341 * 2
def baseEnd_181341 : Nat := 18393105257694861472303

theorem tailTrace_181341 : CollatzResearch.WordTrace tailWord_181341 prefixEnd_181341 18393105257694861472303 := by
  unfold tailWord_181341
  simp only [CollatzResearch.WordTrace]
  refine ⟨6614049636040002422215877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4409366424026668281477251 6614049636040002422215877)
  ·
    refine ⟨1240134306757500454165477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6614049636040002422215877 1240134306757500454165477)
    ·
      refine ⟨232525182517031335156027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1240134306757500454165477 232525182517031335156027)
      ·
        refine ⟨348787773775547002734041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232525182517031335156027 348787773775547002734041)
        ·
          refine ⟨261590830331660252050531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348787773775547002734041 261590830331660252050531)
          ·
            refine ⟨392386245497490378075797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261590830331660252050531 392386245497490378075797)
            ·
              refine ⟨18393105257694861472303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 392386245497490378075797 18393105257694861472303)
              ·
                rfl

theorem cell19_181341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_181341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181341 prefixEnd_181341 := by exact prefixLift 181341
  have htrace : WordTrace (prefixWord ++ tailWord_181341) baseStart_181341 baseEnd_181341 := by
    simpa [prefixWord, tailWord_181341, baseEnd_181341] using wordTrace_append hprefix tailTrace_181341
  have hstable : (prefixWord ++ tailWord_181341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181341).length < 2 ^ (prefixWord ++ tailWord_181341).sum := by decide
  have hdescent : baseEnd_181341 < baseStart_181341 := by decide
  rcases family_descends (prefixWord ++ tailWord_181341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181381 : List Nat := [1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_181381 : Nat := 118140960795 + 181381 * 2 ^ 59
def prefixEnd_181381 : Nat := 4983230072969 + 3 ^ 40 * 181381 * 2
def baseEnd_181381 : Nat := 55191487166376343527911

theorem tailTrace_181381 : CollatzResearch.WordTrace tailWord_181381 prefixEnd_181381 55191487166376343527911 := by
  unfold tailWord_181381
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615508555895089253671997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4410339037263392835781331 6615508555895089253671997)
  ·
    refine ⟨2480815708460658470126999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6615508555895089253671997 2480815708460658470126999)
    ·
      refine ⟨3721223562690987705190499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2480815708460658470126999 3721223562690987705190499)
      ·
        refine ⟨5581835344036481557785749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721223562690987705190499 5581835344036481557785749)
        ·
          refine ⟨261648531751710073021207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5581835344036481557785749 261648531751710073021207)
          ·
            refine ⟨392472797627565109531811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261648531751710073021207 392472797627565109531811)
            ·
              refine ⟨588709196441347664297717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392472797627565109531811 588709196441347664297717)
              ·
                refine ⟨55191487166376343527911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 588709196441347664297717 55191487166376343527911)
                ·
                  rfl

theorem cell19_181381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_181381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181381 prefixEnd_181381 := by exact prefixLift 181381
  have htrace : WordTrace (prefixWord ++ tailWord_181381) baseStart_181381 baseEnd_181381 := by
    simpa [prefixWord, tailWord_181381, baseEnd_181381] using wordTrace_append hprefix tailTrace_181381
  have hstable : (prefixWord ++ tailWord_181381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181381).length < 2 ^ (prefixWord ++ tailWord_181381).sum := by decide
  have hdescent : baseEnd_181381 < baseStart_181381 := by decide
  rcases family_descends (prefixWord ++ tailWord_181381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181400 : List Nat := [2, 1, 2, 4, 2, 3, 5]
def baseStart_181400 : Nat := 118140960795 + 181400 * 2 ^ 59
def prefixEnd_181400 : Nat := 4983230072969 + 3 ^ 40 * 181400 * 2
def baseEnd_181400 : Nat := 18399089526063309701879

theorem tailTrace_181400 : CollatzResearch.WordTrace tailWord_181400 prefixEnd_181400 18399089526063309701879 := by
  unfold tailWord_181400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308100771413127749306827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4410801028550836999075769 3308100771413127749306827)
  ·
    refine ⟨4962151157119691623960241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3308100771413127749306827 4962151157119691623960241)
    ·
      refine ⟨3721613367839768717970181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4962151157119691623960241 3721613367839768717970181)
      ·
        refine ⟨697802506469956634619409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3721613367839768717970181 697802506469956634619409)
        ·
          refine ⟨523351879852467475964557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697802506469956634619409 523351879852467475964557)
          ·
            refine ⟨196256954944675303486709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 523351879852467475964557 196256954944675303486709)
            ·
              refine ⟨18399089526063309701879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196256954944675303486709 18399089526063309701879)
              ·
                rfl

theorem cell19_181400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_181400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181400 prefixEnd_181400 := by exact prefixLift 181400
  have htrace : WordTrace (prefixWord ++ tailWord_181400) baseStart_181400 baseEnd_181400 := by
    simpa [prefixWord, tailWord_181400, baseEnd_181400] using wordTrace_append hprefix tailTrace_181400
  have hstable : (prefixWord ++ tailWord_181400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181400).length < 2 ^ (prefixWord ++ tailWord_181400).sum := by decide
  have hdescent : baseEnd_181400 < baseStart_181400 := by decide
  rcases family_descends (prefixWord ++ tailWord_181400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181438 : List Nat := [4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_181438 : Nat := 118140960795 + 181438 * 2 ^ 59
def prefixEnd_181438 : Nat := 4983230072969 + 3 ^ 40 * 181438 * 2
def baseEnd_181438 : Nat := 55208831401817100261089

theorem tailTrace_181438 : CollatzResearch.WordTrace tailWord_181438 prefixEnd_181438 55208831401817100261089 := by
  unfold tailWord_181438
  simp only [CollatzResearch.WordTrace]
  refine ⟨827198439586073498562121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4411725011125725325664645 827198439586073498562121)
  ·
    refine ⟨620398829689555123921591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 827198439586073498562121 620398829689555123921591)
    ·
      refine ⟨930598244534332685882387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620398829689555123921591 930598244534332685882387)
      ·
        refine ⟨1395897366801499028823581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930598244534332685882387 1395897366801499028823581)
        ·
          refine ⟨523461512550562135808843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1395897366801499028823581 523461512550562135808843)
          ·
            refine ⟨785192268825843203713265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523461512550562135808843 785192268825843203713265)
            ·
              refine ⟨588894201619382402784949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785192268825843203713265 588894201619382402784949)
              ·
                refine ⟨55208831401817100261089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 588894201619382402784949 55208831401817100261089)
                ·
                  rfl

theorem cell19_181438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_181438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181438 prefixEnd_181438 := by exact prefixLift 181438
  have htrace : WordTrace (prefixWord ++ tailWord_181438) baseStart_181438 baseEnd_181438 := by
    simpa [prefixWord, tailWord_181438, baseEnd_181438] using wordTrace_append hprefix tailTrace_181438
  have hstable : (prefixWord ++ tailWord_181438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181438).length < 2 ^ (prefixWord ++ tailWord_181438).sum := by decide
  have hdescent : baseEnd_181438 < baseStart_181438 := by decide
  rcases family_descends (prefixWord ++ tailWord_181438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181453 : List Nat := [1, 6, 2, 2, 2, 6]
def baseStart_181453 : Nat := 118140960795 + 181453 * 2 ^ 59
def prefixEnd_181453 : Nat := 4983230072969 + 3 ^ 40 * 181453 * 2
def baseEnd_181453 : Nat := 6134821741589056658635

theorem tailTrace_181453 : CollatzResearch.WordTrace tailWord_181453 prefixEnd_181453 6134821741589056658635 := by
  unfold tailWord_181453
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618134611634245550293013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4412089741089497033528675 6618134611634245550293013)
  ·
    refine ⟨310225059920355260169985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6618134611634245550293013 310225059920355260169985)
    ·
      refine ⟨232668794940266445127489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310225059920355260169985 232668794940266445127489)
      ·
        refine ⟨174501596205199833845617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232668794940266445127489 174501596205199833845617)
        ·
          refine ⟨130876197153899875384213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174501596205199833845617 130876197153899875384213)
          ·
            refine ⟨6134821741589056658635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130876197153899875384213 6134821741589056658635)
            ·
              rfl

theorem cell19_181453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 6].length) (baseStart_181453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181453 prefixEnd_181453 := by exact prefixLift 181453
  have htrace : WordTrace (prefixWord ++ tailWord_181453) baseStart_181453 baseEnd_181453 := by
    simpa [prefixWord, tailWord_181453, baseEnd_181453] using wordTrace_append hprefix tailTrace_181453
  have hstable : (prefixWord ++ tailWord_181453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181453).length < 2 ^ (prefixWord ++ tailWord_181453).sum := by decide
  have hdescent : baseEnd_181453 < baseStart_181453 := by decide
  rcases family_descends (prefixWord ++ tailWord_181453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181516 : List Nat := [2, 2, 1, 2, 2, 4, 6]
def baseStart_181516 : Nat := 118140960795 + 181516 * 2 ^ 59
def prefixEnd_181516 : Nat := 4983230072969 + 3 ^ 40 * 181516 * 2
def baseEnd_181516 : Nat := 18410855206245343509181

theorem tailTrace_181516 : CollatzResearch.WordTrace tailWord_181516 prefixEnd_181516 18410855206245343509181 := by
  unfold tailWord_181516
  simp only [CollatzResearch.WordTrace]
  refine ⟨3310216205203003654918201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4413621606937338206557601 3310216205203003654918201)
  ·
    refine ⟨2482662153902252741188651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3310216205203003654918201 2482662153902252741188651)
    ·
      refine ⟨3723993230853379111782977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2482662153902252741188651 3723993230853379111782977)
      ·
        refine ⟨2792994923140034333837233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3723993230853379111782977 2792994923140034333837233)
        ·
          refine ⟨2094746192355025750377925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2792994923140034333837233 2094746192355025750377925)
          ·
            refine ⟨392764911066567328195861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2094746192355025750377925 392764911066567328195861)
            ·
              refine ⟨18410855206245343509181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 392764911066567328195861 18410855206245343509181)
              ·
                rfl

theorem cell19_181516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_181516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181516 prefixEnd_181516 := by exact prefixLift 181516
  have htrace : WordTrace (prefixWord ++ tailWord_181516) baseStart_181516 baseEnd_181516 := by
    simpa [prefixWord, tailWord_181516, baseEnd_181516] using wordTrace_append hprefix tailTrace_181516
  have hstable : (prefixWord ++ tailWord_181516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181516).length < 2 ^ (prefixWord ++ tailWord_181516).sum := by decide
  have hdescent : baseEnd_181516 < baseStart_181516 := by decide
  rcases family_descends (prefixWord ++ tailWord_181516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181592 : List Nat := [2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_181592 : Nat := 118140960795 + 181592 * 2 ^ 59
def prefixEnd_181592 : Nat := 4983230072969 + 3 ^ 40 * 181592 * 2
def baseEnd_181592 : Nat := 55255691265990372838447

theorem tailTrace_181592 : CollatzResearch.WordTrace tailWord_181592 prefixEnd_181592 55255691265990372838447 := by
  unfold tailWord_181592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311602179065336144801515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4415469572087114859735353 3311602179065336144801515)
  ·
    refine ⟨4967403268598004217202273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3311602179065336144801515 4967403268598004217202273)
    ·
      refine ⟨3725552451448503162901705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4967403268598004217202273 3725552451448503162901705)
      ·
        refine ⟨2794164338586377372176279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3725552451448503162901705 2794164338586377372176279)
        ·
          refine ⟨4191246507879566058264419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794164338586377372176279 4191246507879566058264419)
          ·
            refine ⟨6286869761819349087396629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191246507879566058264419 6286869761819349087396629)
            ·
              refine ⟨294697020085281988471717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6286869761819349087396629 294697020085281988471717)
              ·
                refine ⟨55255691265990372838447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294697020085281988471717 55255691265990372838447)
                ·
                  rfl

theorem cell19_181592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_181592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181592 prefixEnd_181592 := by exact prefixLift 181592
  have htrace : WordTrace (prefixWord ++ tailWord_181592) baseStart_181592 baseEnd_181592 := by
    simpa [prefixWord, tailWord_181592, baseEnd_181592] using wordTrace_append hprefix tailTrace_181592
  have hstable : (prefixWord ++ tailWord_181592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181592).length < 2 ^ (prefixWord ++ tailWord_181592).sum := by decide
  have hdescent : baseEnd_181592 < baseStart_181592 := by decide
  rcases family_descends (prefixWord ++ tailWord_181592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181662 : List Nat := [4, 3, 1, 2, 2, 1, 3, 3]
def baseStart_181662 : Nat := 118140960795 + 181662 * 2 ^ 59
def prefixEnd_181662 : Nat := 4983230072969 + 3 ^ 40 * 181662 * 2
def baseEnd_181662 : Nat := 55276991204250951282701

theorem tailTrace_181662 : CollatzResearch.WordTrace tailWord_181662 prefixEnd_181662 55276991204250951282701 := by
  unfold tailWord_181662
  simp only [CollatzResearch.WordTrace]
  refine ⟨828219683484634280581405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4417171645251382829767493 828219683484634280581405)
  ·
    refine ⟨310582381306737855218027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 828219683484634280581405 310582381306737855218027)
    ·
      refine ⟨465873571960106782827041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310582381306737855218027 465873571960106782827041)
      ·
        refine ⟨349405178970080087120281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465873571960106782827041 349405178970080087120281)
        ·
          refine ⟨262053884227560065340211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349405178970080087120281 262053884227560065340211)
          ·
            refine ⟨393080826341340098010317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262053884227560065340211 393080826341340098010317)
            ·
              refine ⟨147405309878002536753869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393080826341340098010317 147405309878002536753869)
              ·
                refine ⟨55276991204250951282701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147405309878002536753869 55276991204250951282701)
                ·
                  rfl

theorem cell19_181662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_181662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181662 prefixEnd_181662 := by exact prefixLift 181662
  have htrace : WordTrace (prefixWord ++ tailWord_181662) baseStart_181662 baseEnd_181662 := by
    simpa [prefixWord, tailWord_181662, baseEnd_181662] using wordTrace_append hprefix tailTrace_181662
  have hstable : (prefixWord ++ tailWord_181662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181662).length < 2 ^ (prefixWord ++ tailWord_181662).sum := by decide
  have hdescent : baseEnd_181662 < baseStart_181662 := by decide
  rcases family_descends (prefixWord ++ tailWord_181662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
