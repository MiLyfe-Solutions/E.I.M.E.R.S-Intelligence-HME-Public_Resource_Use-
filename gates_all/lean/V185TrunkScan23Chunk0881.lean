import V185TrunkScan23Chunk0880

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5213802 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_5213802 : Nat := 118140960795 + 5213802 * 2 ^ 59
def prefixEnd_5213802 : Nat := 4983230072969 + 3 ^ 40 * 5213802 * 2
def baseEnd_5213802 : Nat := 892395487791038403132389

theorem tailTrace_5213802 : CollatzResearch.WordTrace tailWord_5213802 prefixEnd_5213802 892395487791038403132389 := by
  unfold tailWord_5213802
  simp only [CollatzResearch.WordTrace]
  refine ⟨47540745364323318833660915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126775320971528850223095773 47540745364323318833660915)
  ·
    refine ⟨71311118046484978250491373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47540745364323318833660915 71311118046484978250491373)
    ·
      refine ⟨26741669267431866843934265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71311118046484978250491373 26741669267431866843934265)
      ·
        refine ⟨20056251950573900132950699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26741669267431866843934265 20056251950573900132950699)
        ·
          refine ⟨30084377925860850199426049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20056251950573900132950699 30084377925860850199426049)
          ·
            refine ⟨22563283444395637649569537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30084377925860850199426049 22563283444395637649569537)
            ·
              refine ⟨16922462583296728237177153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22563283444395637649569537 16922462583296728237177153)
              ·
                refine ⟨12691846937472546177882865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16922462583296728237177153 12691846937472546177882865)
                ·
                  refine ⟨9518885203104409633412149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12691846937472546177882865 9518885203104409633412149)
                  ·
                    refine ⟨892395487791038403132389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9518885203104409633412149 892395487791038403132389)
                    ·
                      rfl

theorem cell23_5213802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_5213802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213802 prefixEnd_5213802 := by exact prefixLift 5213802
  have htrace : WordTrace (prefixWord ++ tailWord_5213802) baseStart_5213802 baseEnd_5213802 := by
    simpa [prefixWord, tailWord_5213802, baseEnd_5213802] using wordTrace_append hprefix tailTrace_5213802
  have hstable : (prefixWord ++ tailWord_5213802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213802).length < 2 ^ (prefixWord ++ tailWord_5213802).sum := by decide
  have hdescent : baseEnd_5213802 < baseStart_5213802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213879 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 6]
def baseStart_5213879 : Nat := 118140960795 + 5213879 * 2 ^ 59
def prefixEnd_5213879 : Nat := 4983230072969 + 3 ^ 40 * 5213879 * 2
def baseEnd_5213879 : Nat := 297469555709279045348257

theorem tailTrace_5213879 : CollatzResearch.WordTrace tailWord_5213879 prefixEnd_5213879 297469555709279045348257 := by
  unfold tailWord_5213879
  simp only [CollatzResearch.WordTrace]
  refine ⟨190165789878014317485196691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126777193252009544990131127 190165789878014317485196691)
  ·
    refine ⟨285248684817021476227795037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190165789878014317485196691 285248684817021476227795037)
    ·
      refine ⟨106968256806383053585423139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285248684817021476227795037 106968256806383053585423139)
      ·
        refine ⟨160452385209574580378134709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106968256806383053585423139 160452385209574580378134709)
        ·
          refine ⟨15042411113397616910450129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160452385209574580378134709 15042411113397616910450129)
          ·
            refine ⟨11281808335048212682837597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15042411113397616910450129 11281808335048212682837597)
            ·
              refine ⟨4230678125643079756064099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11281808335048212682837597 4230678125643079756064099)
              ·
                refine ⟨6346017188464619634096149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230678125643079756064099 6346017188464619634096149)
                ·
                  refine ⟨297469555709279045348257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6346017188464619634096149 297469555709279045348257)
                  ·
                    rfl

theorem cell23_5213879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 6].length) (baseStart_5213879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213879 prefixEnd_5213879 := by exact prefixLift 5213879
  have htrace : WordTrace (prefixWord ++ tailWord_5213879) baseStart_5213879 baseEnd_5213879 := by
    simpa [prefixWord, tailWord_5213879, baseEnd_5213879] using wordTrace_append hprefix tailTrace_5213879
  have hstable : (prefixWord ++ tailWord_5213879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213879).length < 2 ^ (prefixWord ++ tailWord_5213879).sum := by decide
  have hdescent : baseEnd_5213879 < baseStart_5213879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213900 : List Nat := [2, 2, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_5213900 : Nat := 118140960795 + 5213900 * 2 ^ 59
def prefixEnd_5213900 : Nat := 4983230072969 + 3 ^ 40 * 5213900 * 2
def baseEnd_5213900 : Nat := 892412261492418608657239

theorem tailTrace_5213900 : CollatzResearch.WordTrace tailWord_5213900 prefixEnd_5213900 892412261492418608657239 := by
  unfold tailWord_5213900
  simp only [CollatzResearch.WordTrace]
  refine ⟨95083277905469119035855577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126777703873958825381140769 95083277905469119035855577)
  ·
    refine ⟨71312458429101839276891683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95083277905469119035855577 71312458429101839276891683)
    ·
      refine ⟨106968687643652758915337525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71312458429101839276891683 106968687643652758915337525)
      ·
        refine ⟨10028314466592446148312893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106968687643652758915337525 10028314466592446148312893)
        ·
          refine ⟨3760617924972167305617335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10028314466592446148312893 3760617924972167305617335)
          ·
            refine ⟨5640926887458250958426003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760617924972167305617335 5640926887458250958426003)
            ·
              refine ⟨8461390331187376437639005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640926887458250958426003 8461390331187376437639005)
              ·
                refine ⟨3173021374195266164114627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8461390331187376437639005 3173021374195266164114627)
                ·
                  refine ⟨4759532061292899246171941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173021374195266164114627 4759532061292899246171941)
                  ·
                    refine ⟨892412261492418608657239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4759532061292899246171941 892412261492418608657239)
                    ·
                      rfl

theorem cell23_5213900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_5213900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213900 prefixEnd_5213900 := by exact prefixLift 5213900
  have htrace : WordTrace (prefixWord ++ tailWord_5213900) baseStart_5213900 baseEnd_5213900 := by
    simpa [prefixWord, tailWord_5213900, baseEnd_5213900] using wordTrace_append hprefix tailTrace_5213900
  have hstable : (prefixWord ++ tailWord_5213900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213900).length < 2 ^ (prefixWord ++ tailWord_5213900).sum := by decide
  have hdescent : baseEnd_5213900 < baseStart_5213900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213923 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5213923 : Nat := 118140960795 + 5213923 * 2 ^ 59
def prefixEnd_5213923 : Nat := 4983230072969 + 3 ^ 40 * 5213923 * 2
def baseEnd_5213923 : Nat := 2677248594532309235984111

theorem tailTrace_5213923 : CollatzResearch.WordTrace tailWord_5213923 prefixEnd_5213923 2677248594532309235984111 := by
  unfold tailWord_5213923
  simp only [CollatzResearch.WordTrace]
  refine ⟨190167394689854912999798423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126778263126569941999865615 190167394689854912999798423)
  ·
    refine ⟨285251092034782369499697635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190167394689854912999798423 285251092034782369499697635)
    ·
      refine ⟨427876638052173554249546453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285251092034782369499697635 427876638052173554249546453)
      ·
        refine ⟨10028358704347817677723745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 427876638052173554249546453 10028358704347817677723745)
        ·
          refine ⟨7521269028260863258292809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10028358704347817677723745 7521269028260863258292809)
          ·
            refine ⟨5640951771195647443719607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7521269028260863258292809 5640951771195647443719607)
            ·
              refine ⟨8461427656793471165579411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640951771195647443719607 8461427656793471165579411)
              ·
                refine ⟨12692141485190206748369117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8461427656793471165579411 12692141485190206748369117)
                ·
                  refine ⟨4759553056946327530638419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12692141485190206748369117 4759553056946327530638419)
                  ·
                    refine ⟨7139329585419491295957629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759553056946327530638419 7139329585419491295957629)
                    ·
                      refine ⟨2677248594532309235984111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7139329585419491295957629 2677248594532309235984111)
                      ·
                        rfl

theorem cell23_5213923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5213923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213923 prefixEnd_5213923 := by exact prefixLift 5213923
  have htrace : WordTrace (prefixWord ++ tailWord_5213923) baseStart_5213923 baseEnd_5213923 := by
    simpa [prefixWord, tailWord_5213923, baseEnd_5213923] using wordTrace_append hprefix tailTrace_5213923
  have hstable : (prefixWord ++ tailWord_5213923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213923).length < 2 ^ (prefixWord ++ tailWord_5213923).sum := by decide
  have hdescent : baseEnd_5213923 < baseStart_5213923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213932 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_5213932 : Nat := 118140960795 + 5213932 * 2 ^ 59
def prefixEnd_5213932 : Nat := 4983230072969 + 3 ^ 40 * 5213932 * 2
def baseEnd_5213932 : Nat := 2677253215858199700771569

theorem tailTrace_5213932 : CollatzResearch.WordTrace tailWord_5213932 prefixEnd_5213932 2677253215858199700771569 := by
  unfold tailWord_5213932
  simp only [CollatzResearch.WordTrace]
  refine ⟨95083861473411153768438025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126778481964548205024584033 95083861473411153768438025)
  ·
    refine ⟨71312896105058365326328519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95083861473411153768438025 71312896105058365326328519)
    ·
      refine ⟨106969344157587547989492779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71312896105058365326328519 106969344157587547989492779)
      ·
        refine ⟨160454016236381321984239169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106969344157587547989492779 160454016236381321984239169)
        ·
          refine ⟨120340512177285991488179377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160454016236381321984239169 120340512177285991488179377)
          ·
            refine ⟨90255384132964493616134533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120340512177285991488179377 90255384132964493616134533)
            ·
              refine ⟨16922884524930842553025225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90255384132964493616134533 16922884524930842553025225)
              ·
                refine ⟨12692163393698131914768919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16922884524930842553025225 12692163393698131914768919)
                ·
                  refine ⟨19038245090547197872153379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12692163393698131914768919 19038245090547197872153379)
                  ·
                    refine ⟨28557367635820796808230069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19038245090547197872153379 28557367635820796808230069)
                    ·
                      refine ⟨2677253215858199700771569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28557367635820796808230069 2677253215858199700771569)
                      ·
                        rfl

theorem cell23_5213932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_5213932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213932 prefixEnd_5213932 := by exact prefixLift 5213932
  have htrace : WordTrace (prefixWord ++ tailWord_5213932) baseStart_5213932 baseEnd_5213932 := by
    simpa [prefixWord, tailWord_5213932, baseEnd_5213932] using wordTrace_append hprefix tailTrace_5213932
  have hstable : (prefixWord ++ tailWord_5213932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213932).length < 2 ^ (prefixWord ++ tailWord_5213932).sum := by decide
  have hdescent : baseEnd_5213932 < baseStart_5213932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213949 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_5213949 : Nat := 118140960795 + 5213949 * 2 ^ 59
def prefixEnd_5213949 : Nat := 4983230072969 + 3 ^ 40 * 5213949 * 2
def baseEnd_5213949 : Nat := 2677261945029326134258991

theorem tailTrace_5213949 : CollatzResearch.WordTrace tailWord_5213949 prefixEnd_5213949 2677261945029326134258991 := by
  unfold tailWord_5213949
  simp only [CollatzResearch.WordTrace]
  refine ⟨190168342987760719440244901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126778895325173812960163267 190168342987760719440244901)
  ·
    refine ⟨35656564310205134895045919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190168342987760719440244901 35656564310205134895045919)
    ·
      refine ⟨53484846465307702342568879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35656564310205134895045919 53484846465307702342568879)
      ·
        refine ⟨80227269697961553513853319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53484846465307702342568879 80227269697961553513853319)
        ·
          refine ⟨120340904546942330270779979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80227269697961553513853319 120340904546942330270779979)
          ·
            refine ⟨180511356820413495406169969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120340904546942330270779979 180511356820413495406169969)
            ·
              refine ⟨135383517615310121554627477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180511356820413495406169969 135383517615310121554627477)
              ·
                refine ⟨6346102388217661947873163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135383517615310121554627477 6346102388217661947873163)
                ·
                  refine ⟨9519153582326492921809745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6346102388217661947873163 9519153582326492921809745)
                  ·
                    refine ⟨7139365186744869691357309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9519153582326492921809745 7139365186744869691357309)
                    ·
                      refine ⟨2677261945029326134258991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7139365186744869691357309 2677261945029326134258991)
                      ·
                        rfl

theorem cell23_5213949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_5213949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213949 prefixEnd_5213949 := by exact prefixLift 5213949
  have htrace : WordTrace (prefixWord ++ tailWord_5213949) baseStart_5213949 baseEnd_5213949 := by
    simpa [prefixWord, tailWord_5213949, baseEnd_5213949] using wordTrace_append hprefix tailTrace_5213949
  have hstable : (prefixWord ++ tailWord_5213949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213949).length < 2 ^ (prefixWord ++ tailWord_5213949).sum := by decide
  have hdescent : baseEnd_5213949 < baseStart_5213949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213996 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_5213996 : Nat := 118140960795 + 5213996 * 2 ^ 59
def prefixEnd_5213996 : Nat := 4983230072969 + 3 ^ 40 * 5213996 * 2
def baseEnd_5213996 : Nat := 2677286078620087450371275

theorem tailTrace_5213996 : CollatzResearch.WordTrace tailWord_5213996 prefixEnd_5213996 2677286078620087450371275 := by
  unfold tailWord_5213996
  simp only [CollatzResearch.WordTrace]
  refine ⟨95085028609295223233602921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126780038145726964311470561 95085028609295223233602921)
  ·
    refine ⟨71313771456971417425202191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95085028609295223233602921 71313771456971417425202191)
    ·
      refine ⟨106970657185457126137803287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71313771456971417425202191 106970657185457126137803287)
      ·
        refine ⟨160455985778185689206704931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106970657185457126137803287 160455985778185689206704931)
        ·
          refine ⟨240683978667278533810057397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160455985778185689206704931 240683978667278533810057397)
          ·
            refine ⟨22564123000057362544692881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 240683978667278533810057397 22564123000057362544692881)
            ·
              refine ⟨16923092250043021908519661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22564123000057362544692881 16923092250043021908519661)
              ·
                refine ⟨6346159593766133215694873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16923092250043021908519661 6346159593766133215694873)
                ·
                  refine ⟨4759619695324599911771155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6346159593766133215694873 4759619695324599911771155)
                  ·
                    refine ⟨7139429542986899867656733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759619695324599911771155 7139429542986899867656733)
                    ·
                      refine ⟨2677286078620087450371275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7139429542986899867656733 2677286078620087450371275)
                      ·
                        rfl

theorem cell23_5213996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_5213996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213996 prefixEnd_5213996 := by exact prefixLift 5213996
  have htrace : WordTrace (prefixWord ++ tailWord_5213996) baseStart_5213996 baseEnd_5213996 := by
    simpa [prefixWord, tailWord_5213996, baseEnd_5213996] using wordTrace_append hprefix tailTrace_5213996
  have hstable : (prefixWord ++ tailWord_5213996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213996).length < 2 ^ (prefixWord ++ tailWord_5213996).sum := by decide
  have hdescent : baseEnd_5213996 < baseStart_5213996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214023 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_5214023 : Nat := 118140960795 + 5214023 * 2 ^ 59
def prefixEnd_5214023 : Nat := 4983230072969 + 3 ^ 40 * 5214023 * 2
def baseEnd_5214023 : Nat := 2677299942597758844733651

theorem tailTrace_5214023 : CollatzResearch.WordTrace tailWord_5214023 prefixEnd_5214023 2677299942597758844733651 := by
  unfold tailWord_5214023
  simp only [CollatzResearch.WordTrace]
  refine ⟨190171041989492630078438723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126780694659661753385625815 190171041989492630078438723)
  ·
    refine ⟨285256562984238945117658085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190171041989492630078438723 285256562984238945117658085)
    ·
      refine ⟨53485605559544802209560891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285256562984238945117658085 53485605559544802209560891)
      ·
        refine ⟨80228408339317203314341337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53485605559544802209560891 80228408339317203314341337)
        ·
          refine ⟨60171306254487902485756003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80228408339317203314341337 60171306254487902485756003)
          ·
            refine ⟨90256959381731853728634005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60171306254487902485756003 90256959381731853728634005)
            ·
              refine ⟨4230794971018680643529719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90256959381731853728634005 4230794971018680643529719)
              ·
                refine ⟨6346192456528020965294579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230794971018680643529719 6346192456528020965294579)
                ·
                  refine ⟨9519288684792031447941869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6346192456528020965294579 9519288684792031447941869)
                  ·
                    refine ⟨3569733256797011792978201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9519288684792031447941869 3569733256797011792978201)
                    ·
                      refine ⟨2677299942597758844733651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3569733256797011792978201 2677299942597758844733651)
                      ·
                        rfl

theorem cell23_5214023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_5214023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214023 prefixEnd_5214023 := by exact prefixLift 5214023
  have htrace : WordTrace (prefixWord ++ tailWord_5214023) baseStart_5214023 baseEnd_5214023 := by
    simpa [prefixWord, tailWord_5214023, baseEnd_5214023] using wordTrace_append hprefix tailTrace_5214023
  have hstable : (prefixWord ++ tailWord_5214023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214023).length < 2 ^ (prefixWord ++ tailWord_5214023).sum := by decide
  have hdescent : baseEnd_5214023 < baseStart_5214023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214079 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 7, 2]
def baseStart_5214079 : Nat := 118140960795 + 5214079 * 2 ^ 59
def prefixEnd_5214079 : Nat := 4983230072969 + 3 ^ 40 * 5214079 * 2
def baseEnd_5214079 : Nat := 2677328697514410625633393

theorem tailTrace_5214079 : CollatzResearch.WordTrace tailWord_5214079 prefixEnd_5214079 2677328697514410625633393 := by
  unfold tailWord_5214079
  simp only [CollatzResearch.WordTrace]
  refine ⟨190173084477289751642477291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126782056318193167761651527 190173084477289751642477291)
  ·
    refine ⟨285259626715934627463715937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190173084477289751642477291 285259626715934627463715937)
    ·
      refine ⟨213944720036950970597786953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285259626715934627463715937 213944720036950970597786953)
      ·
        refine ⟨160458540027713227948340215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213944720036950970597786953 160458540027713227948340215)
        ·
          refine ⟨240687810041569841922510323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160458540027713227948340215 240687810041569841922510323)
          ·
            refine ⟨361031715062354762883765485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240687810041569841922510323 361031715062354762883765485)
            ·
              refine ⟨135386893148383036081412057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361031715062354762883765485 135386893148383036081412057)
              ·
                refine ⟨101540169861287277061059043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135386893148383036081412057 101540169861287277061059043)
                ·
                  refine ⟨152310254791930915591588565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101540169861287277061059043 152310254791930915591588565)
                  ·
                    refine ⟨3569771596685880834177857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 152310254791930915591588565 3569771596685880834177857)
                    ·
                      refine ⟨2677328697514410625633393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3569771596685880834177857 2677328697514410625633393)
                      ·
                        rfl

theorem cell23_5214079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_5214079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214079 prefixEnd_5214079 := by exact prefixLift 5214079
  have htrace : WordTrace (prefixWord ++ tailWord_5214079) baseStart_5214079 baseEnd_5214079 := by
    simpa [prefixWord, tailWord_5214079, baseEnd_5214079] using wordTrace_append hprefix tailTrace_5214079
  have hstable : (prefixWord ++ tailWord_5214079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214079).length < 2 ^ (prefixWord ++ tailWord_5214079).sum := by decide
  have hdescent : baseEnd_5214079 < baseStart_5214079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214089 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 2, 5]
def baseStart_5214089 : Nat := 118140960795 + 5214089 * 2 ^ 59
def prefixEnd_5214089 : Nat := 4983230072969 + 3 ^ 40 * 5214089 * 2
def baseEnd_5214089 : Nat := 892444610773651862169449

theorem tailTrace_5214089 : CollatzResearch.WordTrace tailWord_5214089 prefixEnd_5214089 892444610773651862169449 := by
  unfold tailWord_5214089
  simp only [CollatzResearch.WordTrace]
  refine ⟨190173449207253523350341321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126782299471502348900227547 190173449207253523350341321)
  ·
    refine ⟨142630086905440142512755991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190173449207253523350341321 142630086905440142512755991)
    ·
      refine ⟨213945130358160213769133987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142630086905440142512755991 213945130358160213769133987)
      ·
        refine ⟨320917695537240320653700981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213945130358160213769133987 320917695537240320653700981)
        ·
          refine ⟨30086033956616280061284467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 320917695537240320653700981 30086033956616280061284467)
          ·
            refine ⟨45129050934924420091926701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30086033956616280061284467 45129050934924420091926701)
            ·
              refine ⟨16923394100596657534472513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45129050934924420091926701 16923394100596657534472513)
              ·
                refine ⟨12692545575447493150854385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16923394100596657534472513 12692545575447493150854385)
                ·
                  refine ⟨9519409181585619863140789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12692545575447493150854385 9519409181585619863140789)
                  ·
                    refine ⟨892444610773651862169449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9519409181585619863140789 892444610773651862169449)
                    ·
                      rfl

theorem cell23_5214089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_5214089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214089 prefixEnd_5214089 := by exact prefixLift 5214089
  have htrace : WordTrace (prefixWord ++ tailWord_5214089) baseStart_5214089 baseEnd_5214089 := by
    simpa [prefixWord, tailWord_5214089, baseEnd_5214089] using wordTrace_append hprefix tailTrace_5214089
  have hstable : (prefixWord ++ tailWord_5214089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214089).length < 2 ^ (prefixWord ++ tailWord_5214089).sum := by decide
  have hdescent : baseEnd_5214089 < baseStart_5214089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214104 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5214104 : Nat := 118140960795 + 5214104 * 2 ^ 59
def prefixEnd_5214104 : Nat := 4983230072969 + 3 ^ 40 * 5214104 * 2
def baseEnd_5214104 : Nat := 2677341534530773027820779

theorem tailTrace_5214104 : CollatzResearch.WordTrace tailWord_5214104 prefixEnd_5214104 2677341534530773027820779 := by
  unfold tailWord_5214104
  simp only [CollatzResearch.WordTrace]
  refine ⟨95086998151099590456068683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126782664201466120608091577 95086998151099590456068683)
  ·
    refine ⟨142630497226649385684103025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95086998151099590456068683 142630497226649385684103025)
    ·
      refine ⟨106972872919987039263077269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142630497226649385684103025 106972872919987039263077269)
      ·
        refine ⟨5014353418124392465456747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106972872919987039263077269 5014353418124392465456747)
        ·
          refine ⟨7521530127186588698185121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014353418124392465456747 7521530127186588698185121)
          ·
            refine ⟨5641147595389941523638841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7521530127186588698185121 5641147595389941523638841)
            ·
              refine ⟨4230860696542456142729131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5641147595389941523638841 4230860696542456142729131)
              ·
                refine ⟨6346291044813684214093697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230860696542456142729131 6346291044813684214093697)
                ·
                  refine ⟨4759718283610263160570273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6346291044813684214093697 4759718283610263160570273)
                  ·
                    refine ⟨3569788712707697370427705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4759718283610263160570273 3569788712707697370427705)
                    ·
                      refine ⟨2677341534530773027820779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3569788712707697370427705 2677341534530773027820779)
                      ·
                        rfl

theorem cell23_5214104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5214104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214104 prefixEnd_5214104 := by exact prefixLift 5214104
  have htrace : WordTrace (prefixWord ++ tailWord_5214104) baseStart_5214104 baseEnd_5214104 := by
    simpa [prefixWord, tailWord_5214104, baseEnd_5214104] using wordTrace_append hprefix tailTrace_5214104
  have hstable : (prefixWord ++ tailWord_5214104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214104).length < 2 ^ (prefixWord ++ tailWord_5214104).sum := by decide
  have hdescent : baseEnd_5214104 < baseStart_5214104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214239 : List Nat := [1, 1, 2, 4, 1, 2, 3, 9]
def baseStart_5214239 : Nat := 118140960795 + 5214239 * 2 ^ 59
def prefixEnd_5214239 : Nat := 4983230072969 + 3 ^ 40 * 5214239 * 2
def baseEnd_5214239 : Nat := 99163364978486296282691

theorem tailTrace_5214239 : CollatzResearch.WordTrace tailWord_5214239 prefixEnd_5214239 99163364978486296282691 := by
  unfold tailWord_5214239
  simp only [CollatzResearch.WordTrace]
  refine ⟨190178920156710098968301771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126785946771140065978867847 190178920156710098968301771)
  ·
    refine ⟨285268380235065148452452657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190178920156710098968301771 285268380235065148452452657)
    ·
      refine ⟨213951285176298861339339493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285268380235065148452452657 213951285176298861339339493)
      ·
        refine ⟨40115865970556036501126155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213951285176298861339339493 40115865970556036501126155)
        ·
          refine ⟨60173798955834054751689233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40115865970556036501126155 60173798955834054751689233)
          ·
            refine ⟨45130349216875541063766925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60173798955834054751689233 45130349216875541063766925)
            ·
              refine ⟨16923880956328327898912597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45130349216875541063766925 16923880956328327898912597)
              ·
                refine ⟨99163364978486296282691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16923880956328327898912597 99163364978486296282691)
                ·
                  rfl

theorem cell23_5214239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 9].length) (baseStart_5214239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214239 prefixEnd_5214239 := by exact prefixLift 5214239
  have htrace : WordTrace (prefixWord ++ tailWord_5214239) baseStart_5214239 baseEnd_5214239 := by
    simpa [prefixWord, tailWord_5214239, baseEnd_5214239] using wordTrace_append hprefix tailTrace_5214239
  have hstable : (prefixWord ++ tailWord_5214239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214239).length < 2 ^ (prefixWord ++ tailWord_5214239).sum := by decide
  have hdescent : baseEnd_5214239 < baseStart_5214239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214244 : List Nat := [2, 3, 1, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5214244 : Nat := 118140960795 + 5214244 * 2 ^ 59
def prefixEnd_5214244 : Nat := 4983230072969 + 3 ^ 40 * 5214244 * 2
def baseEnd_5214244 : Nat := 2677413421822402480070135

theorem tailTrace_5214244 : CollatzResearch.WordTrace tailWord_5214244 prefixEnd_5214244 2677413421822402480070135 := by
  unfold tailWord_5214244
  simp only [CollatzResearch.WordTrace]
  refine ⟨95089551260845992411116893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126786068347794656548155857 95089551260845992411116893)
  ·
    refine ⟨35658581722817247154168835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95089551260845992411116893 35658581722817247154168835)
    ·
      refine ⟨53487872584225870731253253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35658581722817247154168835 53487872584225870731253253)
      ·
        refine ⟨10028976109542350762109985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53487872584225870731253253 10028976109542350762109985)
        ·
          refine ⟨7521732082156763071582489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10028976109542350762109985 7521732082156763071582489)
          ·
            refine ⟨5641299061617572303686867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7521732082156763071582489 5641299061617572303686867)
            ·
              refine ⟨8461948592426358455530301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641299061617572303686867 8461948592426358455530301)
              ·
                refine ⟨3173230722159884420823863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8461948592426358455530301 3173230722159884420823863)
                ·
                  refine ⟨4759846083239826631235795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173230722159884420823863 4759846083239826631235795)
                  ·
                    refine ⟨7139769124859739946853693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759846083239826631235795 7139769124859739946853693)
                    ·
                      refine ⟨2677413421822402480070135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7139769124859739946853693 2677413421822402480070135)
                      ·
                        rfl

theorem cell23_5214244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5214244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214244 prefixEnd_5214244 := by exact prefixLift 5214244
  have htrace : WordTrace (prefixWord ++ tailWord_5214244) baseStart_5214244 baseEnd_5214244 := by
    simpa [prefixWord, tailWord_5214244, baseEnd_5214244] using wordTrace_append hprefix tailTrace_5214244
  have hstable : (prefixWord ++ tailWord_5214244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214244).length < 2 ^ (prefixWord ++ tailWord_5214244).sum := by decide
  have hdescent : baseEnd_5214244 < baseStart_5214244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214283 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 3]
def baseStart_5214283 : Nat := 118140960795 + 5214283 * 2 ^ 59
def prefixEnd_5214283 : Nat := 4983230072969 + 3 ^ 40 * 5214283 * 2
def baseEnd_5214283 : Nat := 2677433447567927827482455

theorem tailTrace_5214283 : CollatzResearch.WordTrace tailWord_5214283 prefixEnd_5214283 2677433447567927827482455 := by
  unfold tailWord_5214283
  simp only [CollatzResearch.WordTrace]
  refine ⟨190180524968550694482903503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126787016645700462988602335 190180524968550694482903503)
  ·
    refine ⟨285270787452826041724355255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190180524968550694482903503 285270787452826041724355255)
    ·
      refine ⟨427906181179239062586532883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285270787452826041724355255 427906181179239062586532883)
      ·
        refine ⟨641859271768858593879799325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427906181179239062586532883 641859271768858593879799325)
        ·
          refine ⟨240697226913321972704924747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 641859271768858593879799325 240697226913321972704924747)
          ·
            refine ⟨361045840369982959057387121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240697226913321972704924747 361045840369982959057387121)
            ·
              refine ⟨270784380277487219293040341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361045840369982959057387121 270784380277487219293040341)
              ·
                refine ⟨6346508912753606702180633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 270784380277487219293040341 6346508912753606702180633)
                ·
                  refine ⟨4759881684565205026635475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6346508912753606702180633 4759881684565205026635475)
                  ·
                    refine ⟨7139822526847807539953213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759881684565205026635475 7139822526847807539953213)
                    ·
                      refine ⟨2677433447567927827482455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7139822526847807539953213 2677433447567927827482455)
                      ·
                        rfl

theorem cell23_5214283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 3].length) (baseStart_5214283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214283 prefixEnd_5214283 := by exact prefixLift 5214283
  have htrace : WordTrace (prefixWord ++ tailWord_5214283) baseStart_5214283 baseEnd_5214283 := by
    simpa [prefixWord, tailWord_5214283, baseEnd_5214283] using wordTrace_append hprefix tailTrace_5214283
  have hstable : (prefixWord ++ tailWord_5214283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214283).length < 2 ^ (prefixWord ++ tailWord_5214283).sum := by decide
  have hdescent : baseEnd_5214283 < baseStart_5214283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214289 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_5214289 : Nat := 118140960795 + 5214289 * 2 ^ 59
def prefixEnd_5214289 : Nat := 4983230072969 + 3 ^ 40 * 5214289 * 2
def baseEnd_5214289 : Nat := 2677436528451854804007427

theorem tailTrace_5214289 : CollatzResearch.WordTrace tailWord_5214289 prefixEnd_5214289 2677436528451854804007427 := by
  unfold tailWord_5214289
  simp only [CollatzResearch.WordTrace]
  refine ⟨190180743806528957507621921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126787162537685971671747947 190180743806528957507621921)
  ·
    refine ⟨142635557854896718130716441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190180743806528957507621921 142635557854896718130716441)
    ·
      refine ⟨106976668391172538598037331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142635557854896718130716441 106976668391172538598037331)
      ·
        refine ⟨160465002586758807897055997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106976668391172538598037331 160465002586758807897055997)
        ·
          refine ⟨60174375970034552961395999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160465002586758807897055997 60174375970034552961395999)
          ·
            refine ⟨90261563955051829442093999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60174375970034552961395999 90261563955051829442093999)
            ·
              refine ⟨135392345932577744163140999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90261563955051829442093999 135392345932577744163140999)
              ·
                refine ⟨203088518898866616244711499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135392345932577744163140999 203088518898866616244711499)
                ·
                  refine ⟨304632778348299924367067249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203088518898866616244711499 304632778348299924367067249)
                  ·
                    refine ⟨228474583761224943275300437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 304632778348299924367067249 228474583761224943275300437)
                    ·
                      refine ⟨2677436528451854804007427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 228474583761224943275300437 2677436528451854804007427)
                      ·
                        rfl

theorem cell23_5214289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_5214289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214289 prefixEnd_5214289 := by exact prefixLift 5214289
  have htrace : WordTrace (prefixWord ++ tailWord_5214289) baseStart_5214289 baseEnd_5214289 := by
    simpa [prefixWord, tailWord_5214289, baseEnd_5214289] using wordTrace_append hprefix tailTrace_5214289
  have hstable : (prefixWord ++ tailWord_5214289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214289).length < 2 ^ (prefixWord ++ tailWord_5214289).sum := by decide
  have hdescent : baseEnd_5214289 < baseStart_5214289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214340 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_5214340 : Nat := 118140960795 + 5214340 * 2 ^ 59
def prefixEnd_5214340 : Nat := 4983230072969 + 3 ^ 40 * 5214340 * 2
def baseEnd_5214340 : Nat := 2677462715965234104469693

theorem tailTrace_5214340 : CollatzResearch.WordTrace tailWord_5214340 prefixEnd_5214340 2677462715965234104469693 := by
  unfold tailWord_5214340
  simp only [CollatzResearch.WordTrace]
  refine ⟨95091301964672096608864237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126788402619562795478485649 95091301964672096608864237)
  ·
    refine ⟨35659238236752036228324089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95091301964672096608864237 35659238236752036228324089)
    ·
      refine ⟨26744428677564027171243067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35659238236752036228324089 26744428677564027171243067)
      ·
        refine ⟨40116643016346040756864601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26744428677564027171243067 40116643016346040756864601)
        ·
          refine ⟨30087482262259530567648451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40116643016346040756864601 30087482262259530567648451)
          ·
            refine ⟨45131223393389295851472677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30087482262259530567648451 45131223393389295851472677)
            ·
              refine ⟨8462104386260492972151127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45131223393389295851472677 8462104386260492972151127)
              ·
                refine ⟨12693156579390739458226691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462104386260492972151127 12693156579390739458226691)
                ·
                  refine ⟨19039734869086109187340037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12693156579390739458226691 19039734869086109187340037)
                  ·
                    refine ⟨3569950287953645472626257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19039734869086109187340037 3569950287953645472626257)
                    ·
                      refine ⟨2677462715965234104469693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3569950287953645472626257 2677462715965234104469693)
                      ·
                        rfl

theorem cell23_5214340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_5214340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214340 prefixEnd_5214340 := by exact prefixLift 5214340
  have htrace : WordTrace (prefixWord ++ tailWord_5214340) baseStart_5214340 baseEnd_5214340 := by
    simpa [prefixWord, tailWord_5214340, baseEnd_5214340] using wordTrace_append hprefix tailTrace_5214340
  have hstable : (prefixWord ++ tailWord_5214340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214340).length < 2 ^ (prefixWord ++ tailWord_5214340).sum := by decide
  have hdescent : baseEnd_5214340 < baseStart_5214340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214346 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 9]
def baseStart_5214346 : Nat := 118140960795 + 5214346 * 2 ^ 59
def prefixEnd_5214346 : Nat := 4983230072969 + 3 ^ 40 * 5214346 * 2
def baseEnd_5214346 : Nat := 297496199649906786777185

theorem tailTrace_5214346 : CollatzResearch.WordTrace tailWord_5214346 prefixEnd_5214346 297496199649906786777185 := by
  unfold tailWord_5214346
  simp only [CollatzResearch.WordTrace]
  refine ⟨47545705691830614060611723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126788548511548304161631261 47545705691830614060611723)
  ·
    refine ⟨71318558537745921090917585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47545705691830614060611723 71318558537745921090917585)
    ·
      refine ⟨53488918903309440818188189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71318558537745921090917585 53488918903309440818188189)
      ·
        refine ⟨20058344588741040306820571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53488918903309440818188189 20058344588741040306820571)
        ·
          refine ⟨30087516883111560460230857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20058344588741040306820571 30087516883111560460230857)
          ·
            refine ⟨22565637662333670345173143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30087516883111560460230857 22565637662333670345173143)
            ·
              refine ⟨33848456493500505517759715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22565637662333670345173143 33848456493500505517759715)
              ·
                refine ⟨50772684740250758276639573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33848456493500505517759715 50772684740250758276639573)
                ·
                  refine ⟨297496199649906786777185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50772684740250758276639573 297496199649906786777185)
                  ·
                    rfl

theorem cell23_5214346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_5214346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214346 prefixEnd_5214346 := by exact prefixLift 5214346
  have htrace : WordTrace (prefixWord ++ tailWord_5214346) baseStart_5214346 baseEnd_5214346 := by
    simpa [prefixWord, tailWord_5214346, baseEnd_5214346] using wordTrace_append hprefix tailTrace_5214346
  have hstable : (prefixWord ++ tailWord_5214346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214346).length < 2 ^ (prefixWord ++ tailWord_5214346).sum := by decide
  have hdescent : baseEnd_5214346 < baseStart_5214346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214386 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_5214386 : Nat := 118140960795 + 5214386 * 2 ^ 59
def prefixEnd_5214386 : Nat := 4983230072969 + 3 ^ 40 * 5214386 * 2
def baseEnd_5214386 : Nat := 2677486336075340924494481

theorem tailTrace_5214386 : CollatzResearch.WordTrace tailWord_5214386 prefixEnd_5214386 2677486336075340924494481 := by
  unfold tailWord_5214386
  simp only [CollatzResearch.WordTrace]
  refine ⟨47546070421794385768475753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126789521124785028715935341 47546070421794385768475753)
  ·
    refine ⟨35659552816345789326356815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47546070421794385768475753 35659552816345789326356815)
    ·
      refine ⟨53489329224518683989535223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35659552816345789326356815 53489329224518683989535223)
      ·
        refine ⟨80233993836778025984302835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53489329224518683989535223 80233993836778025984302835)
        ·
          refine ⟨120350990755167038976454253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80233993836778025984302835 120350990755167038976454253)
          ·
            refine ⟨45131621533187639616170345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120350990755167038976454253 45131621533187639616170345)
            ·
              refine ⟨33848716149890729712127759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45131621533187639616170345 33848716149890729712127759)
              ·
                refine ⟨50773074224836094568191639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33848716149890729712127759 50773074224836094568191639)
                ·
                  refine ⟨76159611337254141852287459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50773074224836094568191639 76159611337254141852287459)
                  ·
                    refine ⟨114239417005881212778431189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76159611337254141852287459 114239417005881212778431189)
                    ·
                      refine ⟨2677486336075340924494481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114239417005881212778431189 2677486336075340924494481)
                      ·
                        rfl

theorem cell23_5214386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_5214386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214386 prefixEnd_5214386 := by exact prefixLift 5214386
  have htrace : WordTrace (prefixWord ++ tailWord_5214386) baseStart_5214386 baseEnd_5214386 := by
    simpa [prefixWord, tailWord_5214386, baseEnd_5214386] using wordTrace_append hprefix tailTrace_5214386
  have hstable : (prefixWord ++ tailWord_5214386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214386).length < 2 ^ (prefixWord ++ tailWord_5214386).sum := by decide
  have hdescent : baseEnd_5214386 < baseStart_5214386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214426 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_5214426 : Nat := 118140960795 + 5214426 * 2 ^ 59
def prefixEnd_5214426 : Nat := 4983230072969 + 3 ^ 40 * 5214426 * 2
def baseEnd_5214426 : Nat := 2677506875301520767994297

theorem tailTrace_5214426 : CollatzResearch.WordTrace tailWord_5214426 prefixEnd_5214426 2677506875301520767994297 := by
  unfold tailWord_5214426
  simp only [CollatzResearch.WordTrace]
  refine ⟨47546435151758157476339783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126790493738021753270239421 47546435151758157476339783)
  ·
    refine ⟨71319652727637236214509675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47546435151758157476339783 71319652727637236214509675)
    ·
      refine ⟨106979479091455854321764513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71319652727637236214509675 106979479091455854321764513)
      ·
        refine ⟨80234609318591890741323385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106979479091455854321764513 80234609318591890741323385)
        ·
          refine ⟨60175956988943918055992539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80234609318591890741323385 60175956988943918055992539)
          ·
            refine ⟨90263935483415877083988809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60175956988943918055992539 90263935483415877083988809)
            ·
              refine ⟨67697951612561907812991607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90263935483415877083988809 67697951612561907812991607)
              ·
                refine ⟨101546927418842861719487411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67697951612561907812991607 101546927418842861719487411)
                ·
                  refine ⟨152320391128264292579231117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101546927418842861719487411 152320391128264292579231117)
                  ·
                    refine ⟨57120146673099109717211669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152320391128264292579231117 57120146673099109717211669)
                    ·
                      refine ⟨2677506875301520767994297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57120146673099109717211669 2677506875301520767994297)
                      ·
                        rfl

theorem cell23_5214426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_5214426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214426 prefixEnd_5214426 := by exact prefixLift 5214426
  have htrace : WordTrace (prefixWord ++ tailWord_5214426) baseStart_5214426 baseEnd_5214426 := by
    simpa [prefixWord, tailWord_5214426, baseEnd_5214426] using wordTrace_append hprefix tailTrace_5214426
  have hstable : (prefixWord ++ tailWord_5214426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214426).length < 2 ^ (prefixWord ++ tailWord_5214426).sum := by decide
  have hdescent : baseEnd_5214426 < baseStart_5214426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214440 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 3, 4]
def baseStart_5214440 : Nat := 118140960795 + 5214440 * 2 ^ 59
def prefixEnd_5214440 : Nat := 4983230072969 + 3 ^ 40 * 5214440 * 2
def baseEnd_5214440 : Nat := 892504688010227904406411

theorem tailTrace_5214440 : CollatzResearch.WordTrace tailWord_5214440 prefixEnd_5214440 892504688010227904406411 := by
  unfold tailWord_5214440
  simp only [CollatzResearch.WordTrace]
  refine ⟨95093125614490955148184387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126790834152654606864245849 95093125614490955148184387)
  ·
    refine ⟨142639688421736432722276581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95093125614490955148184387 142639688421736432722276581)
    ·
      refine ⟨26744941579075581135426859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142639688421736432722276581 26744941579075581135426859)
      ·
        refine ⟨40117412368613371703140289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26744941579075581135426859 40117412368613371703140289)
        ·
          refine ⟨30088059276460028777355217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40117412368613371703140289 30088059276460028777355217)
          ·
            refine ⟨22566044457345021583016413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30088059276460028777355217 22566044457345021583016413)
            ·
              refine ⟨8462266671504383093631155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22566044457345021583016413 8462266671504383093631155)
              ·
                refine ⟨12693400007256574640446733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462266671504383093631155 12693400007256574640446733)
                ·
                  refine ⟨4760025002721215490167525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12693400007256574640446733 4760025002721215490167525)
                  ·
                    refine ⟨892504688010227904406411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4760025002721215490167525 892504688010227904406411)
                    ·
                      rfl

theorem cell23_5214440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_5214440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214440 prefixEnd_5214440 := by exact prefixLift 5214440
  have htrace : WordTrace (prefixWord ++ tailWord_5214440) baseStart_5214440 baseEnd_5214440 := by
    simpa [prefixWord, tailWord_5214440, baseEnd_5214440] using wordTrace_append hprefix tailTrace_5214440
  have hstable : (prefixWord ++ tailWord_5214440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214440).length < 2 ^ (prefixWord ++ tailWord_5214440).sum := by decide
  have hdescent : baseEnd_5214440 < baseStart_5214440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214456 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_5214456 : Nat := 118140960795 + 5214456 * 2 ^ 59
def prefixEnd_5214456 : Nat := 4983230072969 + 3 ^ 40 * 5214456 * 2
def baseEnd_5214456 : Nat := 2677522279721155650619159

theorem tailTrace_5214456 : CollatzResearch.WordTrace tailWord_5214456 prefixEnd_5214456 2677522279721155650619159 := by
  unfold tailWord_5214456
  simp only [CollatzResearch.WordTrace]
  refine ⟨95093417398461972514475611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126791223197949296685967481 95093417398461972514475611)
  ·
    refine ⟨142640126097692958771713417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95093417398461972514475611 142640126097692958771713417)
    ·
      refine ⟨106980094573269719078785063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142640126097692958771713417 106980094573269719078785063)
      ·
        refine ⟨160470141859904578618177595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106980094573269719078785063 160470141859904578618177595)
        ·
          refine ⟨240705212789856867927266393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160470141859904578618177595 240705212789856867927266393)
          ·
            refine ⟨180528909592392650945449795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240705212789856867927266393 180528909592392650945449795)
            ·
              refine ⟨270793364388588976418174693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180528909592392650945449795 270793364388588976418174693)
              ·
                refine ⟨50773755822860433078407755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270793364388588976418174693 50773755822860433078407755)
                ·
                  refine ⟨76160633734290649617611633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50773755822860433078407755 76160633734290649617611633)
                  ·
                    refine ⟨57120475300717987213208725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76160633734290649617611633 57120475300717987213208725)
                    ·
                      refine ⟨2677522279721155650619159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57120475300717987213208725 2677522279721155650619159)
                      ·
                        rfl

theorem cell23_5214456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_5214456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214456 prefixEnd_5214456 := by exact prefixLift 5214456
  have htrace : WordTrace (prefixWord ++ tailWord_5214456) baseStart_5214456 baseEnd_5214456 := by
    simpa [prefixWord, tailWord_5214456, baseEnd_5214456] using wordTrace_append hprefix tailTrace_5214456
  have hstable : (prefixWord ++ tailWord_5214456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214456).length < 2 ^ (prefixWord ++ tailWord_5214456).sum := by decide
  have hdescent : baseEnd_5214456 < baseStart_5214456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214483 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 1, 5]
def baseStart_5214483 : Nat := 118140960795 + 5214483 * 2 ^ 59
def prefixEnd_5214483 : Nat := 4983230072969 + 3 ^ 40 * 5214483 * 2
def baseEnd_5214483 : Nat := 892512047899609014993845

theorem tailTrace_5214483 : CollatzResearch.WordTrace tailWord_5214483 prefixEnd_5214483 892512047899609014993845 := by
  unfold tailWord_5214483
  simp only [CollatzResearch.WordTrace]
  refine ⟨190187819567826128640184103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126791879711884085760122735 190187819567826128640184103)
  ·
    refine ⟨285281729351739192960276155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190187819567826128640184103 285281729351739192960276155)
    ·
      refine ⟨427922594027608789440414233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285281729351739192960276155 427922594027608789440414233)
      ·
        refine ⟨320941945520706592080310675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427922594027608789440414233 320941945520706592080310675)
        ·
          refine ⟨481412918281059888120466013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320941945520706592080310675 481412918281059888120466013)
          ·
            refine ⟨180529844355397458045174755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 481412918281059888120466013 180529844355397458045174755)
            ·
              refine ⟨270794766533096187067762133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180529844355397458045174755 270794766533096187067762133)
              ·
                refine ⟨6346752340619441884400675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 270794766533096187067762133 6346752340619441884400675)
                ·
                  refine ⟨9520128510929162826601013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6346752340619441884400675 9520128510929162826601013)
                  ·
                    refine ⟨892512047899609014993845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9520128510929162826601013 892512047899609014993845)
                    ·
                      rfl

theorem cell23_5214483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 5].length) (baseStart_5214483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214483 prefixEnd_5214483 := by exact prefixLift 5214483
  have htrace : WordTrace (prefixWord ++ tailWord_5214483) baseStart_5214483 baseEnd_5214483 := by
    simpa [prefixWord, tailWord_5214483, baseEnd_5214483] using wordTrace_append hprefix tailTrace_5214483
  have hstable : (prefixWord ++ tailWord_5214483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214483).length < 2 ^ (prefixWord ++ tailWord_5214483).sum := by decide
  have hdescent : baseEnd_5214483 < baseStart_5214483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214567 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_5214567 : Nat := 118140960795 + 5214567 * 2 ^ 59
def prefixEnd_5214567 : Nat := 4983230072969 + 3 ^ 40 * 5214567 * 2
def baseEnd_5214567 : Nat := 2677579276073804716331149

theorem tailTrace_5214567 : CollatzResearch.WordTrace tailWord_5214567 prefixEnd_5214567 2677579276073804716331149 := by
  unfold tailWord_5214567
  simp only [CollatzResearch.WordTrace]
  refine ⟨190190883299521810986241955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126793922199681207324161303 190190883299521810986241955)
  ·
    refine ⟨285286324949282716479362933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190190883299521810986241955 285286324949282716479362933)
    ·
      refine ⟨26745592963995254669940275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285286324949282716479362933 26745592963995254669940275)
      ·
        refine ⟨40118389445992882004910413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26745592963995254669940275 40118389445992882004910413)
        ·
          refine ⟨15044396042247330751841405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40118389445992882004910413 15044396042247330751841405)
          ·
            refine ⟨5641648515842749031940527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15044396042247330751841405 5641648515842749031940527)
            ·
              refine ⟨8462472773764123547910791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641648515842749031940527 8462472773764123547910791)
              ·
                refine ⟨12693709160646185321866187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462472773764123547910791 12693709160646185321866187)
                ·
                  refine ⟨19040563740969277982799281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12693709160646185321866187 19040563740969277982799281)
                  ·
                    refine ⟨14280422805726958487099461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19040563740969277982799281 14280422805726958487099461)
                    ·
                      refine ⟨2677579276073804716331149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14280422805726958487099461 2677579276073804716331149)
                      ·
                        rfl

theorem cell23_5214567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_5214567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214567 prefixEnd_5214567 := by exact prefixLift 5214567
  have htrace : WordTrace (prefixWord ++ tailWord_5214567) baseStart_5214567 baseEnd_5214567 := by
    simpa [prefixWord, tailWord_5214567, baseEnd_5214567] using wordTrace_append hprefix tailTrace_5214567
  have hstable : (prefixWord ++ tailWord_5214567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214567).length < 2 ^ (prefixWord ++ tailWord_5214567).sum := by decide
  have hdescent : baseEnd_5214567 < baseStart_5214567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214594 : List Nat := [3, 4, 2, 1, 3, 1, 9]
def baseStart_5214594 : Nat := 118140960795 + 5214594 * 2 ^ 59
def prefixEnd_5214594 : Nat := 4983230072969 + 3 ^ 40 * 5214594 * 2
def baseEnd_5214594 : Nat := 33056705432734272971525

theorem tailTrace_5214594 : CollatzResearch.WordTrace tailWord_5214594 prefixEnd_5214594 33056705432734272971525 := by
  unfold tailWord_5214594
  simp only [CollatzResearch.WordTrace]
  refine ⟨47547967017605998649368709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126794578713615996398316557 47547967017605998649368709)
  ·
    refine ⟨8915243815801124746756633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47547967017605998649368709 8915243815801124746756633)
    ·
      refine ⟨6686432861850843560067475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8915243815801124746756633 6686432861850843560067475)
      ·
        refine ⟨10029649292776265340101213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6686432861850843560067475 10029649292776265340101213)
        ·
          refine ⟨3761118484791099502537955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10029649292776265340101213 3761118484791099502537955)
          ·
            refine ⟨5641677727186649253806933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761118484791099502537955 5641677727186649253806933)
            ·
              refine ⟨33056705432734272971525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5641677727186649253806933 33056705432734272971525)
              ·
                rfl

theorem cell23_5214594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 9].length) (baseStart_5214594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214594 prefixEnd_5214594 := by exact prefixLift 5214594
  have htrace : WordTrace (prefixWord ++ tailWord_5214594) baseStart_5214594 baseEnd_5214594 := by
    simpa [prefixWord, tailWord_5214594, baseEnd_5214594] using wordTrace_append hprefix tailTrace_5214594
  have hstable : (prefixWord ++ tailWord_5214594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214594).length < 2 ^ (prefixWord ++ tailWord_5214594).sum := by decide
  have hdescent : baseEnd_5214594 < baseStart_5214594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214613 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_5214613 : Nat := 118140960795 + 5214613 * 2 ^ 59
def prefixEnd_5214613 : Nat := 4983230072969 + 3 ^ 40 * 5214613 * 2
def baseEnd_5214613 : Nat := 2677602896183911536355937

theorem tailTrace_5214613 : CollatzResearch.WordTrace tailWord_5214613 prefixEnd_5214613 2677602896183911536355937 := by
  unfold tailWord_5214613
  simp only [CollatzResearch.WordTrace]
  refine ⟨190192561057355160842416493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126795040704903440561610995 190192561057355160842416493)
  ·
    refine ⟨71322210396508185315906185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190192561057355160842416493 71322210396508185315906185)
    ·
      refine ⟨53491657797381138986929639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71322210396508185315906185 53491657797381138986929639)
      ·
        refine ⟨80237486696071708480394459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53491657797381138986929639 80237486696071708480394459)
        ·
          refine ⟨120356230044107562720591689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80237486696071708480394459 120356230044107562720591689)
          ·
            refine ⟨90267172533080672040443767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120356230044107562720591689 90267172533080672040443767)
            ·
              refine ⟨135400758799621008060665651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90267172533080672040443767 135400758799621008060665651)
              ·
                refine ⟨203101138199431512090998477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135400758799621008060665651 203101138199431512090998477)
                ·
                  refine ⟨76162926824786817034124429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203101138199431512090998477 76162926824786817034124429)
                  ·
                    refine ⟨28561097559295056387796661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76162926824786817034124429 28561097559295056387796661)
                    ·
                      refine ⟨2677602896183911536355937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28561097559295056387796661 2677602896183911536355937)
                      ·
                        rfl

theorem cell23_5214613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_5214613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214613 prefixEnd_5214613 := by exact prefixLift 5214613
  have htrace : WordTrace (prefixWord ++ tailWord_5214613) baseStart_5214613 baseEnd_5214613 := by
    simpa [prefixWord, tailWord_5214613, baseEnd_5214613] using wordTrace_append hprefix tailTrace_5214613
  have hstable : (prefixWord ++ tailWord_5214613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214613).length < 2 ^ (prefixWord ++ tailWord_5214613).sum := by decide
  have hdescent : baseEnd_5214613 < baseStart_5214613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214631 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_5214631 : Nat := 118140960795 + 5214631 * 2 ^ 59
def prefixEnd_5214631 : Nat := 4983230072969 + 3 ^ 40 * 5214631 * 2
def baseEnd_5214631 : Nat := 2677612138835692465930855

theorem tailTrace_5214631 : CollatzResearch.WordTrace tailWord_5214631 prefixEnd_5214631 2677612138835692465930855 := by
  unfold tailWord_5214631
  simp only [CollatzResearch.WordTrace]
  refine ⟨190193217571289949916571747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126795478380859966611047831 190193217571289949916571747)
  ·
    refine ⟨285289826356934924874857621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190193217571289949916571747 285289826356934924874857621)
    ·
      refine ⟨13372960610481324603508951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 285289826356934924874857621 13372960610481324603508951)
      ·
        refine ⟨20059440915721986905263427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13372960610481324603508951 20059440915721986905263427)
        ·
          refine ⟨30089161373582980357895141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20059440915721986905263427 30089161373582980357895141)
          ·
            refine ⟨5641717757546808817105339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30089161373582980357895141 5641717757546808817105339)
            ·
              refine ⟨8462576636320213225658009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641717757546808817105339 8462576636320213225658009)
              ·
                refine ⟨6346932477240159919243507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8462576636320213225658009 6346932477240159919243507)
                ·
                  refine ⟨9520398715860239878865261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6346932477240159919243507 9520398715860239878865261)
                  ·
                    refine ⟨3570149518447589954574473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9520398715860239878865261 3570149518447589954574473)
                    ·
                      refine ⟨2677612138835692465930855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570149518447589954574473 2677612138835692465930855)
                      ·
                        rfl

theorem cell23_5214631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_5214631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214631 prefixEnd_5214631 := by exact prefixLift 5214631
  have htrace : WordTrace (prefixWord ++ tailWord_5214631) baseStart_5214631 baseEnd_5214631 := by
    simpa [prefixWord, tailWord_5214631, baseEnd_5214631] using wordTrace_append hprefix tailTrace_5214631
  have hstable : (prefixWord ++ tailWord_5214631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214631).length < 2 ^ (prefixWord ++ tailWord_5214631).sum := by decide
  have hdescent : baseEnd_5214631 < baseStart_5214631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214633 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 7]
def baseStart_5214633 : Nat := 118140960795 + 5214633 * 2 ^ 59
def prefixEnd_5214633 : Nat := 4983230072969 + 3 ^ 40 * 5214633 * 2
def baseEnd_5214633 : Nat := 297512573977444606456205

theorem tailTrace_5214633 : CollatzResearch.WordTrace tailWord_5214633 prefixEnd_5214633 297512573977444606456205 := by
  unfold tailWord_5214633
  simp only [CollatzResearch.WordTrace]
  refine ⟨190193290517282704258144553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126795527011521802838763035 190193290517282704258144553)
  ·
    refine ⟨142644967887962028193608415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190193290517282704258144553 142644967887962028193608415)
    ·
      refine ⟨213967451831943042290412623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142644967887962028193608415 213967451831943042290412623)
      ·
        refine ⟨320951177747914563435618935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213967451831943042290412623 320951177747914563435618935)
        ·
          refine ⟨481426766621871845153428403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320951177747914563435618935 481426766621871845153428403)
          ·
            refine ⟨722140149932807767730142605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481426766621871845153428403 722140149932807767730142605)
            ·
              refine ⟨270802556224802912898803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722140149932807767730142605 270802556224802912898803477)
              ·
                refine ⟨12693869823037636542131413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270802556224802912898803477 12693869823037636542131413)
                ·
                  refine ⟨297512573977444606456205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12693869823037636542131413 297512573977444606456205)
                  ·
                    rfl

theorem cell23_5214633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_5214633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214633 prefixEnd_5214633 := by exact prefixLift 5214633
  have htrace : WordTrace (prefixWord ++ tailWord_5214633) baseStart_5214633 baseEnd_5214633 := by
    simpa [prefixWord, tailWord_5214633, baseEnd_5214633] using wordTrace_append hprefix tailTrace_5214633
  have hstable : (prefixWord ++ tailWord_5214633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214633).length < 2 ^ (prefixWord ++ tailWord_5214633).sum := by decide
  have hdescent : baseEnd_5214633 < baseStart_5214633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214674 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5214674 : Nat := 118140960795 + 5214674 * 2 ^ 59
def prefixEnd_5214674 : Nat := 4983230072969 + 3 ^ 40 * 5214674 * 2
def baseEnd_5214674 : Nat := 2677634218503835797693157

theorem tailTrace_5214674 : CollatzResearch.WordTrace tailWord_5214674 prefixEnd_5214674 2677634218503835797693157 := by
  unfold tailWord_5214674
  simp only [CollatzResearch.WordTrace]
  refine ⟨47548696477533542065096769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126796523940089445506924717 47548696477533542065096769)
  ·
    refine ⟨35661522358150156548822577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47548696477533542065096769 35661522358150156548822577)
    ·
      refine ⟨26746141768612617411616933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35661522358150156548822577 26746141768612617411616933)
      ·
        refine ⟨5014901581614865764678175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26746141768612617411616933 5014901581614865764678175)
        ·
          refine ⟨7522352372422298647017263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014901581614865764678175 7522352372422298647017263)
          ·
            refine ⟨11283528558633447970525895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522352372422298647017263 11283528558633447970525895)
            ·
              refine ⟨16925292837950171955788843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11283528558633447970525895 16925292837950171955788843)
              ·
                refine ⟨25387939256925257933683265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16925292837950171955788843 25387939256925257933683265)
                ·
                  refine ⟨19040954442693943450262449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25387939256925257933683265 19040954442693943450262449)
                  ·
                    refine ⟨14280715832020457587696837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19040954442693943450262449 14280715832020457587696837)
                    ·
                      refine ⟨2677634218503835797693157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14280715832020457587696837 2677634218503835797693157)
                      ·
                        rfl

theorem cell23_5214674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5214674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214674 prefixEnd_5214674 := by exact prefixLift 5214674
  have htrace : WordTrace (prefixWord ++ tailWord_5214674) baseStart_5214674 baseEnd_5214674 := by
    simpa [prefixWord, tailWord_5214674, baseEnd_5214674] using wordTrace_append hprefix tailTrace_5214674
  have hstable : (prefixWord ++ tailWord_5214674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214674).length < 2 ^ (prefixWord ++ tailWord_5214674).sum := by decide
  have hdescent : baseEnd_5214674 < baseStart_5214674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214677 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5214677 : Nat := 118140960795 + 5214677 * 2 ^ 59
def prefixEnd_5214677 : Nat := 4983230072969 + 3 ^ 40 * 5214677 * 2
def baseEnd_5214677 : Nat := 2677635758945799285955643

theorem tailTrace_5214677 : CollatzResearch.WordTrace tailWord_5214677 prefixEnd_5214677 2677635758945799285955643 := by
  unfold tailWord_5214677
  simp only [CollatzResearch.WordTrace]
  refine ⟨190194895329123299772746285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126796596886082199848497523 190194895329123299772746285)
  ·
    refine ⟨71323085748421237414779857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190194895329123299772746285 71323085748421237414779857)
    ·
      refine ⟨53492314311315928061084893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71323085748421237414779857 53492314311315928061084893)
      ·
        refine ⟨20059617866743473022906835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53492314311315928061084893 20059617866743473022906835)
        ·
          refine ⟨30089426800115209534360253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20059617866743473022906835 30089426800115209534360253)
          ·
            refine ⟨11283535050043203575385095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30089426800115209534360253 11283535050043203575385095)
            ·
              refine ⟨16925302575064805363077643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11283535050043203575385095 16925302575064805363077643)
              ·
                refine ⟨25387953862597208044616465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16925302575064805363077643 25387953862597208044616465)
                ·
                  refine ⟨19040965396947906033462349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25387953862597208044616465 19040965396947906033462349)
                  ·
                    refine ⟨7140362023855464762548381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19040965396947906033462349 7140362023855464762548381)
                    ·
                      refine ⟨2677635758945799285955643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7140362023855464762548381 2677635758945799285955643)
                      ·
                        rfl

theorem cell23_5214677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5214677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214677 prefixEnd_5214677 := by exact prefixLift 5214677
  have htrace : WordTrace (prefixWord ++ tailWord_5214677) baseStart_5214677 baseEnd_5214677 := by
    simpa [prefixWord, tailWord_5214677, baseEnd_5214677] using wordTrace_append hprefix tailTrace_5214677
  have hstable : (prefixWord ++ tailWord_5214677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214677).length < 2 ^ (prefixWord ++ tailWord_5214677).sum := by decide
  have hdescent : baseEnd_5214677 < baseStart_5214677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214700 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_5214700 : Nat := 118140960795 + 5214700 * 2 ^ 59
def prefixEnd_5214700 : Nat := 4983230072969 + 3 ^ 40 * 5214700 * 2
def baseEnd_5214700 : Nat := 2677647569000852695968037

theorem tailTrace_5214700 : CollatzResearch.WordTrace tailWord_5214700 prefixEnd_5214700 2677647569000852695968037 := by
  unfold tailWord_5214700
  simp only [CollatzResearch.WordTrace]
  refine ⟨95097867104019987350416777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126797156138693316467222369 95097867104019987350416777)
  ·
    refine ⟨71323400328014990512812583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95097867104019987350416777 71323400328014990512812583)
    ·
      refine ⟨106985100492022485769218875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71323400328014990512812583 106985100492022485769218875)
      ·
        refine ⟨160477650738033728653828313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106985100492022485769218875 160477650738033728653828313)
        ·
          refine ⟨120358238053525296490371235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160477650738033728653828313 120358238053525296490371235)
          ·
            refine ⟨180537357080287944735556853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120358238053525296490371235 180537357080287944735556853)
            ·
              refine ⟨16925377226276994818958455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180537357080287944735556853 16925377226276994818958455)
              ·
                refine ⟨25388065839415492228437683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16925377226276994818958455 25388065839415492228437683)
                ·
                  refine ⟨38082098759123238342656525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25388065839415492228437683 38082098759123238342656525)
                  ·
                    refine ⟨14280787034671214378496197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38082098759123238342656525 14280787034671214378496197)
                    ·
                      refine ⟨2677647569000852695968037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14280787034671214378496197 2677647569000852695968037)
                      ·
                        rfl

theorem cell23_5214700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_5214700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214700 prefixEnd_5214700 := by exact prefixLift 5214700
  have htrace : WordTrace (prefixWord ++ tailWord_5214700) baseStart_5214700 baseEnd_5214700 := by
    simpa [prefixWord, tailWord_5214700, baseEnd_5214700] using wordTrace_append hprefix tailTrace_5214700
  have hstable : (prefixWord ++ tailWord_5214700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214700).length < 2 ^ (prefixWord ++ tailWord_5214700).sum := by decide
  have hdescent : baseEnd_5214700 < baseStart_5214700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214717 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_5214717 : Nat := 118140960795 + 5214717 * 2 ^ 59
def prefixEnd_5214717 : Nat := 4983230072969 + 3 ^ 40 * 5214717 * 2
def baseEnd_5214717 : Nat := 2677656298171979129455459

theorem tailTrace_5214717 : CollatzResearch.WordTrace tailWord_5214717 prefixEnd_5214717 2677656298171979129455459 := by
  unfold tailWord_5214717
  simp only [CollatzResearch.WordTrace]
  refine ⟨190196354248978386604202405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126797569499318924402801603 190196354248978386604202405)
  ·
    refine ⟨35661816421683447488287951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190196354248978386604202405 35661816421683447488287951)
    ·
      refine ⟨53492724632525171232431927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35661816421683447488287951 53492724632525171232431927)
      ·
        refine ⟨80239086948787756848647891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53492724632525171232431927 80239086948787756848647891)
        ·
          refine ⟨120358630423181635272971837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80239086948787756848647891 120358630423181635272971837)
          ·
            refine ⟨45134486408693113227364439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120358630423181635272971837 45134486408693113227364439)
            ·
              refine ⟨67701729613039669841046659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45134486408693113227364439 67701729613039669841046659)
              ·
                refine ⟨101552594419559504761569989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67701729613039669841046659 101552594419559504761569989)
                ·
                  refine ⟨19041111453667407142794373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101552594419559504761569989 19041111453667407142794373)
                  ·
                    refine ⟨3570208397562638839273945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19041111453667407142794373 3570208397562638839273945)
                    ·
                      refine ⟨2677656298171979129455459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570208397562638839273945 2677656298171979129455459)
                      ·
                        rfl

theorem cell23_5214717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_5214717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214717 prefixEnd_5214717 := by exact prefixLift 5214717
  have htrace : WordTrace (prefixWord ++ tailWord_5214717) baseStart_5214717 baseEnd_5214717 := by
    simpa [prefixWord, tailWord_5214717, baseEnd_5214717] using wordTrace_append hprefix tailTrace_5214717
  have hstable : (prefixWord ++ tailWord_5214717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214717).length < 2 ^ (prefixWord ++ tailWord_5214717).sum := by decide
  have hdescent : baseEnd_5214717 < baseStart_5214717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214730 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5214730 : Nat := 118140960795 + 5214730 * 2 ^ 59
def prefixEnd_5214730 : Nat := 4983230072969 + 3 ^ 40 * 5214730 * 2
def baseEnd_5214730 : Nat := 2677662973420487578592899

theorem tailTrace_5214730 : CollatzResearch.WordTrace tailWord_5214730 prefixEnd_5214730 2677662973420487578592899 := by
  unfold tailWord_5214730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47549207099482822456106411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126797885598620859882950429 47549207099482822456106411)
  ·
    refine ⟨71323810649224233684159617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47549207099482822456106411 71323810649224233684159617)
    ·
      refine ⟨53492857986918175263119713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71323810649224233684159617 53492857986918175263119713)
      ·
        refine ⟨40119643490188631447339785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53492857986918175263119713 40119643490188631447339785)
        ·
          refine ⟨30089732617641473585504839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40119643490188631447339785 30089732617641473585504839)
          ·
            refine ⟨45134598926462210378257259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30089732617641473585504839 45134598926462210378257259)
            ·
              refine ⟨67701898389693315567385889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45134598926462210378257259 67701898389693315567385889)
              ·
                refine ⟨50776423792269986675539417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67701898389693315567385889 50776423792269986675539417)
                ·
                  refine ⟨38082317844202490006654563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50776423792269986675539417 38082317844202490006654563)
                  ·
                    refine ⟨57123476766303735009981845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38082317844202490006654563 57123476766303735009981845)
                    ·
                      refine ⟨2677662973420487578592899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57123476766303735009981845 2677662973420487578592899)
                      ·
                        rfl

theorem cell23_5214730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5214730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214730 prefixEnd_5214730 := by exact prefixLift 5214730
  have htrace : WordTrace (prefixWord ++ tailWord_5214730) baseStart_5214730 baseEnd_5214730 := by
    simpa [prefixWord, tailWord_5214730, baseEnd_5214730] using wordTrace_append hprefix tailTrace_5214730
  have hstable : (prefixWord ++ tailWord_5214730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214730).length < 2 ^ (prefixWord ++ tailWord_5214730).sum := by decide
  have hdescent : baseEnd_5214730 < baseStart_5214730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214734 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_5214734 : Nat := 118140960795 + 5214734 * 2 ^ 59
def prefixEnd_5214734 : Nat := 4983230072969 + 3 ^ 40 * 5214734 * 2
def baseEnd_5214734 : Nat := 2677665027343105562942881

theorem tailTrace_5214734 : CollatzResearch.WordTrace tailWord_5214734 prefixEnd_5214734 2677665027343105562942881 := by
  unfold tailWord_5214734
  simp only [CollatzResearch.WordTrace]
  refine ⟨23774621786239599813446407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126797982859944532338380837 23774621786239599813446407)
  ·
    refine ⟨35661932679359399720169611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23774621786239599813446407 35661932679359399720169611)
    ·
      refine ⟨53492899019039099580254417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35661932679359399720169611 53492899019039099580254417)
      ·
        refine ⟨40119674264279324685190813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53492899019039099580254417 40119674264279324685190813)
        ·
          refine ⟨15044877849104746756946555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40119674264279324685190813 15044877849104746756946555)
          ·
            refine ⟨22567316773657120135419833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15044877849104746756946555 22567316773657120135419833)
            ·
              refine ⟨16925487580242840101564875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22567316773657120135419833 16925487580242840101564875)
              ·
                refine ⟨25388231370364260152347313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16925487580242840101564875 25388231370364260152347313)
                ·
                  refine ⟨19041173527773195114260485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25388231370364260152347313 19041173527773195114260485)
                  ·
                    refine ⟨3570220036457474083923841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19041173527773195114260485 3570220036457474083923841)
                    ·
                      refine ⟨2677665027343105562942881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570220036457474083923841 2677665027343105562942881)
                      ·
                        rfl

theorem cell23_5214734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_5214734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214734 prefixEnd_5214734 := by exact prefixLift 5214734
  have htrace : WordTrace (prefixWord ++ tailWord_5214734) baseStart_5214734 baseEnd_5214734 := by
    simpa [prefixWord, tailWord_5214734, baseEnd_5214734] using wordTrace_append hprefix tailTrace_5214734
  have hstable : (prefixWord ++ tailWord_5214734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214734).length < 2 ^ (prefixWord ++ tailWord_5214734).sum := by decide
  have hdescent : baseEnd_5214734 < baseStart_5214734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214784 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 3, 1, 3]
def baseStart_5214784 : Nat := 118140960795 + 5214784 * 2 ^ 59
def prefixEnd_5214784 : Nat := 4983230072969 + 3 ^ 40 * 5214784 * 2
def baseEnd_5214784 : Nat := 2677690701375830367317651

theorem tailTrace_5214784 : CollatzResearch.WordTrace tailWord_5214784 prefixEnd_5214784 2677690701375830367317651 := by
  unfold tailWord_5214784
  simp only [CollatzResearch.WordTrace]
  refine ⟨95099398969867828523445703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126799198626490438031260937 95099398969867828523445703)
  ·
    refine ⟨142649098454801742785168555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95099398969867828523445703 142649098454801742785168555)
    ·
      refine ⟨213973647682202614177752833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142649098454801742785168555 213973647682202614177752833)
      ·
        refine ⟨160480235761651960633314625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213973647682202614177752833 160480235761651960633314625)
        ·
          refine ⟨120360176821238970474985969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160480235761651960633314625 120360176821238970474985969)
          ·
            refine ⟨90270132615929227856239477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120360176821238970474985969 90270132615929227856239477)
            ·
              refine ⟨8462824932743365111522451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90270132615929227856239477 8462824932743365111522451)
              ·
                refine ⟨12694237399115047667283677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462824932743365111522451 12694237399115047667283677)
                ·
                  refine ⟨4760339024668142875231379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12694237399115047667283677 4760339024668142875231379)
                  ·
                    refine ⟨7140508537002214312847069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4760339024668142875231379 7140508537002214312847069)
                    ·
                      refine ⟨2677690701375830367317651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7140508537002214312847069 2677690701375830367317651)
                      ·
                        rfl

theorem cell23_5214784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_5214784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214784 prefixEnd_5214784 := by exact prefixLift 5214784
  have htrace : WordTrace (prefixWord ++ tailWord_5214784) baseStart_5214784 baseEnd_5214784 := by
    simpa [prefixWord, tailWord_5214784, baseEnd_5214784] using wordTrace_append hprefix tailTrace_5214784
  have hstable : (prefixWord ++ tailWord_5214784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214784).length < 2 ^ (prefixWord ++ tailWord_5214784).sum := by decide
  have hdescent : baseEnd_5214784 < baseStart_5214784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214804 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_5214804 : Nat := 118140960795 + 5214804 * 2 ^ 59
def prefixEnd_5214804 : Nat := 4983230072969 + 3 ^ 40 * 5214804 * 2
def baseEnd_5214804 : Nat := 892566990329640096355853

theorem tailTrace_5214804 : CollatzResearch.WordTrace tailWord_5214804 prefixEnd_5214804 892566990329640096355853 := by
  unfold tailWord_5214804
  simp only [CollatzResearch.WordTrace]
  refine ⟨95099763699831600231309733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126799684933108800308412977 95099763699831600231309733)
  ·
    refine ⟨17831205693718425043370575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95099763699831600231309733 17831205693718425043370575)
    ·
      refine ⟨26746808540577637565055863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17831205693718425043370575 26746808540577637565055863)
      ·
        refine ⟨40120212810866456347583795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26746808540577637565055863 40120212810866456347583795)
        ·
          refine ⟨60180319216299684521375693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40120212810866456347583795 60180319216299684521375693)
          ·
            refine ⟨22567619706112381695515885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60180319216299684521375693 22567619706112381695515885)
            ·
              refine ⟨8462857389792143135818457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22567619706112381695515885 8462857389792143135818457)
              ·
                refine ⟨6347143042344107351863843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8462857389792143135818457 6347143042344107351863843)
                ·
                  refine ⟨9520714563516161027795765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347143042344107351863843 9520714563516161027795765)
                  ·
                    refine ⟨892566990329640096355853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9520714563516161027795765 892566990329640096355853)
                    ·
                      rfl

theorem cell23_5214804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_5214804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214804 prefixEnd_5214804 := by exact prefixLift 5214804
  have htrace : WordTrace (prefixWord ++ tailWord_5214804) baseStart_5214804 baseEnd_5214804 := by
    simpa [prefixWord, tailWord_5214804, baseEnd_5214804] using wordTrace_append hprefix tailTrace_5214804
  have hstable : (prefixWord ++ tailWord_5214804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214804).length < 2 ^ (prefixWord ++ tailWord_5214804).sum := by decide
  have hdescent : baseEnd_5214804 < baseStart_5214804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214807 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_5214807 : Nat := 118140960795 + 5214807 * 2 ^ 59
def prefixEnd_5214807 : Nat := 4983230072969 + 3 ^ 40 * 5214807 * 2
def baseEnd_5214807 : Nat := 2677702511430883777330045

theorem tailTrace_5214807 : CollatzResearch.WordTrace tailWord_5214807 prefixEnd_5214807 2677702511430883777330045 := by
  unfold tailWord_5214807
  simp only [CollatzResearch.WordTrace]
  refine ⟨190199636818652331974978675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126799757879101554649985783 190199636818652331974978675)
  ·
    refine ⟨285299455227978497962468013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190199636818652331974978675 285299455227978497962468013)
    ·
      refine ⟨106987295710491936735925505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285299455227978497962468013 106987295710491936735925505)
      ·
        refine ⟨80240471782868952551944129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106987295710491936735925505 80240471782868952551944129)
        ·
          refine ⟨60180353837151714413958097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80240471782868952551944129 60180353837151714413958097)
          ·
            refine ⟨45135265377863785810468573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60180353837151714413958097 45135265377863785810468573)
            ·
              refine ⟨16925724516698919678925715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45135265377863785810468573 16925724516698919678925715)
              ·
                refine ⟨25388586775048379518388573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16925724516698919678925715 25388586775048379518388573)
                ·
                  refine ⟨9520720040643142319395715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25388586775048379518388573 9520720040643142319395715)
                  ·
                    refine ⟨14281080060964713479093573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9520720040643142319395715 14281080060964713479093573)
                    ·
                      refine ⟨2677702511430883777330045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14281080060964713479093573 2677702511430883777330045)
                      ·
                        rfl

theorem cell23_5214807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_5214807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214807 prefixEnd_5214807 := by exact prefixLift 5214807
  have htrace : WordTrace (prefixWord ++ tailWord_5214807) baseStart_5214807 baseEnd_5214807 := by
    simpa [prefixWord, tailWord_5214807, baseEnd_5214807] using wordTrace_append hprefix tailTrace_5214807
  have hstable : (prefixWord ++ tailWord_5214807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214807).length < 2 ^ (prefixWord ++ tailWord_5214807).sum := by decide
  have hdescent : baseEnd_5214807 < baseStart_5214807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214810 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_5214810 : Nat := 118140960795 + 5214810 * 2 ^ 59
def prefixEnd_5214810 : Nat := 4983230072969 + 3 ^ 40 * 5214810 * 2
def baseEnd_5214810 : Nat := 2677704051872847265592531

theorem tailTrace_5214810 : CollatzResearch.WordTrace tailWord_5214810 prefixEnd_5214810 2677704051872847265592531 := by
  unfold tailWord_5214810
  simp only [CollatzResearch.WordTrace]
  refine ⟨47549936559410365871834471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126799830825094308991558589 47549936559410365871834471)
  ·
    refine ⟨71324904839115548807751707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47549936559410365871834471 71324904839115548807751707)
    ·
      refine ⟨106987357258673323211627561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71324904839115548807751707 106987357258673323211627561)
      ·
        refine ⟨80240517944004992408720671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106987357258673323211627561 80240517944004992408720671)
        ·
          refine ⟨120360776916007488613081007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80240517944004992408720671 120360776916007488613081007)
          ·
            refine ⟨180541165374011232919621511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120360776916007488613081007 180541165374011232919621511)
            ·
              refine ⟨270811748061016849379432267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180541165374011232919621511 270811748061016849379432267)
              ·
                refine ⟨406217622091525274069148401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270811748061016849379432267 406217622091525274069148401)
                ·
                  refine ⟨304663216568643955551861301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406217622091525274069148401 304663216568643955551861301)
                  ·
                    refine ⟨28562176553310370832986997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 304663216568643955551861301 28562176553310370832986997)
                    ·
                      refine ⟨2677704051872847265592531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28562176553310370832986997 2677704051872847265592531)
                      ·
                        rfl

theorem cell23_5214810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_5214810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214810 prefixEnd_5214810 := by exact prefixLift 5214810
  have htrace : WordTrace (prefixWord ++ tailWord_5214810) baseStart_5214810 baseEnd_5214810 := by
    simpa [prefixWord, tailWord_5214810, baseEnd_5214810] using wordTrace_append hprefix tailTrace_5214810
  have hstable : (prefixWord ++ tailWord_5214810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214810).length < 2 ^ (prefixWord ++ tailWord_5214810).sum := by decide
  have hdescent : baseEnd_5214810 < baseStart_5214810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214817 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 1, 6]
def baseStart_5214817 : Nat := 118140960795 + 5214817 * 2 ^ 59
def prefixEnd_5214817 : Nat := 4983230072969 + 3 ^ 40 * 5214817 * 2
def baseEnd_5214817 : Nat := 892569215412476246068333

theorem tailTrace_5214817 : CollatzResearch.WordTrace tailWord_5214817 prefixEnd_5214817 892569215412476246068333 := by
  unfold tailWord_5214817
  simp only [CollatzResearch.WordTrace]
  refine ⟨190200001548616103682842705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126800001032410735788561803 190200001548616103682842705)
  ·
    refine ⟨142650001161462077762132029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190200001548616103682842705 142650001161462077762132029)
    ·
      refine ⟨53493750435548279160799511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142650001161462077762132029 53493750435548279160799511)
      ·
        refine ⟨80240625653322418741199267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53493750435548279160799511 80240625653322418741199267)
        ·
          refine ⟨120360938479983628111798901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80240625653322418741199267 120360938479983628111798901)
          ·
            refine ⟨11283837982498465135481147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120360938479983628111798901 11283837982498465135481147)
            ·
              refine ⟨16925756973747697703221721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11283837982498465135481147 16925756973747697703221721)
              ·
                refine ⟨12694317730310773277416291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16925756973747697703221721 12694317730310773277416291)
                ·
                  refine ⟨19041476595466159916124437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12694317730310773277416291 19041476595466159916124437)
                  ·
                    refine ⟨892569215412476246068333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19041476595466159916124437 892569215412476246068333)
                    ·
                      rfl

theorem cell23_5214817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_5214817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214817 prefixEnd_5214817 := by exact prefixLift 5214817
  have htrace : WordTrace (prefixWord ++ tailWord_5214817) baseStart_5214817 baseEnd_5214817 := by
    simpa [prefixWord, tailWord_5214817, baseEnd_5214817] using wordTrace_append hprefix tailTrace_5214817
  have hstable : (prefixWord ++ tailWord_5214817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214817).length < 2 ^ (prefixWord ++ tailWord_5214817).sum := by decide
  have hdescent : baseEnd_5214817 < baseStart_5214817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214821 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_5214821 : Nat := 118140960795 + 5214821 * 2 ^ 59
def prefixEnd_5214821 : Nat := 4983230072969 + 3 ^ 40 * 5214821 * 2
def baseEnd_5214821 : Nat := 892569900053348907518327

theorem tailTrace_5214821 : CollatzResearch.WordTrace tailWord_5214821 prefixEnd_5214821 892569900053348907518327 := by
  unfold tailWord_5214821
  simp only [CollatzResearch.WordTrace]
  refine ⟨190200147440601612365988317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126800098293734408243992211 190200147440601612365988317)
  ·
    refine ⟨71325055290225604637245619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190200147440601612365988317 71325055290225604637245619)
    ·
      refine ⟨106987582935338406955868429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71325055290225604637245619 106987582935338406955868429)
      ·
        refine ⟨40120343600751902608450661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106987582935338406955868429 40120343600751902608450661)
        ·
          refine ⟨7522564425140981739084499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40120343600751902608450661 7522564425140981739084499)
          ·
            refine ⟨11283846637711472608626749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522564425140981739084499 11283846637711472608626749)
            ·
              refine ⟨4231442489141802228235031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11283846637711472608626749 4231442489141802228235031)
              ·
                refine ⟨6347163733712703342352547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4231442489141802228235031 6347163733712703342352547)
                ·
                  refine ⟨9520745600569055013528821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347163733712703342352547 9520745600569055013528821)
                  ·
                    refine ⟨892569900053348907518327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9520745600569055013528821 892569900053348907518327)
                    ·
                      rfl

theorem cell23_5214821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_5214821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214821 prefixEnd_5214821 := by exact prefixLift 5214821
  have htrace : WordTrace (prefixWord ++ tailWord_5214821) baseStart_5214821 baseEnd_5214821 := by
    simpa [prefixWord, tailWord_5214821, baseEnd_5214821] using wordTrace_append hprefix tailTrace_5214821
  have hstable : (prefixWord ++ tailWord_5214821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214821).length < 2 ^ (prefixWord ++ tailWord_5214821).sum := by decide
  have hdescent : baseEnd_5214821 < baseStart_5214821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214858 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_5214858 : Nat := 118140960795 + 5214858 * 2 ^ 59
def prefixEnd_5214858 : Nat := 4983230072969 + 3 ^ 40 * 5214858 * 2
def baseEnd_5214858 : Nat := 2677728698944263077792311

theorem tailTrace_5214858 : CollatzResearch.WordTrace tailWord_5214858 prefixEnd_5214858 2677728698944263077792311 := by
  unfold tailWord_5214858
  simp only [CollatzResearch.WordTrace]
  refine ⟨47550374235366891921271307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126800997960978378456723485 47550374235366891921271307)
  ·
    refine ⟨71325561353050337881906961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47550374235366891921271307 71325561353050337881906961)
    ·
      refine ⟨53494171014787753411430221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71325561353050337881906961 53494171014787753411430221)
      ·
        refine ⟨20060314130545407529286333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53494171014787753411430221 20060314130545407529286333)
        ·
          refine ⟨7522617798954527823482375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20060314130545407529286333 7522617798954527823482375)
          ·
            refine ⟨11283926698431791735223563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522617798954527823482375 11283926698431791735223563)
            ·
              refine ⟨16925890047647687602835345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11283926698431791735223563 16925890047647687602835345)
              ·
                refine ⟨12694417535735765702126509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16925890047647687602835345 12694417535735765702126509)
                ·
                  refine ⟨4760406575900912138297441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12694417535735765702126509 4760406575900912138297441)
                  ·
                    refine ⟨3570304931925684103723081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4760406575900912138297441 3570304931925684103723081)
                    ·
                      refine ⟨2677728698944263077792311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570304931925684103723081 2677728698944263077792311)
                      ·
                        rfl

theorem cell23_5214858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_5214858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214858 prefixEnd_5214858 := by exact prefixLift 5214858
  have htrace : WordTrace (prefixWord ++ tailWord_5214858) baseStart_5214858 baseEnd_5214858 := by
    simpa [prefixWord, tailWord_5214858, baseEnd_5214858] using wordTrace_append hprefix tailTrace_5214858
  have hstable : (prefixWord ++ tailWord_5214858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214858).length < 2 ^ (prefixWord ++ tailWord_5214858).sum := by decide
  have hdescent : baseEnd_5214858 < baseStart_5214858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214908 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_5214908 : Nat := 118140960795 + 5214908 * 2 ^ 59
def prefixEnd_5214908 : Nat := 4983230072969 + 3 ^ 40 * 5214908 * 2
def baseEnd_5214908 : Nat := 2677754372976987882167081

theorem tailTrace_5214908 : CollatzResearch.WordTrace tailWord_5214908 prefixEnd_5214908 2677754372976987882167081 := by
  unfold tailWord_5214908
  simp only [CollatzResearch.WordTrace]
  refine ⟨95101660295643213112202689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126802213727524284149603585 95101660295643213112202689)
  ·
    refine ⟨71326245221732409834152017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95101660295643213112202689 71326245221732409834152017)
    ·
      refine ⟨53494683916299307375614013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71326245221732409834152017 53494683916299307375614013)
      ·
        refine ⟨20060506468612240265855255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53494683916299307375614013 20060506468612240265855255)
        ·
          refine ⟨30090759702918360398782883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20060506468612240265855255 30090759702918360398782883)
          ·
            refine ⟨45136139554377540598174325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30090759702918360398782883 45136139554377540598174325)
            ·
              refine ⟨4231513083222894431078843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45136139554377540598174325 4231513083222894431078843)
              ·
                refine ⟨6347269624834341646618265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4231513083222894431078843 6347269624834341646618265)
                ·
                  refine ⟨4760452218625756234963699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6347269624834341646618265 4760452218625756234963699)
                  ·
                    refine ⟨7140678327938634352445549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4760452218625756234963699 7140678327938634352445549)
                    ·
                      refine ⟨2677754372976987882167081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7140678327938634352445549 2677754372976987882167081)
                      ·
                        rfl

theorem cell23_5214908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_5214908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214908 prefixEnd_5214908 := by exact prefixLift 5214908
  have htrace : WordTrace (prefixWord ++ tailWord_5214908) baseStart_5214908 baseEnd_5214908 := by
    simpa [prefixWord, tailWord_5214908, baseEnd_5214908] using wordTrace_append hprefix tailTrace_5214908
  have hstable : (prefixWord ++ tailWord_5214908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214908).length < 2 ^ (prefixWord ++ tailWord_5214908).sum := by decide
  have hdescent : baseEnd_5214908 < baseStart_5214908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214967 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 6, 5]
def baseStart_5214967 : Nat := 118140960795 + 5214967 * 2 ^ 59
def prefixEnd_5214967 : Nat := 4983230072969 + 3 ^ 40 * 5214967 * 2
def baseEnd_5214967 : Nat := 892594889445201050443103

theorem tailTrace_5214967 : CollatzResearch.WordTrace tailWord_5214967 prefixEnd_5214967 892594889445201050443103 := by
  unfold tailWord_5214967
  simp only [CollatzResearch.WordTrace]
  refine ⟨190205472498072679300803155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126803648332048452867202103 190205472498072679300803155)
  ·
    refine ⟨285308208747109018951204733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190205472498072679300803155 285308208747109018951204733)
    ·
      refine ⟨106990578280165882106701775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285308208747109018951204733 106990578280165882106701775)
      ·
        refine ⟨160485867420248823160052663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106990578280165882106701775 160485867420248823160052663)
        ·
          refine ⟨240728801130373234740078995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160485867420248823160052663 240728801130373234740078995)
          ·
            refine ⟨361093201695559852110118493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240728801130373234740078995 361093201695559852110118493)
            ·
              refine ⟨135409950635834944541294435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361093201695559852110118493 135409950635834944541294435)
              ·
                refine ⟨203114925953752416811941653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135409950635834944541294435 203114925953752416811941653)
                ·
                  refine ⟨9521012154082144538059765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 203114925953752416811941653 9521012154082144538059765)
                  ·
                    refine ⟨892594889445201050443103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9521012154082144538059765 892594889445201050443103)
                    ·
                      rfl

theorem cell23_5214967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_5214967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214967 prefixEnd_5214967 := by exact prefixLift 5214967
  have htrace : WordTrace (prefixWord ++ tailWord_5214967) baseStart_5214967 baseEnd_5214967 := by
    simpa [prefixWord, tailWord_5214967, baseEnd_5214967] using wordTrace_append hprefix tailTrace_5214967
  have hstable : (prefixWord ++ tailWord_5214967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214967).length < 2 ^ (prefixWord ++ tailWord_5214967).sum := by decide
  have hdescent : baseEnd_5214967 < baseStart_5214967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214977 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5214977 : Nat := 118140960795 + 5214977 * 2 ^ 59
def prefixEnd_5214977 : Nat := 4983230072969 + 3 ^ 40 * 5214977 * 2
def baseEnd_5214977 : Nat := 2677789803142148112204263

theorem tailTrace_5214977 : CollatzResearch.WordTrace tailWord_5214977 prefixEnd_5214977 2677789803142148112204263 := by
  unfold tailWord_5214977
  simp only [CollatzResearch.WordTrace]
  refine ⟨190205837228036451008667185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126803891485357634005778123 190205837228036451008667185)
  ·
    refine ⟨142654377921027338256500389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190205837228036451008667185 142654377921027338256500389)
    ·
      refine ⟨26747695860192625923093823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142654377921027338256500389 26747695860192625923093823)
      ·
        refine ⟨40121543790288938884640735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26747695860192625923093823 40121543790288938884640735)
        ·
          refine ⟨60182315685433408326961103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40121543790288938884640735 60182315685433408326961103)
          ·
            refine ⟨90273473528150112490441655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60182315685433408326961103 90273473528150112490441655)
            ·
              refine ⟨135410210292225168735662483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90273473528150112490441655 135410210292225168735662483)
              ·
                refine ⟨203115315438337753103493725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135410210292225168735662483 203115315438337753103493725)
                ·
                  refine ⟨76168243289376657413810147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203115315438337753103493725 76168243289376657413810147)
                  ·
                    refine ⟨114252364934064986120715221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76168243289376657413810147 114252364934064986120715221)
                    ·
                      refine ⟨2677789803142148112204263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114252364934064986120715221 2677789803142148112204263)
                      ·
                        rfl

theorem cell23_5214977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5214977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214977 prefixEnd_5214977 := by exact prefixLift 5214977
  have htrace : WordTrace (prefixWord ++ tailWord_5214977) baseStart_5214977 baseEnd_5214977 := by
    simpa [prefixWord, tailWord_5214977, baseEnd_5214977] using wordTrace_append hprefix tailTrace_5214977
  have hstable : (prefixWord ++ tailWord_5214977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214977).length < 2 ^ (prefixWord ++ tailWord_5214977).sum := by decide
  have hdescent : baseEnd_5214977 < baseStart_5214977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214984 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 2, 5]
def baseStart_5214984 : Nat := 118140960795 + 5214984 * 2 ^ 59
def prefixEnd_5214984 : Nat := 4983230072969 + 3 ^ 40 * 5214984 * 2
def baseEnd_5214984 : Nat := 892597799168909861605577

theorem tailTrace_5214984 : CollatzResearch.WordTrace tailWord_5214984 prefixEnd_5214984 892597799168909861605577 := by
  unfold tailWord_5214984
  simp only [CollatzResearch.WordTrace]
  refine ⟨95103046269505545602086003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126804061692674060802781337 95103046269505545602086003)
  ·
    refine ⟨142654569404258318403129005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95103046269505545602086003 142654569404258318403129005)
    ·
      refine ⟨53495463526596869401173377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142654569404258318403129005 53495463526596869401173377)
      ·
        refine ⟨40121597644947652050880033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53495463526596869401173377 40121597644947652050880033)
        ·
          refine ⟨30091198233710739038160025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40121597644947652050880033 30091198233710739038160025)
          ·
            refine ⟨22568398675283054278620019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30091198233710739038160025 22568398675283054278620019)
            ·
              refine ⟨33852598012924581417930029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22568398675283054278620019 33852598012924581417930029)
              ·
                refine ⟨12694724254846718031723761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33852598012924581417930029 12694724254846718031723761)
                ·
                  refine ⟨9521043191135038523792821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12694724254846718031723761 9521043191135038523792821)
                  ·
                    refine ⟨892597799168909861605577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9521043191135038523792821 892597799168909861605577)
                    ·
                      rfl

theorem cell23_5214984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_5214984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5214984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5214984 prefixEnd_5214984 := by exact prefixLift 5214984
  have htrace : WordTrace (prefixWord ++ tailWord_5214984) baseStart_5214984 baseEnd_5214984 := by
    simpa [prefixWord, tailWord_5214984, baseEnd_5214984] using wordTrace_append hprefix tailTrace_5214984
  have hstable : (prefixWord ++ tailWord_5214984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214984).length < 2 ^ (prefixWord ++ tailWord_5214984).sum := by decide
  have hdescent : baseEnd_5214984 < baseStart_5214984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215017 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_5215017 : Nat := 118140960795 + 5215017 * 2 ^ 59
def prefixEnd_5215017 : Nat := 4983230072969 + 3 ^ 40 * 5215017 * 2
def baseEnd_5215017 : Nat := 2677810342368327955704079

theorem tailTrace_5215017 : CollatzResearch.WordTrace tailWord_5215017 prefixEnd_5215017 2677810342368327955704079 := by
  unfold tailWord_5215017
  simp only [CollatzResearch.WordTrace]
  refine ⟨190207296147891537840123305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126804864098594358560082203 190207296147891537840123305)
  ·
    refine ⟨142655472110918653380092479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190207296147891537840123305 142655472110918653380092479)
    ·
      refine ⟨213983208166377980070138719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142655472110918653380092479 213983208166377980070138719)
      ·
        refine ⟨320974812249566970105208079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213983208166377980070138719 320974812249566970105208079)
        ·
          refine ⟨481462218374350455157812119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320974812249566970105208079 481462218374350455157812119)
          ·
            refine ⟨722193327561525682736718179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481462218374350455157812119 722193327561525682736718179)
            ·
              refine ⟨1083289991342288524105077269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722193327561525682736718179 1083289991342288524105077269)
              ·
                refine ⟨50779218344169774567425497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1083289991342288524105077269 50779218344169774567425497)
                ·
                  refine ⟨38084413758127330925569123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50779218344169774567425497 38084413758127330925569123)
                  ·
                    refine ⟨57126620637190996388353685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38084413758127330925569123 57126620637190996388353685)
                    ·
                      refine ⟨2677810342368327955704079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57126620637190996388353685 2677810342368327955704079)
                      ·
                        rfl

theorem cell23_5215017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_5215017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215017 prefixEnd_5215017 := by exact prefixLift 5215017
  have htrace : WordTrace (prefixWord ++ tailWord_5215017) baseStart_5215017 baseEnd_5215017 := by
    simpa [prefixWord, tailWord_5215017, baseEnd_5215017] using wordTrace_append hprefix tailTrace_5215017
  have hstable : (prefixWord ++ tailWord_5215017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215017).length < 2 ^ (prefixWord ++ tailWord_5215017).sum := by decide
  have hdescent : baseEnd_5215017 < baseStart_5215017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215024 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3]
def baseStart_5215024 : Nat := 118140960795 + 5215024 * 2 ^ 59
def prefixEnd_5215024 : Nat := 4983230072969 + 3 ^ 40 * 5215024 * 2
def baseEnd_5215024 : Nat := 2677813936732909428316547

theorem tailTrace_5215024 : CollatzResearch.WordTrace tailWord_5215024 prefixEnd_5215024 2677813936732909428316547 := by
  unfold tailWord_5215024
  simp only [CollatzResearch.WordTrace]
  refine ⟨95103775729433089017814063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126805034305910785357085417 95103775729433089017814063)
  ·
    refine ⟨142655663594149633526721095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95103775729433089017814063 142655663594149633526721095)
    ·
      refine ⟨213983495391224450290081643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142655663594149633526721095 213983495391224450290081643)
      ·
        refine ⟨320975243086836675435122465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213983495391224450290081643 320975243086836675435122465)
        ·
          refine ⟨240731432315127506576341849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320975243086836675435122465 240731432315127506576341849)
          ·
            refine ⟨180548574236345629932256387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240731432315127506576341849 180548574236345629932256387)
            ·
              refine ⟨270822861354518444898384581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180548574236345629932256387 270822861354518444898384581)
              ·
                refine ⟨50779286503972208418447109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270822861354518444898384581 50779286503972208418447109)
                ·
                  refine ⟨9521116219494789078458833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50779286503972208418447109 9521116219494789078458833)
                  ·
                    refine ⟨7140837164621091808844125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9521116219494789078458833 7140837164621091808844125)
                    ·
                      refine ⟨2677813936732909428316547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7140837164621091808844125 2677813936732909428316547)
                      ·
                        rfl

theorem cell23_5215024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_5215024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215024 prefixEnd_5215024 := by exact prefixLift 5215024
  have htrace : WordTrace (prefixWord ++ tailWord_5215024) baseStart_5215024 baseEnd_5215024 := by
    simpa [prefixWord, tailWord_5215024, baseEnd_5215024] using wordTrace_append hprefix tailTrace_5215024
  have hstable : (prefixWord ++ tailWord_5215024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215024).length < 2 ^ (prefixWord ++ tailWord_5215024).sum := by decide
  have hdescent : baseEnd_5215024 < baseStart_5215024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215048 : List Nat := [2, 1, 3, 1, 1, 3, 4, 3, 1, 4]
def baseStart_5215048 : Nat := 118140960795 + 5215048 * 2 ^ 59
def prefixEnd_5215048 : Nat := 4983230072969 + 3 ^ 40 * 5215048 * 2
def baseEnd_5215048 : Nat := 892608753422872444805479

theorem tailTrace_5215048 : CollatzResearch.WordTrace tailWord_5215048 prefixEnd_5215048 892608753422872444805479 := by
  unfold tailWord_5215048
  simp only [CollatzResearch.WordTrace]
  refine ⟨95104213405389615067250899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126805617873852820089667865 95104213405389615067250899)
  ·
    refine ⟨142656320108084422600876349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95104213405389615067250899 142656320108084422600876349)
    ·
      refine ⟨53496120040531658475328631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142656320108084422600876349 53496120040531658475328631)
      ·
        refine ⟨80244180060797487712992947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53496120040531658475328631 80244180060797487712992947)
        ·
          refine ⟨120366270091196231569489421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80244180060797487712992947 120366270091196231569489421)
          ·
            refine ⟨45137351284198586838558533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120366270091196231569489421 45137351284198586838558533)
            ·
              refine ⟨8463253365787235032229725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45137351284198586838558533 8463253365787235032229725)
              ·
                refine ⟨3173720012170213137086147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8463253365787235032229725 3173720012170213137086147)
                ·
                  refine ⟨4760580018255319705629221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173720012170213137086147 4760580018255319705629221)
                  ·
                    refine ⟨892608753422872444805479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4760580018255319705629221 892608753422872444805479)
                    ·
                      rfl

theorem cell23_5215048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_5215048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215048 prefixEnd_5215048 := by exact prefixLift 5215048
  have htrace : WordTrace (prefixWord ++ tailWord_5215048) baseStart_5215048 baseEnd_5215048 := by
    simpa [prefixWord, tailWord_5215048, baseEnd_5215048] using wordTrace_append hprefix tailTrace_5215048
  have hstable : (prefixWord ++ tailWord_5215048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215048).length < 2 ^ (prefixWord ++ tailWord_5215048).sum := by decide
  have hdescent : baseEnd_5215048 < baseStart_5215048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215054 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_5215054 : Nat := 118140960795 + 5215054 * 2 ^ 59
def prefixEnd_5215054 : Nat := 4983230072969 + 3 ^ 40 * 5215054 * 2
def baseEnd_5215054 : Nat := 2677829341152544310941409

theorem tailTrace_5215054 : CollatzResearch.WordTrace tailWord_5215054 prefixEnd_5215054 2677829341152544310941409 := by
  unfold tailWord_5215054
  simp only [CollatzResearch.WordTrace]
  refine ⟨23776080706094686644902527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126805763765838328772813477 23776080706094686644902527)
  ·
    refine ⟨35664121059142029967353791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23776080706094686644902527 35664121059142029967353791)
    ·
      refine ⟨53496181588713044951030687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35664121059142029967353791 53496181588713044951030687)
      ·
        refine ⟨80244272383069567426546031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53496181588713044951030687 80244272383069567426546031)
        ·
          refine ⟨120366408574604351139819047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80244272383069567426546031 120366408574604351139819047)
          ·
            refine ⟨180549612861906526709728571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120366408574604351139819047 180549612861906526709728571)
            ·
              refine ⟨270824419292859790064592857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180549612861906526709728571 270824419292859790064592857)
              ·
                refine ⟨203118314469644842548444643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270824419292859790064592857 203118314469644842548444643)
                ·
                  refine ⟨304677471704467263822666965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203118314469644842548444643 304677471704467263822666965)
                  ·
                    refine ⟨7140878243073451495843757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 304677471704467263822666965 7140878243073451495843757)
                    ·
                      refine ⟨2677829341152544310941409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7140878243073451495843757 2677829341152544310941409)
                      ·
                        rfl

theorem cell23_5215054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_5215054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215054 prefixEnd_5215054 := by exact prefixLift 5215054
  have htrace : WordTrace (prefixWord ++ tailWord_5215054) baseStart_5215054 baseEnd_5215054 := by
    simpa [prefixWord, tailWord_5215054, baseEnd_5215054] using wordTrace_append hprefix tailTrace_5215054
  have hstable : (prefixWord ++ tailWord_5215054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215054).length < 2 ^ (prefixWord ++ tailWord_5215054).sum := by decide
  have hdescent : baseEnd_5215054 < baseStart_5215054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7]
def baseStart_5215067 : Nat := 118140960795 + 5215067 * 2 ^ 59
def prefixEnd_5215067 : Nat := 4983230072969 + 3 ^ 40 * 5215067 * 2
def baseEnd_5215067 : Nat := 2677836016401052760078849

theorem tailTrace_5215067 : CollatzResearch.WordTrace tailWord_5215067 prefixEnd_5215067 2677836016401052760078849 := by
  unfold tailWord_5215067
  simp only [CollatzResearch.WordTrace]
  refine ⟨190209119797710396379443455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126806079865140264252962303 190209119797710396379443455)
  ·
    refine ⟨285313679696565594569165183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190209119797710396379443455 285313679696565594569165183)
    ·
      refine ⟨427970519544848391853747775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285313679696565594569165183 427970519544848391853747775)
      ·
        refine ⟨641955779317272587780621663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427970519544848391853747775 641955779317272587780621663)
        ·
          refine ⟨962933668975908881670932495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641955779317272587780621663 962933668975908881670932495)
          ·
            refine ⟨1444400503463863322506398743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962933668975908881670932495 1444400503463863322506398743)
            ·
              refine ⟨2166600755195794983759598115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444400503463863322506398743 2166600755195794983759598115)
              ·
                refine ⟨3249901132793692475639397173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166600755195794983759598115 3249901132793692475639397173)
                ·
                  refine ⟨304678231199408669591193485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3249901132793692475639397173 304678231199408669591193485)
                  ·
                    refine ⟨114254336699778251096697557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304678231199408669591193485 114254336699778251096697557)
                    ·
                      refine ⟨2677836016401052760078849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114254336699778251096697557 2677836016401052760078849)
                      ·
                        rfl

theorem cell23_5215067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_5215067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215067 prefixEnd_5215067 := by exact prefixLift 5215067
  have htrace : WordTrace (prefixWord ++ tailWord_5215067) baseStart_5215067 baseEnd_5215067 := by
    simpa [prefixWord, tailWord_5215067, baseEnd_5215067] using wordTrace_append hprefix tailTrace_5215067
  have hstable : (prefixWord ++ tailWord_5215067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215067).length < 2 ^ (prefixWord ++ tailWord_5215067).sum := by decide
  have hdescent : baseEnd_5215067 < baseStart_5215067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215121 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 2, 4]
def baseStart_5215121 : Nat := 118140960795 + 5215121 * 2 ^ 59
def prefixEnd_5215121 : Nat := 4983230072969 + 3 ^ 40 * 5215121 * 2
def baseEnd_5215121 : Nat := 892621248118798516267867

theorem tailTrace_5215121 : CollatzResearch.WordTrace tailWord_5215121 prefixEnd_5215121 892621248118798516267867 := by
  unfold tailWord_5215121
  simp only [CollatzResearch.WordTrace]
  refine ⟨190211089339514763601909217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126807392893009842401272811 190211089339514763601909217)
  ·
    refine ⟨142658317004636072701431913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190211089339514763601909217 142658317004636072701431913)
    ·
      refine ⟨106993737753477054526073935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142658317004636072701431913 106993737753477054526073935)
      ·
        refine ⟨160490606630215581789110903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106993737753477054526073935 160490606630215581789110903)
        ·
          refine ⟨240735909945323372683666355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160490606630215581789110903 240735909945323372683666355)
          ·
            refine ⟨361103864917985059025499533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240735909945323372683666355 361103864917985059025499533)
            ·
              refine ⟨135413949344244397134562325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361103864917985059025499533 135413949344244397134562325)
              ·
                refine ⟨6347528875511456115682609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135413949344244397134562325 6347528875511456115682609)
                ·
                  refine ⟨4760646656633592086761957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6347528875511456115682609 4760646656633592086761957)
                  ·
                    refine ⟨892621248118798516267867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4760646656633592086761957 892621248118798516267867)
                    ·
                      rfl

theorem cell23_5215121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_5215121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215121 prefixEnd_5215121 := by exact prefixLift 5215121
  have htrace : WordTrace (prefixWord ++ tailWord_5215121) baseStart_5215121 baseEnd_5215121 := by
    simpa [prefixWord, tailWord_5215121, baseEnd_5215121] using wordTrace_append hprefix tailTrace_5215121
  have hstable : (prefixWord ++ tailWord_5215121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215121).length < 2 ^ (prefixWord ++ tailWord_5215121).sum := by decide
  have hdescent : baseEnd_5215121 < baseStart_5215121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215122 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5215122 : Nat := 118140960795 + 5215122 * 2 ^ 59
def prefixEnd_5215122 : Nat := 4983230072969 + 3 ^ 40 * 5215122 * 2
def baseEnd_5215122 : Nat := 2677864257837050044891097

theorem tailTrace_5215122 : CollatzResearch.WordTrace tailWord_5215122 prefixEnd_5215122 2677864257837050044891097 := by
  unfold tailWord_5215122
  simp only [CollatzResearch.WordTrace]
  refine ⟨47552781453127785193173905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126807417208340760515130413 47552781453127785193173905)
  ·
    refine ⟨35664586089845838894880429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47552781453127785193173905 35664586089845838894880429)
    ·
      refine ⟨13374219783692189585580161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35664586089845838894880429 13374219783692189585580161)
      ·
        refine ⟨10030664837769142189185121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13374219783692189585580161 10030664837769142189185121)
        ·
          refine ⟨7522998628326856641888841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10030664837769142189185121 7522998628326856641888841)
          ·
            refine ⟨5642248971245142481416631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7522998628326856641888841 5642248971245142481416631)
            ·
              refine ⟨8463373456867713722124947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642248971245142481416631 8463373456867713722124947)
              ·
                refine ⟨12695060185301570583187421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8463373456867713722124947 12695060185301570583187421)
                ·
                  refine ⟨4760647569488088968695283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12695060185301570583187421 4760647569488088968695283)
                  ·
                    refine ⟨7140971354232133453042925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4760647569488088968695283 7140971354232133453042925)
                    ·
                      refine ⟨2677864257837050044891097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7140971354232133453042925 2677864257837050044891097)
                      ·
                        rfl

theorem cell23_5215122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5215122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215122 prefixEnd_5215122 := by exact prefixLift 5215122
  have htrace : WordTrace (prefixWord ++ tailWord_5215122) baseStart_5215122 baseEnd_5215122 := by
    simpa [prefixWord, tailWord_5215122, baseEnd_5215122] using wordTrace_append hprefix tailTrace_5215122
  have hstable : (prefixWord ++ tailWord_5215122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215122).length < 2 ^ (prefixWord ++ tailWord_5215122).sum := by decide
  have hdescent : baseEnd_5215122 < baseStart_5215122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215161 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 3]
def baseStart_5215161 : Nat := 118140960795 + 5215161 * 2 ^ 59
def prefixEnd_5215161 : Nat := 4983230072969 + 3 ^ 40 * 5215161 * 2
def baseEnd_5215161 : Nat := 2677884283582575392303417

theorem tailTrace_5215161 : CollatzResearch.WordTrace tailWord_5215161 prefixEnd_5215161 2677884283582575392303417 := by
  unfold tailWord_5215161
  simp only [CollatzResearch.WordTrace]
  refine ⟨190212548259369850433365337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126808365506246566955576891 190212548259369850433365337)
  ·
    refine ⟨142659411194527387825024003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190212548259369850433365337 142659411194527387825024003)
    ·
      refine ⟨213989116791791081737536005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142659411194527387825024003 213989116791791081737536005)
      ·
        refine ⟨40122959398460827825788001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213989116791791081737536005 40122959398460827825788001)
        ·
          refine ⟨30092219548845620869341001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40122959398460827825788001 30092219548845620869341001)
          ·
            refine ⟨22569164661634215652005751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30092219548845620869341001 22569164661634215652005751)
            ·
              refine ⟨33853746992451323478008627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22569164661634215652005751 33853746992451323478008627)
              ·
                refine ⟨50780620488676985217012941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33853746992451323478008627 50780620488676985217012941)
                ·
                  refine ⟨19042732683253869456379853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50780620488676985217012941 19042732683253869456379853)
                  ·
                    refine ⟨7141024756220201046142445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19042732683253869456379853 7141024756220201046142445)
                    ·
                      refine ⟨2677884283582575392303417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7141024756220201046142445 2677884283582575392303417)
                      ·
                        rfl

theorem cell23_5215161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_5215161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215161 prefixEnd_5215161 := by exact prefixLift 5215161
  have htrace : WordTrace (prefixWord ++ tailWord_5215161) baseStart_5215161 baseEnd_5215161 := by
    simpa [prefixWord, tailWord_5215161, baseEnd_5215161] using wordTrace_append hprefix tailTrace_5215161
  have hstable : (prefixWord ++ tailWord_5215161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215161).length < 2 ^ (prefixWord ++ tailWord_5215161).sum := by decide
  have hdescent : baseEnd_5215161 < baseStart_5215161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215165 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_5215165 : Nat := 118140960795 + 5215165 * 2 ^ 59
def prefixEnd_5215165 : Nat := 4983230072969 + 3 ^ 40 * 5215165 * 2
def baseEnd_5215165 : Nat := 2677886337505193376653399

theorem tailTrace_5215165 : CollatzResearch.WordTrace tailWord_5215165 prefixEnd_5215165 2677886337505193376653399 := by
  unfold tailWord_5215165
  simp only [CollatzResearch.WordTrace]
  refine ⟨190212694151355359116510949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126808462767570239411007299 190212694151355359116510949)
  ·
    refine ⟨35664880153379129834345803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190212694151355359116510949 35664880153379129834345803)
    ·
      refine ⟨53497320230068694751518705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35664880153379129834345803 53497320230068694751518705)
      ·
        refine ⟨40122990172551521063639029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53497320230068694751518705 40122990172551521063639029)
        ·
          refine ⟨3761530328676705099716159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40122990172551521063639029 3761530328676705099716159)
          ·
            refine ⟨5642295493015057649574239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761530328676705099716159 5642295493015057649574239)
            ·
              refine ⟨8463443239522586474361359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642295493015057649574239 8463443239522586474361359)
              ·
                refine ⟨12695164859283879711542039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8463443239522586474361359 12695164859283879711542039)
                ·
                  refine ⟨19042747288925819567313059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12695164859283879711542039 19042747288925819567313059)
                  ·
                    refine ⟨28564120933388729350969589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19042747288925819567313059 28564120933388729350969589)
                    ·
                      refine ⟨2677886337505193376653399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28564120933388729350969589 2677886337505193376653399)
                      ·
                        rfl

theorem cell23_5215165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_5215165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215165 prefixEnd_5215165 := by exact prefixLift 5215165
  have htrace : WordTrace (prefixWord ++ tailWord_5215165) baseStart_5215165 baseEnd_5215165 := by
    simpa [prefixWord, tailWord_5215165, baseEnd_5215165] using wordTrace_append hprefix tailTrace_5215165
  have hstable : (prefixWord ++ tailWord_5215165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215165).length < 2 ^ (prefixWord ++ tailWord_5215165).sum := by decide
  have hdescent : baseEnd_5215165 < baseStart_5215165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215172 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5215172 : Nat := 118140960795 + 5215172 * 2 ^ 59
def prefixEnd_5215172 : Nat := 4983230072969 + 3 ^ 40 * 5215172 * 2
def baseEnd_5215172 : Nat := 892629977289924949755289

theorem tailTrace_5215172 : CollatzResearch.WordTrace tailWord_5215172 prefixEnd_5215172 892629977289924949755289 := by
  unfold tailWord_5215172
  simp only [CollatzResearch.WordTrace]
  refine ⟨95106474731164999656007885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126808632974886666208010513 95106474731164999656007885)
  ·
    refine ⟨35664928024186874871002957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95106474731164999656007885 35664928024186874871002957)
    ·
      refine ⟨13374348009070078076626109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35664928024186874871002957 13374348009070078076626109)
      ·
        refine ⟨5015380503401279278734791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13374348009070078076626109 5015380503401279278734791)
        ·
          refine ⟨7523070755101918918102187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5015380503401279278734791 7523070755101918918102187)
          ·
            refine ⟨11284606132652878377153281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7523070755101918918102187 11284606132652878377153281)
            ·
              refine ⟨8463454599489658782864961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11284606132652878377153281 8463454599489658782864961)
              ·
                refine ⟨6347590949617244087148721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8463454599489658782864961 6347590949617244087148721)
                ·
                  refine ⟨4760693212212933065361541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6347590949617244087148721 4760693212212933065361541)
                  ·
                    refine ⟨892629977289924949755289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4760693212212933065361541 892629977289924949755289)
                    ·
                      rfl

theorem cell23_5215172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5215172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215172 prefixEnd_5215172 := by exact prefixLift 5215172
  have htrace : WordTrace (prefixWord ++ tailWord_5215172) baseStart_5215172 baseEnd_5215172 := by
    simpa [prefixWord, tailWord_5215172, baseEnd_5215172] using wordTrace_append hprefix tailTrace_5215172
  have hstable : (prefixWord ++ tailWord_5215172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215172).length < 2 ^ (prefixWord ++ tailWord_5215172).sum := by decide
  have hdescent : baseEnd_5215172 < baseStart_5215172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215179 : List Nat := [1, 1, 1, 1, 3, 7, 2, 2, 1, 2, 2]
def baseStart_5215179 : Nat := 118140960795 + 5215179 * 2 ^ 59
def prefixEnd_5215179 : Nat := 4983230072969 + 3 ^ 40 * 5215179 * 2
def baseEnd_5215179 : Nat := 2677893526234356321878335

theorem tailTrace_5215179 : CollatzResearch.WordTrace tailWord_5215179 prefixEnd_5215179 2677893526234356321878335 := by
  unfold tailWord_5215179
  simp only [CollatzResearch.WordTrace]
  refine ⟨190213204773304639507520591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126808803182203093005013727 190213204773304639507520591)
  ·
    refine ⟨285319807159956959261280887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190213204773304639507520591 285319807159956959261280887)
    ·
      refine ⟨427979710739935438891921331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285319807159956959261280887 427979710739935438891921331)
      ·
        refine ⟨641969566109903158337881997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427979710739935438891921331 641969566109903158337881997)
        ·
          refine ⟨240738587291213684376705749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 641969566109903158337881997 240738587291213684376705749)
          ·
            refine ⟨5642310639637820727579041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 240738587291213684376705749 5642310639637820727579041)
            ·
              refine ⟨4231732979728365545684281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5642310639637820727579041 4231732979728365545684281)
              ·
                refine ⟨3173799734796274159263211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4231732979728365545684281 3173799734796274159263211)
                ·
                  refine ⟨4760699602194411238894817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173799734796274159263211 4760699602194411238894817)
                  ·
                    refine ⟨3570524701645808429171113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4760699602194411238894817 3570524701645808429171113)
                    ·
                      refine ⟨2677893526234356321878335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570524701645808429171113 2677893526234356321878335)
                      ·
                        rfl

theorem cell23_5215179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 2, 2].length) (baseStart_5215179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215179 prefixEnd_5215179 := by exact prefixLift 5215179
  have htrace : WordTrace (prefixWord ++ tailWord_5215179) baseStart_5215179 baseEnd_5215179 := by
    simpa [prefixWord, tailWord_5215179, baseEnd_5215179] using wordTrace_append hprefix tailTrace_5215179
  have hstable : (prefixWord ++ tailWord_5215179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215179).length < 2 ^ (prefixWord ++ tailWord_5215179).sum := by decide
  have hdescent : baseEnd_5215179 < baseStart_5215179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215222 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_5215222 : Nat := 118140960795 + 5215222 * 2 ^ 59
def prefixEnd_5215222 : Nat := 4983230072969 + 3 ^ 40 * 5215222 * 2
def baseEnd_5215222 : Nat := 2677915605902499653640637

theorem tailTrace_5215222 : CollatzResearch.WordTrace tailWord_5215222 prefixEnd_5215222 2677915605902499653640637 := by
  unfold tailWord_5215222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888423319509303615708495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126809848741432571900890613 11888423319509303615708495)
  ·
    refine ⟨17832634979263955423562743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11888423319509303615708495 17832634979263955423562743)
    ·
      refine ⟨26748952468895933135344115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17832634979263955423562743 26748952468895933135344115)
      ·
        refine ⟨40123428703343899703016173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26748952468895933135344115 40123428703343899703016173)
        ·
          refine ⟨15046285763753962388631065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40123428703343899703016173 15046285763753962388631065)
          ·
            refine ⟨11284714322815471791473299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15046285763753962388631065 11284714322815471791473299)
            ·
              refine ⟨16927071484223207687209949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11284714322815471791473299 16927071484223207687209949)
              ·
                refine ⟨6347651806583702882703731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16927071484223207687209949 6347651806583702882703731)
                ·
                  refine ⟨9521477709875554324055597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347651806583702882703731 9521477709875554324055597)
                  ·
                    refine ⟨3570554141203332871520849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9521477709875554324055597 3570554141203332871520849)
                    ·
                      refine ⟨2677915605902499653640637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570554141203332871520849 2677915605902499653640637)
                      ·
                        rfl

theorem cell23_5215222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_5215222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215222 prefixEnd_5215222 := by exact prefixLift 5215222
  have htrace : WordTrace (prefixWord ++ tailWord_5215222) baseStart_5215222 baseEnd_5215222 := by
    simpa [prefixWord, tailWord_5215222, baseEnd_5215222] using wordTrace_append hprefix tailTrace_5215222
  have hstable : (prefixWord ++ tailWord_5215222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215222).length < 2 ^ (prefixWord ++ tailWord_5215222).sum := by decide
  have hdescent : baseEnd_5215222 < baseStart_5215222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215224 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 11]
def baseStart_5215224 : Nat := 118140960795 + 5215224 * 2 ^ 59
def prefixEnd_5215224 : Nat := 4983230072969 + 3 ^ 40 * 5215224 * 2
def baseEnd_5215224 : Nat := 297546292540423182868403

theorem tailTrace_5215224 : CollatzResearch.WordTrace tailWord_5215224 prefixEnd_5215224 297546292540423182868403 := by
  unfold tailWord_5215224
  simp only [CollatzResearch.WordTrace]
  refine ⟨95107423029070806096454363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126809897372094408128605817 95107423029070806096454363)
  ·
    refine ⟨142661134543606209144681545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95107423029070806096454363 142661134543606209144681545)
    ·
      refine ⟨106995850907704656858511159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142661134543606209144681545 106995850907704656858511159)
      ·
        refine ⟨160493776361556985287766739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106995850907704656858511159 160493776361556985287766739)
        ·
          refine ⟨240740664542335477931650109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160493776361556985287766739 240740664542335477931650109)
          ·
            refine ⟨90277749203375804224368791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240740664542335477931650109 90277749203375804224368791)
            ·
              refine ⟨135416623805063706336553187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90277749203375804224368791 135416623805063706336553187)
              ·
                refine ⟨203124935707595559504829781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135416623805063706336553187 203124935707595559504829781)
                ·
                  refine ⟨297546292540423182868403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 203124935707595559504829781 297546292540423182868403)
                  ·
                    rfl

theorem cell23_5215224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 11].length) (baseStart_5215224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215224 prefixEnd_5215224 := by exact prefixLift 5215224
  have htrace : WordTrace (prefixWord ++ tailWord_5215224) baseStart_5215224 baseEnd_5215224 := by
    simpa [prefixWord, tailWord_5215224, baseEnd_5215224] using wordTrace_append hprefix tailTrace_5215224
  have hstable : (prefixWord ++ tailWord_5215224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215224).length < 2 ^ (prefixWord ++ tailWord_5215224).sum := by decide
  have hdescent : baseEnd_5215224 < baseStart_5215224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215281 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_5215281 : Nat := 118140960795 + 5215281 * 2 ^ 59
def prefixEnd_5215281 : Nat := 4983230072969 + 3 ^ 40 * 5215281 * 2
def baseEnd_5215281 : Nat := 2677945901261114922802865

theorem tailTrace_5215281 : CollatzResearch.WordTrace tailWord_5215281 prefixEnd_5215281 2677945901261114922802865 := by
  unfold tailWord_5215281
  simp only [CollatzResearch.WordTrace]
  refine ⟨190216925018935110927733697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126811283345956740618489131 190216925018935110927733697)
  ·
    refine ⟨142662693764201333195800273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190216925018935110927733697 142662693764201333195800273)
    ·
      refine ⟨106997020323150999896850205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142662693764201333195800273 106997020323150999896850205)
      ·
        refine ⟨40123882621181624961318827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106997020323150999896850205 40123882621181624961318827)
        ·
          refine ⟨60185823931772437441978241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40123882621181624961318827 60185823931772437441978241)
          ·
            refine ⟨45139367948829328081483681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60185823931772437441978241 45139367948829328081483681)
            ·
              refine ⟨33854525961621996061112761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45139367948829328081483681 33854525961621996061112761)
              ·
                refine ⟨25390894471216497045834571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33854525961621996061112761 25390894471216497045834571)
                ·
                  refine ⟨38086341706824745568751857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25390894471216497045834571 38086341706824745568751857)
                  ·
                    refine ⟨28564756280118559176563893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38086341706824745568751857 28564756280118559176563893)
                    ·
                      refine ⟨2677945901261114922802865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28564756280118559176563893 2677945901261114922802865)
                      ·
                        rfl

theorem cell23_5215281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_5215281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215281 prefixEnd_5215281 := by exact prefixLift 5215281
  have htrace : WordTrace (prefixWord ++ tailWord_5215281) baseStart_5215281 baseEnd_5215281 := by
    simpa [prefixWord, tailWord_5215281, baseEnd_5215281] using wordTrace_append hprefix tailTrace_5215281
  have hstable : (prefixWord ++ tailWord_5215281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215281).length < 2 ^ (prefixWord ++ tailWord_5215281).sum := by decide
  have hdescent : baseEnd_5215281 < baseStart_5215281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215288 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 2, 5]
def baseStart_5215288 : Nat := 118140960795 + 5215288 * 2 ^ 59
def prefixEnd_5215288 : Nat := 4983230072969 + 3 ^ 40 * 5215288 * 2
def baseEnd_5215288 : Nat := 892649831875232131805111

theorem tailTrace_5215288 : CollatzResearch.WordTrace tailWord_5215288 prefixEnd_5215288 892649831875232131805111 := by
  unfold tailWord_5215288
  simp only [CollatzResearch.WordTrace]
  refine ⟨95108590164954875561619259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126811453553273167415492345 95108590164954875561619259)
  ·
    refine ⟨142662885247432313342428889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95108590164954875561619259 142662885247432313342428889)
    ·
      refine ⟨106997163935574235006821667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142662885247432313342428889 106997163935574235006821667)
      ·
        refine ⟨160495745903361352510232501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106997163935574235006821667 160495745903361352510232501)
        ·
          refine ⟨15046476178440126797834297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160495745903361352510232501 15046476178440126797834297)
          ·
            refine ⟨11284857133830095098375723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15046476178440126797834297 11284857133830095098375723)
            ·
              refine ⟨16927285700745142647563585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11284857133830095098375723 16927285700745142647563585)
              ·
                refine ⟨12695464275558856985672689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16927285700745142647563585 12695464275558856985672689)
                ·
                  refine ⟨9521598206669142739254517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12695464275558856985672689 9521598206669142739254517)
                  ·
                    refine ⟨892649831875232131805111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9521598206669142739254517 892649831875232131805111)
                    ·
                      rfl

theorem cell23_5215288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_5215288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215288 prefixEnd_5215288 := by exact prefixLift 5215288
  have htrace : WordTrace (prefixWord ++ tailWord_5215288) baseStart_5215288 baseEnd_5215288 := by
    simpa [prefixWord, tailWord_5215288, baseEnd_5215288] using wordTrace_append hprefix tailTrace_5215288
  have hstable : (prefixWord ++ tailWord_5215288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215288).length < 2 ^ (prefixWord ++ tailWord_5215288).sum := by decide
  have hdescent : baseEnd_5215288 < baseStart_5215288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215308 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 1, 6, 2]
def baseStart_5215308 : Nat := 118140960795 + 5215308 * 2 ^ 59
def prefixEnd_5215308 : Nat := 4983230072969 + 3 ^ 40 * 5215308 * 2
def baseEnd_5215308 : Nat := 2677959765238786317165241

theorem tailTrace_5215308 : CollatzResearch.WordTrace tailWord_5215308 prefixEnd_5215308 2677959765238786317165241 := by
  unfold tailWord_5215308
  simp only [CollatzResearch.WordTrace]
  refine ⟨95108954894918647269483289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126811939859891529692644385 95108954894918647269483289)
  ·
    refine ⟨71331716171188985452112467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95108954894918647269483289 71331716171188985452112467)
    ·
      refine ⟨106997574256783478178168701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71331716171188985452112467 106997574256783478178168701)
      ·
        refine ⟨40124090346293804316813263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106997574256783478178168701 40124090346293804316813263)
        ·
          refine ⟨60186135519440706475219895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40124090346293804316813263 60186135519440706475219895)
          ·
            refine ⟨90279203279161059712829843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60186135519440706475219895 90279203279161059712829843)
            ·
              refine ⟨135418804918741589569244765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90279203279161059712829843 135418804918741589569244765)
              ·
                refine ⟨50782051844528096088466787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135418804918741589569244765 50782051844528096088466787)
                ·
                  refine ⟨76173077766792144132700181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50782051844528096088466787 76173077766792144132700181)
                  ·
                    refine ⟨3570613020318381756220321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76173077766792144132700181 3570613020318381756220321)
                    ·
                      refine ⟨2677959765238786317165241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570613020318381756220321 2677959765238786317165241)
                      ·
                        rfl

theorem cell23_5215308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_5215308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215308 prefixEnd_5215308 := by exact prefixLift 5215308
  have htrace : WordTrace (prefixWord ++ tailWord_5215308) baseStart_5215308 baseEnd_5215308 := by
    simpa [prefixWord, tailWord_5215308, baseEnd_5215308] using wordTrace_append hprefix tailTrace_5215308
  have hstable : (prefixWord ++ tailWord_5215308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215308).length < 2 ^ (prefixWord ++ tailWord_5215308).sum := by decide
  have hdescent : baseEnd_5215308 < baseStart_5215308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215351 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_5215351 : Nat := 118140960795 + 5215351 * 2 ^ 59
def prefixEnd_5215351 : Nat := 4983230072969 + 3 ^ 40 * 5215351 * 2
def baseEnd_5215351 : Nat := 2677981844906929648927543

theorem tailTrace_5215351 : CollatzResearch.WordTrace tailWord_5215351 prefixEnd_5215351 2677981844906929648927543 := by
  unfold tailWord_5215351
  simp only [CollatzResearch.WordTrace]
  refine ⟨190219478128681512882781907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126812985419121008588521271 190219478128681512882781907)
  ·
    refine ⟨285329217193022269324172861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190219478128681512882781907 285329217193022269324172861)
    ·
      refine ⟨106998456447383350996564823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285329217193022269324172861 106998456447383350996564823)
      ·
        refine ⟨160497684671075026494847235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106998456447383350996564823 160497684671075026494847235)
        ·
          refine ⟨240746527006612539742270853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160497684671075026494847235 240746527006612539742270853)
          ·
            refine ⟨45139973813739851201675785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240746527006612539742270853 45139973813739851201675785)
            ·
              refine ⟨33854980360304888401256839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45139973813739851201675785 33854980360304888401256839)
              ·
                refine ⟨50782470540457332601885259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33854980360304888401256839 50782470540457332601885259)
                ·
                  refine ⟨76173705810685998902827889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50782470540457332601885259 76173705810685998902827889)
                  ·
                    refine ⟨57130279358014499177120917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76173705810685998902827889 57130279358014499177120917)
                    ·
                      refine ⟨2677981844906929648927543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57130279358014499177120917 2677981844906929648927543)
                      ·
                        rfl

theorem cell23_5215351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_5215351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215351 prefixEnd_5215351 := by exact prefixLift 5215351
  have htrace : WordTrace (prefixWord ++ tailWord_5215351) baseStart_5215351 baseEnd_5215351 := by
    simpa [prefixWord, tailWord_5215351, baseEnd_5215351] using wordTrace_append hprefix tailTrace_5215351
  have hstable : (prefixWord ++ tailWord_5215351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215351).length < 2 ^ (prefixWord ++ tailWord_5215351).sum := by decide
  have hdescent : baseEnd_5215351 < baseStart_5215351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215352 : List Nat := [2, 1, 2, 1, 1, 1, 8, 2, 1, 4]
def baseStart_5215352 : Nat := 118140960795 + 5215352 * 2 ^ 59
def prefixEnd_5215352 : Nat := 4983230072969 + 3 ^ 40 * 5215352 * 2
def baseEnd_5215352 : Nat := 892660786129194715005013

theorem tailTrace_5215352 : CollatzResearch.WordTrace tailWord_5215352 prefixEnd_5215352 892660786129194715005013 := by
  unfold tailWord_5215352
  simp only [CollatzResearch.WordTrace]
  refine ⟨95109757300838945026784155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126813009734451926702378873 95109757300838945026784155)
  ·
    refine ⟨142664635951258417540176233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95109757300838945026784155 142664635951258417540176233)
    ·
      refine ⟨106998476963443813155132175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142664635951258417540176233 106998476963443813155132175)
      ·
        refine ⟨160497715445165719732698263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106998476963443813155132175 160497715445165719732698263)
        ·
          refine ⟨240746573167748579599047395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160497715445165719732698263 240746573167748579599047395)
          ·
            refine ⟨361119859751622869398571093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240746573167748579599047395 361119859751622869398571093)
            ·
              refine ⟨4231873356464330500764505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 361119859751622869398571093 4231873356464330500764505)
              ·
                refine ⟨3173905017348247875573379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4231873356464330500764505 3173905017348247875573379)
                ·
                  refine ⟨4760857526022371813360069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173905017348247875573379 4760857526022371813360069)
                  ·
                    refine ⟨892660786129194715005013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4760857526022371813360069 892660786129194715005013)
                    ·
                      rfl

theorem cell23_5215352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_5215352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215352 prefixEnd_5215352 := by exact prefixLift 5215352
  have htrace : WordTrace (prefixWord ++ tailWord_5215352) baseStart_5215352 baseEnd_5215352 := by
    simpa [prefixWord, tailWord_5215352, baseEnd_5215352] using wordTrace_append hprefix tailTrace_5215352
  have hstable : (prefixWord ++ tailWord_5215352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215352).length < 2 ^ (prefixWord ++ tailWord_5215352).sum := by decide
  have hdescent : baseEnd_5215352 < baseStart_5215352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215408 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 4, 4]
def baseStart_5215408 : Nat := 118140960795 + 5215408 * 2 ^ 59
def prefixEnd_5215408 : Nat := 4983230072969 + 3 ^ 40 * 5215408 * 2
def baseEnd_5215408 : Nat := 892670371101411975304927

theorem tailTrace_5215408 : CollatzResearch.WordTrace tailWord_5215408 prefixEnd_5215408 892670371101411975304927 := by
  unfold tailWord_5215408
  simp only [CollatzResearch.WordTrace]
  refine ⟨95110778544737505808803439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126814371392983341078404585 95110778544737505808803439)
  ·
    refine ⟨142666167817106258713205159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95110778544737505808803439 142666167817106258713205159)
    ·
      refine ⟨213999251725659388069807739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142666167817106258713205159 213999251725659388069807739)
      ·
        refine ⟨320998877588489082104711609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213999251725659388069807739 320998877588489082104711609)
        ·
          refine ⟨240749158191366811578533707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320998877588489082104711609 240749158191366811578533707)
          ·
            refine ⟨361123737287050217367800561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240749158191366811578533707 361123737287050217367800561)
            ·
              refine ⟨270842802965287663025850421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361123737287050217367800561 270842802965287663025850421)
              ·
                refine ⟨25391512777995718408673477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270842802965287663025850421 25391512777995718408673477)
                ·
                  refine ⟨4760908645874197201626277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25391512777995718408673477 4760908645874197201626277)
                  ·
                    refine ⟨892670371101411975304927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4760908645874197201626277 892670371101411975304927)
                    ·
                      rfl

theorem cell23_5215408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_5215408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215408 prefixEnd_5215408 := by exact prefixLift 5215408
  have htrace : WordTrace (prefixWord ++ tailWord_5215408) baseStart_5215408 baseEnd_5215408 := by
    simpa [prefixWord, tailWord_5215408, baseEnd_5215408] using wordTrace_append hprefix tailTrace_5215408
  have hstable : (prefixWord ++ tailWord_5215408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215408).length < 2 ^ (prefixWord ++ tailWord_5215408).sum := by decide
  have hdescent : baseEnd_5215408 < baseStart_5215408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215409 : List Nat := [1, 2, 2, 5, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5215409 : Nat := 118140960795 + 5215409 * 2 ^ 59
def prefixEnd_5215409 : Nat := 4983230072969 + 3 ^ 40 * 5215409 * 2
def baseEnd_5215409 : Nat := 2678011626784890422002277

theorem tailTrace_5215409 : CollatzResearch.WordTrace tailWord_5215409 prefixEnd_5215409 2678011626784890422002277 := by
  unfold tailWord_5215409
  simp only [CollatzResearch.WordTrace]
  refine ⟨190221593562471388788393281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126814395708314259192262187 190221593562471388788393281)
  ·
    refine ⟨142666195171853541591294961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190221593562471388788393281 142666195171853541591294961)
    ·
      refine ⟨106999646378890156193471221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142666195171853541591294961 106999646378890156193471221)
      ·
        refine ⟨10031216848020952143137927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106999646378890156193471221 10031216848020952143137927)
        ·
          refine ⟨15046825272031428214706891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10031216848020952143137927 15046825272031428214706891)
          ·
            refine ⟨22570237908047142322060337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15046825272031428214706891 22570237908047142322060337)
            ·
              refine ⟨16927678431035356741545253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22570237908047142322060337 16927678431035356741545253)
              ·
                refine ⟨3173939705819129389039735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16927678431035356741545253 3173939705819129389039735)
                ·
                  refine ⟨4760909558728694083559603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173939705819129389039735 4760909558728694083559603)
                  ·
                    refine ⟨7141364338093041125339405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4760909558728694083559603 7141364338093041125339405)
                    ·
                      refine ⟨2678011626784890422002277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7141364338093041125339405 2678011626784890422002277)
                      ·
                        rfl

theorem cell23_5215409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5215409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215409 prefixEnd_5215409 := by exact prefixLift 5215409
  have htrace : WordTrace (prefixWord ++ tailWord_5215409) baseStart_5215409 baseEnd_5215409 := by
    simpa [prefixWord, tailWord_5215409, baseEnd_5215409] using wordTrace_append hprefix tailTrace_5215409
  have hstable : (prefixWord ++ tailWord_5215409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215409).length < 2 ^ (prefixWord ++ tailWord_5215409).sum := by decide
  have hdescent : baseEnd_5215409 < baseStart_5215409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215432 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_5215432 : Nat := 118140960795 + 5215432 * 2 ^ 59
def prefixEnd_5215432 : Nat := 4983230072969 + 3 ^ 40 * 5215432 * 2
def baseEnd_5215432 : Nat := 2678023436839943832014671

theorem tailTrace_5215432 : CollatzResearch.WordTrace tailWord_5215432 prefixEnd_5215432 2678023436839943832014671 := by
  unfold tailWord_5215432
  simp only [CollatzResearch.WordTrace]
  refine ⟨95111216220694031858240275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126814954960925375810987033 95111216220694031858240275)
  ·
    refine ⟨142666824331041047787360413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95111216220694031858240275 142666824331041047787360413)
    ·
      refine ⟨53500059124140392920260155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142666824331041047787360413 53500059124140392920260155)
      ·
        refine ⟨80250088686210589380390233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53500059124140392920260155 80250088686210589380390233)
        ·
          refine ⟨60187566514657942035292675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80250088686210589380390233 60187566514657942035292675)
          ·
            refine ⟨90281349771986913052939013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60187566514657942035292675 90281349771986913052939013)
            ·
              refine ⟨16927753082247546197426065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90281349771986913052939013 16927753082247546197426065)
              ·
                refine ⟨12695814811685659648069549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16927753082247546197426065 12695814811685659648069549)
                ·
                  refine ⟨4760930554382122368026081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12695814811685659648069549 4760930554382122368026081)
                  ·
                    refine ⟨3570697915786591776019561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4760930554382122368026081 3570697915786591776019561)
                    ·
                      refine ⟨2678023436839943832014671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570697915786591776019561 2678023436839943832014671)
                      ·
                        rfl

theorem cell23_5215432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_5215432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215432 prefixEnd_5215432 := by exact prefixLift 5215432
  have htrace : WordTrace (prefixWord ++ tailWord_5215432) baseStart_5215432 baseEnd_5215432 := by
    simpa [prefixWord, tailWord_5215432, baseEnd_5215432] using wordTrace_append hprefix tailTrace_5215432
  have hstable : (prefixWord ++ tailWord_5215432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215432).length < 2 ^ (prefixWord ++ tailWord_5215432).sum := by decide
  have hdescent : baseEnd_5215432 < baseStart_5215432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215482 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_5215482 : Nat := 118140960795 + 5215482 * 2 ^ 59
def prefixEnd_5215482 : Nat := 4983230072969 + 3 ^ 40 * 5215482 * 2
def baseEnd_5215482 : Nat := 2678049110872668636389441

theorem tailTrace_5215482 : CollatzResearch.WordTrace tailWord_5215482 prefixEnd_5215482 2678049110872668636389441 := by
  unfold tailWord_5215482
  simp only [CollatzResearch.WordTrace]
  refine ⟨47556064022801730563950175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126816170727471281503867133 47556064022801730563950175)
  ·
    refine ⟨71334096034202595845925263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47556064022801730563950175 71334096034202595845925263)
    ·
      refine ⟨107001144051303893768887895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71334096034202595845925263 107001144051303893768887895)
      ·
        refine ⟨160501716076955840653331843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107001144051303893768887895 160501716076955840653331843)
        ·
          refine ⟨240752574115433760979997765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160501716076955840653331843 240752574115433760979997765)
          ·
            refine ⟨45141107646643830183749581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240752574115433760979997765 45141107646643830183749581)
            ·
              refine ⟨16927915367491436318906093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45141107646643830183749581 16927915367491436318906093)
              ·
                refine ⟨6347968262809288619589785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16927915367491436318906093 6347968262809288619589785)
                ·
                  refine ⟨4760976197106966464692339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6347968262809288619589785 4760976197106966464692339)
                  ·
                    refine ⟨7141464295660449697038509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4760976197106966464692339 7141464295660449697038509)
                    ·
                      refine ⟨2678049110872668636389441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7141464295660449697038509 2678049110872668636389441)
                      ·
                        rfl

theorem cell23_5215482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_5215482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215482 prefixEnd_5215482 := by exact prefixLift 5215482
  have htrace : WordTrace (prefixWord ++ tailWord_5215482) baseStart_5215482 baseEnd_5215482 := by
    simpa [prefixWord, tailWord_5215482, baseEnd_5215482] using wordTrace_append hprefix tailTrace_5215482
  have hstable : (prefixWord ++ tailWord_5215482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215482).length < 2 ^ (prefixWord ++ tailWord_5215482).sum := by decide
  have hdescent : baseEnd_5215482 < baseStart_5215482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215498 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_5215498 : Nat := 118140960795 + 5215498 * 2 ^ 59
def prefixEnd_5215498 : Nat := 4983230072969 + 3 ^ 40 * 5215498 * 2
def baseEnd_5215498 : Nat := 892685775521046857929789

theorem tailTrace_5215498 : CollatzResearch.WordTrace tailWord_5215498 prefixEnd_5215498 892685775521046857929789 := by
  unfold tailWord_5215498
  simp only [CollatzResearch.WordTrace]
  refine ⟨47556209914787239247095787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126816559772765971325588765 47556209914787239247095787)
  ·
    refine ⟨71334314872180858870643681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47556209914787239247095787 71334314872180858870643681)
    ·
      refine ⟨53500736154135644152982761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71334314872180858870643681 53500736154135644152982761)
      ·
        refine ⟨40125552115601733114737071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53500736154135644152982761 40125552115601733114737071)
        ·
          refine ⟨60188328173402599672105607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40125552115601733114737071 60188328173402599672105607)
          ·
            refine ⟨90282492260103899508158411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60188328173402599672105607 90282492260103899508158411)
            ·
              refine ⟨135423738390155849262237617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90282492260103899508158411 135423738390155849262237617)
              ·
                refine ⟨101567803792616886946678213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135423738390155849262237617 101567803792616886946678213)
                ·
                  refine ⟨19043963211115666302502165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101567803792616886946678213 19043963211115666302502165)
                  ·
                    refine ⟨892685775521046857929789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19043963211115666302502165 892685775521046857929789)
                    ·
                      rfl

theorem cell23_5215498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_5215498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215498 prefixEnd_5215498 := by exact prefixLift 5215498
  have htrace : WordTrace (prefixWord ++ tailWord_5215498) baseStart_5215498 baseEnd_5215498 := by
    simpa [prefixWord, tailWord_5215498, baseEnd_5215498] using wordTrace_append hprefix tailTrace_5215498
  have hstable : (prefixWord ++ tailWord_5215498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215498).length < 2 ^ (prefixWord ++ tailWord_5215498).sum := by decide
  have hdescent : baseEnd_5215498 < baseStart_5215498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215525 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_5215525 : Nat := 118140960795 + 5215525 * 2 ^ 59
def prefixEnd_5215525 : Nat := 4983230072969 + 3 ^ 40 * 5215525 * 2
def baseEnd_5215525 : Nat := 2678071190540811968151743

theorem tailTrace_5215525 : CollatzResearch.WordTrace tailWord_5215525 prefixEnd_5215525 2678071190540811968151743 := by
  unfold tailWord_5215525
  simp only [CollatzResearch.WordTrace]
  refine ⟨190225824430051140599616029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126817216286700760399744019 190225824430051140599616029)
  ·
    refine ⟨71334684161269177724856011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190225824430051140599616029 71334684161269177724856011)
    ·
      refine ⟨107002026241903766587284017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71334684161269177724856011 107002026241903766587284017)
      ·
        refine ⟨80251519681427824940463013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107002026241903766587284017 80251519681427824940463013)
        ·
          refine ⟨15047159940267717176336815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80251519681427824940463013 15047159940267717176336815)
          ·
            refine ⟨22570739910401575764505223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15047159940267717176336815 22570739910401575764505223)
            ·
              refine ⟨33856109865602363646757835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22570739910401575764505223 33856109865602363646757835)
              ·
                refine ⟨50784164798403545470136753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33856109865602363646757835 50784164798403545470136753)
                ·
                  refine ⟨38088123598802659102602565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50784164798403545470136753 38088123598802659102602565)
                  ·
                    refine ⟨7141523174775498581737981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38088123598802659102602565 7141523174775498581737981)
                    ·
                      refine ⟨2678071190540811968151743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7141523174775498581737981 2678071190540811968151743)
                      ·
                        rfl

theorem cell23_5215525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_5215525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215525 prefixEnd_5215525 := by exact prefixLift 5215525
  have htrace : WordTrace (prefixWord ++ tailWord_5215525) baseStart_5215525 baseEnd_5215525 := by
    simpa [prefixWord, tailWord_5215525, baseEnd_5215525] using wordTrace_append hprefix tailTrace_5215525
  have hstable : (prefixWord ++ tailWord_5215525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215525).length < 2 ^ (prefixWord ++ tailWord_5215525).sum := by decide
  have hdescent : baseEnd_5215525 < baseStart_5215525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215539 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 2, 2, 2]
def baseStart_5215539 : Nat := 118140960795 + 5215539 * 2 ^ 59
def prefixEnd_5215539 : Nat := 4983230072969 + 3 ^ 40 * 5215539 * 2
def baseEnd_5215539 : Nat := 2678078379269974913376679

theorem tailTrace_5215539 : CollatzResearch.WordTrace tailWord_5215539 prefixEnd_5215539 2678078379269974913376679 := by
  unfold tailWord_5215539
  simp only [CollatzResearch.WordTrace]
  refine ⟨190226335052000420990625671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126817556701333613993750447 190226335052000420990625671)
  ·
    refine ⟨285339502578000631485938507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190226335052000420990625671 285339502578000631485938507)
    ·
      refine ⟨428009253867000947228907761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285339502578000631485938507 428009253867000947228907761)
      ·
        refine ⟨321006940400250710421680821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428009253867000947228907761 321006940400250710421680821)
        ·
          refine ⟨30094400662523504102032577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 321006940400250710421680821 30094400662523504102032577)
          ·
            refine ⟨22570800496892628076524433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30094400662523504102032577 22570800496892628076524433)
            ·
              refine ⟨16928100372669471057393325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22570800496892628076524433 16928100372669471057393325)
              ·
                refine ⟨6348037639751051646522497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16928100372669471057393325 6348037639751051646522497)
                ·
                  refine ⟨4761028229813288734891873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348037639751051646522497 4761028229813288734891873)
                  ·
                    refine ⟨3570771172359966551168905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761028229813288734891873 3570771172359966551168905)
                    ·
                      refine ⟨2678078379269974913376679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570771172359966551168905 2678078379269974913376679)
                      ·
                        rfl

theorem cell23_5215539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 2, 2].length) (baseStart_5215539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215539 prefixEnd_5215539 := by exact prefixLift 5215539
  have htrace : WordTrace (prefixWord ++ tailWord_5215539) baseStart_5215539 baseEnd_5215539 := by
    simpa [prefixWord, tailWord_5215539, baseEnd_5215539] using wordTrace_append hprefix tailTrace_5215539
  have hstable : (prefixWord ++ tailWord_5215539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215539).length < 2 ^ (prefixWord ++ tailWord_5215539).sum := by decide
  have hdescent : baseEnd_5215539 < baseStart_5215539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215672 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 1, 5, 2]
def baseStart_5215672 : Nat := 118140960795 + 5215672 * 2 ^ 59
def prefixEnd_5215672 : Nat := 4983230072969 + 3 ^ 40 * 5215672 * 2
def baseEnd_5215672 : Nat := 2678146672197022893013567

theorem tailTrace_5215672 : CollatzResearch.WordTrace tailWord_5215672 prefixEnd_5215672 2678146672197022893013567 := by
  unfold tailWord_5215672
  simp only [CollatzResearch.WordTrace]
  refine ⟨95115592980259292352608635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126820790640345723136811513 95115592980259292352608635)
  ·
    refine ⟨142673389470388938528912953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95115592980259292352608635 142673389470388938528912953)
    ·
      refine ⟨107005042102791703896684715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142673389470388938528912953 107005042102791703896684715)
      ·
        refine ⟨160507563154187555845027073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107005042102791703896684715 160507563154187555845027073)
        ·
          refine ⟨120380672365640666883770305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160507563154187555845027073 120380672365640666883770305)
          ·
            refine ⟨90285504274230500162827729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120380672365640666883770305 90285504274230500162827729)
            ·
              refine ⟨67714128205672875122120797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90285504274230500162827729 67714128205672875122120797)
              ·
                refine ⟨25392798077127328170795299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67714128205672875122120797 25392798077127328170795299)
                ·
                  refine ⟨38089197115690992256192949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25392798077127328170795299 38089197115690992256192949)
                  ·
                    refine ⟨3570862229596030524018089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38089197115690992256192949 3570862229596030524018089)
                    ·
                      refine ⟨2678146672197022893013567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3570862229596030524018089 2678146672197022893013567)
                      ·
                        rfl

theorem cell23_5215672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_5215672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215672 prefixEnd_5215672 := by exact prefixLift 5215672
  have htrace : WordTrace (prefixWord ++ tailWord_5215672) baseStart_5215672 baseEnd_5215672 := by
    simpa [prefixWord, tailWord_5215672, baseEnd_5215672] using wordTrace_append hprefix tailTrace_5215672
  have hstable : (prefixWord ++ tailWord_5215672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215672).length < 2 ^ (prefixWord ++ tailWord_5215672).sum := by decide
  have hdescent : baseEnd_5215672 < baseStart_5215672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215733 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5215733 : Nat := 118140960795 + 5215733 * 2 ^ 59
def prefixEnd_5215733 : Nat := 4983230072969 + 3 ^ 40 * 5215733 * 2
def baseEnd_5215733 : Nat := 892725998172315718116929

theorem tailTrace_5215733 : CollatzResearch.WordTrace tailWord_5215733 prefixEnd_5215733 892725998172315718116929 := by
  unfold tailWord_5215733
  simp only [CollatzResearch.WordTrace]
  refine ⟨190233410813297592123187853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126822273875531728082125235 190233410813297592123187853)
  ·
    refine ⟨71337529054986597046195445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190233410813297592123187853 71337529054986597046195445)
    ·
      refine ⟨6687893348904993473080823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71337529054986597046195445 6687893348904993473080823)
      ·
        refine ⟨10031840023357490209621235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6687893348904993473080823 10031840023357490209621235)
        ·
          refine ⟨15047760035036235314431853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10031840023357490209621235 15047760035036235314431853)
          ·
            refine ⟨5642910013138588242911945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15047760035036235314431853 5642910013138588242911945)
            ·
              refine ⟨4232182509853941182183959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5642910013138588242911945 4232182509853941182183959)
              ·
                refine ⟨6348273764780911773275939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232182509853941182183959 6348273764780911773275939)
                ·
                  refine ⟨9522410647171367659913909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6348273764780911773275939 9522410647171367659913909)
                  ·
                    refine ⟨892725998172315718116929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9522410647171367659913909 892725998172315718116929)
                    ·
                      rfl

theorem cell23_5215733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5215733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215733 prefixEnd_5215733 := by exact prefixLift 5215733
  have htrace : WordTrace (prefixWord ++ tailWord_5215733) baseStart_5215733 baseEnd_5215733 := by
    simpa [prefixWord, tailWord_5215733, baseEnd_5215733] using wordTrace_append hprefix tailTrace_5215733
  have hstable : (prefixWord ++ tailWord_5215733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215733).length < 2 ^ (prefixWord ++ tailWord_5215733).sum := by decide
  have hdescent : baseEnd_5215733 < baseStart_5215733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215736 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 1, 1, 4]
def baseStart_5215736 : Nat := 118140960795 + 5215736 * 2 ^ 59
def prefixEnd_5215736 : Nat := 4983230072969 + 3 ^ 40 * 5215736 * 2
def baseEnd_5215736 : Nat := 2678179534958910642613273

theorem tailTrace_5215736 : CollatzResearch.WordTrace tailWord_5215736 prefixEnd_5215736 2678179534958910642613273 := by
  unfold tailWord_5215736
  simp only [CollatzResearch.WordTrace]
  refine ⟨95116760116143361817773531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126822346821524482423698041 95116760116143361817773531)
  ·
    refine ⟨142675140174215042726660297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95116760116143361817773531 142675140174215042726660297)
    ·
      refine ⟨107006355130661282044995223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142675140174215042726660297 107006355130661282044995223)
      ·
        refine ⟨160509532695991923067492835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107006355130661282044995223 160509532695991923067492835)
        ·
          refine ⟨240764299043987884601239253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160509532695991923067492835 240764299043987884601239253)
          ·
            refine ⟨5642913258843466045341545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 240764299043987884601239253 5642913258843466045341545)
            ·
              refine ⟨4232184944132599534006159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5642913258843466045341545 4232184944132599534006159)
              ·
                refine ⟨6348277416198899301009239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232184944132599534006159 6348277416198899301009239)
                ·
                  refine ⟨9522416124298348951513859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6348277416198899301009239 9522416124298348951513859)
                  ·
                    refine ⟨14283624186447523427270789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9522416124298348951513859 14283624186447523427270789)
                    ·
                      refine ⟨2678179534958910642613273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14283624186447523427270789 2678179534958910642613273)
                      ·
                        rfl

theorem cell23_5215736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_5215736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215736 prefixEnd_5215736 := by exact prefixLift 5215736
  have htrace : WordTrace (prefixWord ++ tailWord_5215736) baseStart_5215736 baseEnd_5215736 := by
    simpa [prefixWord, tailWord_5215736, baseEnd_5215736] using wordTrace_append hprefix tailTrace_5215736
  have hstable : (prefixWord ++ tailWord_5215736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215736).length < 2 ^ (prefixWord ++ tailWord_5215736).sum := by decide
  have hdescent : baseEnd_5215736 < baseStart_5215736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215746 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5215746 : Nat := 118140960795 + 5215746 * 2 ^ 59
def prefixEnd_5215746 : Nat := 4983230072969 + 3 ^ 40 * 5215746 * 2
def baseEnd_5215746 : Nat := 892728223255151867829409

theorem tailTrace_5215746 : CollatzResearch.WordTrace tailWord_5215746 prefixEnd_5215746 892728223255151867829409 := by
  unfold tailWord_5215746
  simp only [CollatzResearch.WordTrace]
  refine ⟨47558471240562623835852773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126822589974833663562274061 47558471240562623835852773)
  ·
    refine ⟨8917213357605491969222395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47558471240562623835852773 8917213357605491969222395)
    ·
      refine ⟨13375820036408237953833593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8917213357605491969222395 13375820036408237953833593)
      ·
        refine ⟨10031865027306178465375195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13375820036408237953833593 10031865027306178465375195)
        ·
          refine ⟨15047797540959267698062793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10031865027306178465375195 15047797540959267698062793)
          ·
            refine ⟨11285848155719450773547095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15047797540959267698062793 11285848155719450773547095)
            ·
              refine ⟨16928772233579176160320643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11285848155719450773547095 16928772233579176160320643)
              ·
                refine ⟨25393158350368764240480965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16928772233579176160320643 25393158350368764240480965)
                ·
                  refine ⟨4761217190694143295090181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25393158350368764240480965 4761217190694143295090181)
                  ·
                    refine ⟨892728223255151867829409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4761217190694143295090181 892728223255151867829409)
                    ·
                      rfl

theorem cell23_5215746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5215746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215746 prefixEnd_5215746 := by exact prefixLift 5215746
  have htrace : WordTrace (prefixWord ++ tailWord_5215746) baseStart_5215746 baseEnd_5215746 := by
    simpa [prefixWord, tailWord_5215746, baseEnd_5215746] using wordTrace_append hprefix tailTrace_5215746
  have hstable : (prefixWord ++ tailWord_5215746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215746).length < 2 ^ (prefixWord ++ tailWord_5215746).sum := by decide
  have hdescent : baseEnd_5215746 < baseStart_5215746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215752 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_5215752 : Nat := 118140960795 + 5215752 * 2 ^ 59
def prefixEnd_5215752 : Nat := 4983230072969 + 3 ^ 40 * 5215752 * 2
def baseEnd_5215752 : Nat := 2678187750649382580013199

theorem tailTrace_5215752 : CollatzResearch.WordTrace tailWord_5215752 prefixEnd_5215752 2678187750649382580013199 := by
  unfold tailWord_5215752
  simp only [CollatzResearch.WordTrace]
  refine ⟨95117051900114379184064755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126822735866819172245419673 95117051900114379184064755)
  ·
    refine ⟨142675577850171568776097133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95117051900114379184064755 142675577850171568776097133)
    ·
      refine ⟨53503341693814338291036425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142675577850171568776097133 53503341693814338291036425)
      ·
        refine ⟨40127506270360753718277319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53503341693814338291036425 40127506270360753718277319)
        ·
          refine ⟨60191259405541130577415979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40127506270360753718277319 60191259405541130577415979)
          ·
            refine ⟨90286889108311695866123969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60191259405541130577415979 90286889108311695866123969)
            ·
              refine ⟨67715166831233771899592977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90286889108311695866123969 67715166831233771899592977)
              ·
                refine ⟨50786375123425328924694733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67715166831233771899592977 50786375123425328924694733)
                ·
                  refine ⟨19044890671284498346760525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50786375123425328924694733 19044890671284498346760525)
                  ·
                    refine ⟨7141834001731686880035197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19044890671284498346760525 7141834001731686880035197)
                    ·
                      refine ⟨2678187750649382580013199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7141834001731686880035197 2678187750649382580013199)
                      ·
                        rfl

theorem cell23_5215752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_5215752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215752 prefixEnd_5215752 := by exact prefixLift 5215752
  have htrace : WordTrace (prefixWord ++ tailWord_5215752) baseStart_5215752 baseEnd_5215752 := by
    simpa [prefixWord, tailWord_5215752, baseEnd_5215752] using wordTrace_append hprefix tailTrace_5215752
  have hstable : (prefixWord ++ tailWord_5215752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215752).length < 2 ^ (prefixWord ++ tailWord_5215752).sum := by decide
  have hdescent : baseEnd_5215752 < baseStart_5215752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215822 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_5215822 : Nat := 118140960795 + 5215822 * 2 ^ 59
def prefixEnd_5215822 : Nat := 4983230072969 + 3 ^ 40 * 5215822 * 2
def baseEnd_5215822 : Nat := 2678223694295197306137877

theorem tailTrace_5215822 : CollatzResearch.WordTrace tailWord_5215822 prefixEnd_5215822 2678223694295197306137877 := by
  unfold tailWord_5215822
  simp only [CollatzResearch.WordTrace]
  refine ⟨23779582113746895040397215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126824437939983440215451813 23779582113746895040397215)
  ·
    refine ⟨35669373170620342560595823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23779582113746895040397215 35669373170620342560595823)
    ·
      refine ⟨53504059755930513840893735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35669373170620342560595823 53504059755930513840893735)
      ·
        refine ⟨80256089633895770761340603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53504059755930513840893735 80256089633895770761340603)
        ·
          refine ⟨120384134450843656142010905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80256089633895770761340603 120384134450843656142010905)
          ·
            refine ⟨90288100838132742106508179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120384134450843656142010905 90288100838132742106508179)
            ·
              refine ⟨135432151257199113159762269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90288100838132742106508179 135432151257199113159762269)
              ·
                refine ⟨50787056721449667434910851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135432151257199113159762269 50787056721449667434910851)
                ·
                  refine ⟨76180585082174501152366277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50787056721449667434910851 76180585082174501152366277)
                  ·
                    refine ⟨14283859702907718966068677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76180585082174501152366277 14283859702907718966068677)
                    ·
                      refine ⟨2678223694295197306137877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14283859702907718966068677 2678223694295197306137877)
                      ·
                        rfl

theorem cell23_5215822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_5215822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215822 prefixEnd_5215822 := by exact prefixLift 5215822
  have htrace : WordTrace (prefixWord ++ tailWord_5215822) baseStart_5215822 baseEnd_5215822 := by
    simpa [prefixWord, tailWord_5215822, baseEnd_5215822] using wordTrace_append hprefix tailTrace_5215822
  have hstable : (prefixWord ++ tailWord_5215822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215822).length < 2 ^ (prefixWord ++ tailWord_5215822).sum := by decide
  have hdescent : baseEnd_5215822 < baseStart_5215822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215872 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_5215872 : Nat := 118140960795 + 5215872 * 2 ^ 59
def prefixEnd_5215872 : Nat := 4983230072969 + 3 ^ 40 * 5215872 * 2
def baseEnd_5215872 : Nat := 2678249368327922110512647

theorem tailTrace_5215872 : CollatzResearch.WordTrace tailWord_5215872 prefixEnd_5215872 2678249368327922110512647 := by
  unfold tailWord_5215872
  simp only [CollatzResearch.WordTrace]
  refine ⟨95119240279897009431248935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126825653706529345908331913 95119240279897009431248935)
  ·
    refine ⟨142678860419845514146873403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95119240279897009431248935 142678860419845514146873403)
    ·
      refine ⟨214018290629768271220310105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142678860419845514146873403 214018290629768271220310105)
      ·
        refine ⟨160513717972326203415232579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214018290629768271220310105 160513717972326203415232579)
        ·
          refine ⟨240770576958489305122848869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160513717972326203415232579 240770576958489305122848869)
          ·
            refine ⟨45144483179716744710534163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240770576958489305122848869 45144483179716744710534163)
            ·
              refine ⟨67716724769575117065801245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45144483179716744710534163 67716724769575117065801245)
              ·
                refine ⟨25393771788590668899675467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67716724769575117065801245 25393771788590668899675467)
                ·
                  refine ⟨38090657682886003349513201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25393771788590668899675467 38090657682886003349513201)
                  ·
                    refine ⟨28567993262164502512134901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38090657682886003349513201 28567993262164502512134901)
                    ·
                      refine ⟨2678249368327922110512647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28567993262164502512134901 2678249368327922110512647)
                      ·
                        rfl

theorem cell23_5215872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_5215872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215872 prefixEnd_5215872 := by exact prefixLift 5215872
  have htrace : WordTrace (prefixWord ++ tailWord_5215872) baseStart_5215872 baseEnd_5215872 := by
    simpa [prefixWord, tailWord_5215872, baseEnd_5215872] using wordTrace_append hprefix tailTrace_5215872
  have hstable : (prefixWord ++ tailWord_5215872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215872).length < 2 ^ (prefixWord ++ tailWord_5215872).sum := by decide
  have hdescent : baseEnd_5215872 < baseStart_5215872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215876 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_5215876 : Nat := 118140960795 + 5215876 * 2 ^ 59
def prefixEnd_5215876 : Nat := 4983230072969 + 3 ^ 40 * 5215876 * 2
def baseEnd_5215876 : Nat := 2678251422250540094862629

theorem tailTrace_5215876 : CollatzResearch.WordTrace tailWord_5215876 prefixEnd_5215876 2678251422250540094862629 := by
  unfold tailWord_5215876
  simp only [CollatzResearch.WordTrace]
  refine ⟨95119313225889763772821741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126825750967853018363762321 95119313225889763772821741)
  ·
    refine ⟨35669742459708661414808153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95119313225889763772821741 35669742459708661414808153)
    ·
      refine ⟨26752306844781496061106115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35669742459708661414808153 26752306844781496061106115)
      ·
        refine ⟨40128460267172244091659173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26752306844781496061106115 40128460267172244091659173)
        ·
          refine ⟨7524086300094795767186095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40128460267172244091659173 7524086300094795767186095)
          ·
            refine ⟨11286129450142193650779143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524086300094795767186095 11286129450142193650779143)
            ·
              refine ⟨16929194175213290476168715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11286129450142193650779143 16929194175213290476168715)
              ·
                refine ⟨25393791262819935714253073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16929194175213290476168715 25393791262819935714253073)
                ·
                  refine ⟨19045343447114951785689805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25393791262819935714253073 19045343447114951785689805)
                  ·
                    refine ⟨7142003792668106919633677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19045343447114951785689805 7142003792668106919633677)
                    ·
                      refine ⟨2678251422250540094862629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142003792668106919633677 2678251422250540094862629)
                      ·
                        rfl

theorem cell23_5215876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_5215876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215876 prefixEnd_5215876 := by exact prefixLift 5215876
  have htrace : WordTrace (prefixWord ++ tailWord_5215876) baseStart_5215876 baseEnd_5215876 := by
    simpa [prefixWord, tailWord_5215876, baseEnd_5215876] using wordTrace_append hprefix tailTrace_5215876
  have hstable : (prefixWord ++ tailWord_5215876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215876).length < 2 ^ (prefixWord ++ tailWord_5215876).sum := by decide
  have hdescent : baseEnd_5215876 < baseStart_5215876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215896 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 2, 5]
def baseStart_5215896 : Nat := 118140960795 + 5215896 * 2 ^ 59
def prefixEnd_5215896 : Nat := 4983230072969 + 3 ^ 40 * 5215896 * 2
def baseEnd_5215896 : Nat := 892753897287876672204179

theorem tailTrace_5215896 : CollatzResearch.WordTrace tailWord_5215896 prefixEnd_5215896 892753897287876672204179 := by
  unfold tailWord_5215896
  simp only [CollatzResearch.WordTrace]
  refine ⟨95119677955853535480685771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126826237274471380640914361 95119677955853535480685771)
  ·
    refine ⟨142679516933780303221028657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95119677955853535480685771 142679516933780303221028657)
    ·
      refine ⟨107009637700335227415771493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142679516933780303221028657 107009637700335227415771493)
      ·
        refine ⟨20064307068812855140457155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107009637700335227415771493 20064307068812855140457155)
        ·
          refine ⟨30096460603219282710685733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20064307068812855140457155 30096460603219282710685733)
          ·
            refine ⟨5643086363103615508253575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30096460603219282710685733 5643086363103615508253575)
            ·
              refine ⟨8464629544655423262380363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643086363103615508253575 8464629544655423262380363)
              ·
                refine ⟨12696944316983134893570545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8464629544655423262380363 12696944316983134893570545)
                ·
                  refine ⟨9522708237737351170177909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12696944316983134893570545 9522708237737351170177909)
                  ·
                    refine ⟨892753897287876672204179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9522708237737351170177909 892753897287876672204179)
                    ·
                      rfl

theorem cell23_5215896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_5215896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215896 prefixEnd_5215896 := by exact prefixLift 5215896
  have htrace : WordTrace (prefixWord ++ tailWord_5215896) baseStart_5215896 baseEnd_5215896 := by
    simpa [prefixWord, tailWord_5215896, baseEnd_5215896] using wordTrace_append hprefix tailTrace_5215896
  have hstable : (prefixWord ++ tailWord_5215896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215896).length < 2 ^ (prefixWord ++ tailWord_5215896).sum := by decide
  have hdescent : baseEnd_5215896 < baseStart_5215896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215919 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 3]
def baseStart_5215919 : Nat := 118140960795 + 5215919 * 2 ^ 59
def prefixEnd_5215919 : Nat := 4983230072969 + 3 ^ 40 * 5215919 * 2
def baseEnd_5215919 : Nat := 2678273501918683426624931

theorem tailTrace_5215919 : CollatzResearch.WordTrace tailWord_5215919 prefixEnd_5215919 2678273501918683426624931 := by
  unfold tailWord_5215919
  simp only [CollatzResearch.WordTrace]
  refine ⟨190240194790623745889458811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126826796527082497259639207 190240194790623745889458811)
  ·
    refine ⟨285360292185935618834188217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190240194790623745889458811 285360292185935618834188217)
    ·
      refine ⟨214020219139451714125641163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285360292185935618834188217 214020219139451714125641163)
      ·
        refine ⟨321030328709177571188461745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214020219139451714125641163 321030328709177571188461745)
        ·
          refine ⟨240772746531883178391346309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321030328709177571188461745 240772746531883178391346309)
          ·
            refine ⟨45144889974728095948377433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240772746531883178391346309 45144889974728095948377433)
            ·
              refine ⟨33858667481046071961283075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45144889974728095948377433 33858667481046071961283075)
              ·
                refine ⟨50788001221569107941924613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33858667481046071961283075 50788001221569107941924613)
                ·
                  refine ⟨9522750229044207739110865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50788001221569107941924613 9522750229044207739110865)
                  ·
                    refine ⟨7142062671783155804333149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9522750229044207739110865 7142062671783155804333149)
                    ·
                      refine ⟨2678273501918683426624931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142062671783155804333149 2678273501918683426624931)
                      ·
                        rfl

theorem cell23_5215919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_5215919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5215919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5215919 prefixEnd_5215919 := by exact prefixLift 5215919
  have htrace : WordTrace (prefixWord ++ tailWord_5215919) baseStart_5215919 baseEnd_5215919 := by
    simpa [prefixWord, tailWord_5215919, baseEnd_5215919] using wordTrace_append hprefix tailTrace_5215919
  have hstable : (prefixWord ++ tailWord_5215919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215919).length < 2 ^ (prefixWord ++ tailWord_5215919).sum := by decide
  have hdescent : baseEnd_5215919 < baseStart_5215919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216026 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_5216026 : Nat := 118140960795 + 5216026 * 2 ^ 59
def prefixEnd_5216026 : Nat := 4983230072969 + 3 ^ 40 * 5216026 * 2
def baseEnd_5216026 : Nat := 2678328444348714507986939

theorem tailTrace_5216026 : CollatzResearch.WordTrace tailWord_5216026 prefixEnd_5216026 2678328444348714507986939 := by
  unfold tailWord_5216026
  simp only [CollatzResearch.WordTrace]
  refine ⟨47561024350309025790900983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126829398267490735442402621 47561024350309025790900983)
  ·
    refine ⟨71341536525463538686351475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47561024350309025790900983 71341536525463538686351475)
    ·
      refine ⟨107012304788195308029527213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71341536525463538686351475 107012304788195308029527213)
      ·
        refine ⟨40129614295573240511072705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107012304788195308029527213 40129614295573240511072705)
        ·
          refine ⟨30097210721679930383304529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40129614295573240511072705 30097210721679930383304529)
          ·
            refine ⟨22572908041259947787478397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30097210721679930383304529 22572908041259947787478397)
            ·
              refine ⟨8464840515472480420304399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22572908041259947787478397 8464840515472480420304399)
              ·
                refine ⟨12697260773208720630456599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8464840515472480420304399 12697260773208720630456599)
                ·
                  refine ⟨19045891159813080945684899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12697260773208720630456599 19045891159813080945684899)
                  ·
                    refine ⟨28568836739719621418527349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19045891159813080945684899 28568836739719621418527349)
                    ·
                      refine ⟨2678328444348714507986939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28568836739719621418527349 2678328444348714507986939)
                      ·
                        rfl

theorem cell23_5216026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_5216026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216026 prefixEnd_5216026 := by exact prefixLift 5216026
  have htrace : WordTrace (prefixWord ++ tailWord_5216026) baseStart_5216026 baseEnd_5216026 := by
    simpa [prefixWord, tailWord_5216026, baseEnd_5216026] using wordTrace_append hprefix tailTrace_5216026
  have hstable : (prefixWord ++ tailWord_5216026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216026).length < 2 ^ (prefixWord ++ tailWord_5216026).sum := by decide
  have hdescent : baseEnd_5216026 < baseStart_5216026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216033 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 2, 4]
def baseStart_5216033 : Nat := 118140960795 + 5216033 * 2 ^ 59
def prefixEnd_5216033 : Nat := 4983230072969 + 3 ^ 40 * 5216033 * 2
def baseEnd_5216033 : Nat := 892777346237765326866469

theorem tailTrace_5216033 : CollatzResearch.WordTrace tailWord_5216033 prefixEnd_5216033 892777346237765326866469 := by
  unfold tailWord_5216033
  simp only [CollatzResearch.WordTrace]
  refine ⟨190244352712210743359108753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126829568474807162239405835 190244352712210743359108753)
  ·
    refine ⟨142683264534158057519331565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190244352712210743359108753 142683264534158057519331565)
    ·
      refine ⟨53506224200309271569749337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142683264534158057519331565 53506224200309271569749337)
      ·
        refine ⟨40129668150231953677312003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53506224200309271569749337 40129668150231953677312003)
        ·
          refine ⟨60194502225347930515968005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40129668150231953677312003 60194502225347930515968005)
          ·
            refine ⟨11286469167252736971744001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60194502225347930515968005 11286469167252736971744001)
            ·
              refine ⟨8464851875439552728808001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11286469167252736971744001 8464851875439552728808001)
              ·
                refine ⟨6348638906579664546606001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8464851875439552728808001 6348638906579664546606001)
                ·
                  refine ⟨4761479179934748409954501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348638906579664546606001 4761479179934748409954501)
                  ·
                    refine ⟨892777346237765326866469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4761479179934748409954501 892777346237765326866469)
                    ·
                      rfl

theorem cell23_5216033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_5216033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216033 prefixEnd_5216033 := by exact prefixLift 5216033
  have htrace : WordTrace (prefixWord ++ tailWord_5216033) baseStart_5216033 baseEnd_5216033 := by
    simpa [prefixWord, tailWord_5216033, baseEnd_5216033] using wordTrace_append hprefix tailTrace_5216033
  have hstable : (prefixWord ++ tailWord_5216033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216033).length < 2 ^ (prefixWord ++ tailWord_5216033).sum := by decide
  have hdescent : baseEnd_5216033 < baseStart_5216033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216053 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_5216053 : Nat := 118140960795 + 5216053 * 2 ^ 59
def prefixEnd_5216053 : Nat := 4983230072969 + 3 ^ 40 * 5216053 * 2
def baseEnd_5216053 : Nat := 2678342308326385902349315

theorem tailTrace_5216053 : CollatzResearch.WordTrace tailWord_5216053 prefixEnd_5216053 2678342308326385902349315 := by
  unfold tailWord_5216053
  simp only [CollatzResearch.WordTrace]
  refine ⟨190245082172138286774836813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126830054781425524516557875 190245082172138286774836813)
  ·
    refine ⟨71341905814551857540563805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190245082172138286774836813 71341905814551857540563805)
    ·
      refine ⟨26753214680456946577711427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71341905814551857540563805 26753214680456946577711427)
      ·
        refine ⟨40129822020685419866567141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26753214680456946577711427 40129822020685419866567141)
        ·
          refine ⟨7524341628878516224981339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40129822020685419866567141 7524341628878516224981339)
          ·
            refine ⟨11286512443317774337472009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524341628878516224981339 11286512443317774337472009)
            ·
              refine ⟨8464884332488330753104007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11286512443317774337472009 8464884332488330753104007)
              ·
                refine ⟨12697326498732496129656011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8464884332488330753104007 12697326498732496129656011)
                ·
                  refine ⟨19045989748098744194484017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12697326498732496129656011 19045989748098744194484017)
                  ·
                    refine ⟨14284492311074058145863013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19045989748098744194484017 14284492311074058145863013)
                    ·
                      refine ⟨2678342308326385902349315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14284492311074058145863013 2678342308326385902349315)
                      ·
                        rfl

theorem cell23_5216053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_5216053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216053 prefixEnd_5216053 := by exact prefixLift 5216053
  have htrace : WordTrace (prefixWord ++ tailWord_5216053) baseStart_5216053 baseEnd_5216053 := by
    simpa [prefixWord, tailWord_5216053, baseEnd_5216053] using wordTrace_append hprefix tailTrace_5216053
  have hstable : (prefixWord ++ tailWord_5216053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216053).length < 2 ^ (prefixWord ++ tailWord_5216053).sum := by decide
  have hdescent : baseEnd_5216053 < baseStart_5216053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216056 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_5216056 : Nat := 118140960795 + 5216056 * 2 ^ 59
def prefixEnd_5216056 : Nat := 4983230072969 + 3 ^ 40 * 5216056 * 2
def baseEnd_5216056 : Nat := 2678343848768349390611801

theorem tailTrace_5216056 : CollatzResearch.WordTrace tailWord_5216056 prefixEnd_5216056 2678343848768349390611801 := by
  unfold tailWord_5216056
  simp only [CollatzResearch.WordTrace]
  refine ⟨95122595795563709143598011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126830127727418278858130681 95122595795563709143598011)
  ·
    refine ⟨142683893693345563715397017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95122595795563709143598011 142683893693345563715397017)
    ·
      refine ⟨107012920270009172786547763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142683893693345563715397017 107012920270009172786547763)
      ·
        refine ⟨160519380405013759179821645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107012920270009172786547763 160519380405013759179821645)
        ·
          refine ⟨60194767651880159692433117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160519380405013759179821645 60194767651880159692433117)
          ·
            refine ⟨22573037869455059884662419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60194767651880159692433117 22573037869455059884662419)
            ·
              refine ⟨33859556804182589826993629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22573037869455059884662419 33859556804182589826993629)
              ·
                refine ⟨12697333801568471185122611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33859556804182589826993629 12697333801568471185122611)
                ·
                  refine ⟨19046000702352706777683917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12697333801568471185122611 19046000702352706777683917)
                  ·
                    refine ⟨7142250263382265041631469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19046000702352706777683917 7142250263382265041631469)
                    ·
                      refine ⟨2678343848768349390611801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142250263382265041631469 2678343848768349390611801)
                      ·
                        rfl

theorem cell23_5216056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_5216056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216056 prefixEnd_5216056 := by exact prefixLift 5216056
  have htrace : WordTrace (prefixWord ++ tailWord_5216056) baseStart_5216056 baseEnd_5216056 := by
    simpa [prefixWord, tailWord_5216056, baseEnd_5216056] using wordTrace_append hprefix tailTrace_5216056
  have hstable : (prefixWord ++ tailWord_5216056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216056).length < 2 ^ (prefixWord ++ tailWord_5216056).sum := by decide
  have hdescent : baseEnd_5216056 < baseStart_5216056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216057 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5216057 : Nat := 118140960795 + 5216057 * 2 ^ 59
def prefixEnd_5216057 : Nat := 4983230072969 + 3 ^ 40 * 5216057 * 2
def baseEnd_5216057 : Nat := 2678344362249003886699297

theorem tailTrace_5216057 : CollatzResearch.WordTrace tailWord_5216057 prefixEnd_5216057 2678344362249003886699297 := by
  unfold tailWord_5216057
  simp only [CollatzResearch.WordTrace]
  refine ⟨190245228064123795457982425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126830152042749196971988283 190245228064123795457982425)
  ·
    refine ⟨142683921048092846593486819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190245228064123795457982425 142683921048092846593486819)
    ·
      refine ⟨214025881572139269890230229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142683921048092846593486819 214025881572139269890230229)
      ·
        refine ⟨5016231599347014138052271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 214025881572139269890230229 5016231599347014138052271)
        ·
          refine ⟨7524347399020521207078407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016231599347014138052271 7524347399020521207078407)
          ·
            refine ⟨11286521098530781810617611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524347399020521207078407 11286521098530781810617611)
            ·
              refine ⟨16929781647796172715926417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11286521098530781810617611 16929781647796172715926417)
              ·
                refine ⟨12697336235847129536944813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16929781647796172715926417 12697336235847129536944813)
                ·
                  refine ⟨4761501088442673576354305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12697336235847129536944813 4761501088442673576354305)
                  ·
                    refine ⟨3571125816332005182265729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761501088442673576354305 3571125816332005182265729)
                    ·
                      refine ⟨2678344362249003886699297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571125816332005182265729 2678344362249003886699297)
                      ·
                        rfl

theorem cell23_5216057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5216057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216057 prefixEnd_5216057 := by exact prefixLift 5216057
  have htrace : WordTrace (prefixWord ++ tailWord_5216057) baseStart_5216057 baseEnd_5216057 := by
    simpa [prefixWord, tailWord_5216057, baseEnd_5216057] using wordTrace_append hprefix tailTrace_5216057
  have hstable : (prefixWord ++ tailWord_5216057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216057).length < 2 ^ (prefixWord ++ tailWord_5216057).sum := by decide
  have hdescent : baseEnd_5216057 < baseStart_5216057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216069 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_5216069 : Nat := 118140960795 + 5216069 * 2 ^ 59
def prefixEnd_5216069 : Nat := 4983230072969 + 3 ^ 40 * 5216069 * 2
def baseEnd_5216069 : Nat := 2678350524016857839749241

theorem tailTrace_5216069 : CollatzResearch.WordTrace tailWord_5216069 prefixEnd_5216069 2678350524016857839749241 := by
  unfold tailWord_5216069
  simp only [CollatzResearch.WordTrace]
  refine ⟨190245665740080321507419261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126830443826720214338279507 190245665740080321507419261)
  ·
    refine ⟨71342124652530120565282223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190245665740080321507419261 71342124652530120565282223)
    ·
      refine ⟨107013186978795180847923335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71342124652530120565282223 107013186978795180847923335)
      ·
        refine ⟨160519780468192771271885003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107013186978795180847923335 160519780468192771271885003)
        ·
          refine ⟨240779670702289156907827505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160519780468192771271885003 240779670702289156907827505)
          ·
            refine ⟨180584753026716867680870629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240779670702289156907827505 180584753026716867680870629)
            ·
              refine ⟨33859641192509412690163243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180584753026716867680870629 33859641192509412690163243)
              ·
                refine ⟨50789461788764119035244865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33859641192509412690163243 50789461788764119035244865)
                ·
                  refine ⟨38092096341573089276433649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50789461788764119035244865 38092096341573089276433649)
                  ·
                    refine ⟨28569072256179816957325237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38092096341573089276433649 28569072256179816957325237)
                    ·
                      refine ⟨2678350524016857839749241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28569072256179816957325237 2678350524016857839749241)
                      ·
                        rfl

theorem cell23_5216069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_5216069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216069 prefixEnd_5216069 := by exact prefixLift 5216069
  have htrace : WordTrace (prefixWord ++ tailWord_5216069) baseStart_5216069 baseEnd_5216069 := by
    simpa [prefixWord, tailWord_5216069, baseEnd_5216069] using wordTrace_append hprefix tailTrace_5216069
  have hstable : (prefixWord ++ tailWord_5216069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216069).length < 2 ^ (prefixWord ++ tailWord_5216069).sum := by decide
  have hdescent : baseEnd_5216069 < baseStart_5216069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216070 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5216070 : Nat := 118140960795 + 5216070 * 2 ^ 59
def prefixEnd_5216070 : Nat := 4983230072969 + 3 ^ 40 * 5216070 * 2
def baseEnd_5216070 : Nat := 2678351037497512335836737

theorem tailTrace_5216070 : CollatzResearch.WordTrace tailWord_5216070 prefixEnd_5216070 2678351037497512335836737 := by
  unfold tailWord_5216070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945178194158646833693927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126830468142051132452137109 5945178194158646833693927)
  ·
    refine ⟨8917767291237970250540891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5945178194158646833693927 8917767291237970250540891)
    ·
      refine ⟨13376650936856955375811337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8917767291237970250540891 13376650936856955375811337)
      ·
        refine ⟨10032488202642716531858503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13376650936856955375811337 10032488202642716531858503)
        ·
          refine ⟨15048732303964074797787755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10032488202642716531858503 15048732303964074797787755)
          ·
            refine ⟨22573098455946112196681633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15048732303964074797787755 22573098455946112196681633)
            ·
              refine ⟨16929823841959584147511225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22573098455946112196681633 16929823841959584147511225)
              ·
                refine ⟨12697367881469688110633419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16929823841959584147511225 12697367881469688110633419)
                ·
                  refine ⟨19046051822204532165950129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12697367881469688110633419 19046051822204532165950129)
                  ·
                    refine ⟨14284538866653399124462597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19046051822204532165950129 14284538866653399124462597)
                    ·
                      refine ⟨2678351037497512335836737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14284538866653399124462597 2678351037497512335836737)
                      ·
                        rfl

theorem cell23_5216070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5216070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216070 prefixEnd_5216070 := by exact prefixLift 5216070
  have htrace : WordTrace (prefixWord ++ tailWord_5216070) baseStart_5216070 baseEnd_5216070 := by
    simpa [prefixWord, tailWord_5216070, baseEnd_5216070] using wordTrace_append hprefix tailTrace_5216070
  have hstable : (prefixWord ++ tailWord_5216070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216070).length < 2 ^ (prefixWord ++ tailWord_5216070).sum := by decide
  have hdescent : baseEnd_5216070 < baseStart_5216070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216077 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5216077 : Nat := 118140960795 + 5216077 * 2 ^ 59
def prefixEnd_5216077 : Nat := 4983230072969 + 3 ^ 40 * 5216077 * 2
def baseEnd_5216077 : Nat := 2678354631862093808449205

theorem tailTrace_5216077 : CollatzResearch.WordTrace tailWord_5216077 prefixEnd_5216077 2678354631862093808449205 := by
  unfold tailWord_5216077
  simp only [CollatzResearch.WordTrace]
  refine ⟨190245957524051338873710485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126830638349367559249140323 190245957524051338873710485)
  ·
    refine ⟨8917779258939906509705179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 190245957524051338873710485 8917779258939906509705179)
    ·
      refine ⟨13376668888409859764557769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8917779258939906509705179 13376668888409859764557769)
      ·
        refine ⟨10032501666307394823418327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13376668888409859764557769 10032501666307394823418327)
        ·
          refine ⟨15048752499461092235127491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10032501666307394823418327 15048752499461092235127491)
          ·
            refine ⟨22573128749191638352691237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15048752499461092235127491 22573128749191638352691237)
            ·
              refine ⟨4232461640473432191129607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22573128749191638352691237 4232461640473432191129607)
              ·
                refine ⟨6348692460710148286694411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232461640473432191129607 6348692460710148286694411)
                ·
                  refine ⟨9523038691065222430041617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6348692460710148286694411 9523038691065222430041617)
                  ·
                    refine ⟨7142279018298916822531213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9523038691065222430041617 7142279018298916822531213)
                    ·
                      refine ⟨2678354631862093808449205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142279018298916822531213 2678354631862093808449205)
                      ·
                        rfl

theorem cell23_5216077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5216077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216077 prefixEnd_5216077 := by exact prefixLift 5216077
  have htrace : WordTrace (prefixWord ++ tailWord_5216077) baseStart_5216077 baseEnd_5216077 := by
    simpa [prefixWord, tailWord_5216077, baseEnd_5216077] using wordTrace_append hprefix tailTrace_5216077
  have hstable : (prefixWord ++ tailWord_5216077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216077).length < 2 ^ (prefixWord ++ tailWord_5216077).sum := by decide
  have hdescent : baseEnd_5216077 < baseStart_5216077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216089 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 4, 6]
def baseStart_5216089 : Nat := 118140960795 + 5216089 * 2 ^ 59
def prefixEnd_5216089 : Nat := 4983230072969 + 3 ^ 40 * 5216089 * 2
def baseEnd_5216089 : Nat := 892786931209982587166383

theorem tailTrace_5216089 : CollatzResearch.WordTrace tailWord_5216089 prefixEnd_5216089 892786931209982587166383 := by
  unfold tailWord_5216089
  simp only [CollatzResearch.WordTrace]
  refine ⟨190246395200007864923147321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126830930133338576615431547 190246395200007864923147321)
  ·
    refine ⟨142684796400005898692360491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190246395200007864923147321 142684796400005898692360491)
    ·
      refine ⟨214027194600008848038540737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142684796400005898692360491 214027194600008848038540737)
      ·
        refine ⟨160520395950006636028905553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214027194600008848038540737 160520395950006636028905553)
        ·
          refine ⟨120390296962504977021679165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160520395950006636028905553 120390296962504977021679165)
          ·
            refine ⟨45146361360939366383129687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120390296962504977021679165 45146361360939366383129687)
            ·
              refine ⟨67719542041409049574694531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45146361360939366383129687 67719542041409049574694531)
              ·
                refine ⟨101579313062113574362041797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67719542041409049574694531 101579313062113574362041797)
                ·
                  refine ⟨19046121199146295192882837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101579313062113574362041797 19046121199146295192882837)
                  ·
                    refine ⟨892786931209982587166383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19046121199146295192882837 892786931209982587166383)
                    ·
                      rfl

theorem cell23_5216089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_5216089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216089 prefixEnd_5216089 := by exact prefixLift 5216089
  have htrace : WordTrace (prefixWord ++ tailWord_5216089) baseStart_5216089 baseEnd_5216089 := by
    simpa [prefixWord, tailWord_5216089, baseEnd_5216089] using wordTrace_append hprefix tailTrace_5216089
  have hstable : (prefixWord ++ tailWord_5216089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216089).length < 2 ^ (prefixWord ++ tailWord_5216089).sum := by decide
  have hdescent : baseEnd_5216089 < baseStart_5216089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216158 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5216158 : Nat := 118140960795 + 5216158 * 2 ^ 59
def prefixEnd_5216158 : Nat := 4983230072969 + 3 ^ 40 * 5216158 * 2
def baseEnd_5216158 : Nat := 2678396223795107991536333

theorem tailTrace_5216158 : CollatzResearch.WordTrace tailWord_5216158 prefixEnd_5216158 2678396223795107991536333 := by
  unfold tailWord_5216158
  simp only [CollatzResearch.WordTrace]
  refine ⟨23781113979594736213426141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126832607891171926471606085 23781113979594736213426141)
  ·
    refine ⟨8917917742348026080034803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23781113979594736213426141 8917917742348026080034803)
    ·
      refine ⟨13376876613522039120052205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8917917742348026080034803 13376876613522039120052205)
      ·
        refine ⟨5016328730070764670019577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13376876613522039120052205 5016328730070764670019577)
        ·
          refine ⟨3762246547553073502514683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5016328730070764670019577 3762246547553073502514683)
          ·
            refine ⟨5643369821329610253772025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762246547553073502514683 5643369821329610253772025)
            ·
              refine ⟨4232527365997207690329019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5643369821329610253772025 4232527365997207690329019)
              ·
                refine ⟨6348791048995811535493529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232527365997207690329019 6348791048995811535493529)
                ·
                  refine ⟨4761593286746858651620147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348791048995811535493529 4761593286746858651620147)
                  ·
                    refine ⟨7142389930120287977430221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761593286746858651620147 7142389930120287977430221)
                    ·
                      refine ⟨2678396223795107991536333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142389930120287977430221 2678396223795107991536333)
                      ·
                        rfl

theorem cell23_5216158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5216158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216158 prefixEnd_5216158 := by exact prefixLift 5216158
  have htrace : WordTrace (prefixWord ++ tailWord_5216158) baseStart_5216158 baseEnd_5216158 := by
    simpa [prefixWord, tailWord_5216158, baseEnd_5216158] using wordTrace_append hprefix tailTrace_5216158
  have hstable : (prefixWord ++ tailWord_5216158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216158).length < 2 ^ (prefixWord ++ tailWord_5216158).sum := by decide
  have hdescent : baseEnd_5216158 < baseStart_5216158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216164 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_5216164 : Nat := 118140960795 + 5216164 * 2 ^ 59
def prefixEnd_5216164 : Nat := 4983230072969 + 3 ^ 40 * 5216164 * 2
def baseEnd_5216164 : Nat := 2678399304679034968061305

theorem tailTrace_5216164 : CollatzResearch.WordTrace tailWord_5216164 prefixEnd_5216164 2678399304679034968061305 := by
  unfold tailWord_5216164
  simp only [CollatzResearch.WordTrace]
  refine ⟨95124565337368076366063773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126832753783157435154751697 95124565337368076366063773)
  ·
    refine ⟨35671712001513028637273915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95124565337368076366063773 35671712001513028637273915)
    ·
      refine ⟨53507568002269542955910873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35671712001513028637273915 53507568002269542955910873)
      ·
        refine ⟨40130676001702157216933155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53507568002269542955910873 40130676001702157216933155)
        ·
          refine ⟨60196014002553235825399733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40130676001702157216933155 60196014002553235825399733)
          ·
            refine ⟨5643376312739365858631225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60196014002553235825399733 5643376312739365858631225)
            ·
              refine ⟨4232532234554524393973419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5643376312739365858631225 4232532234554524393973419)
              ·
                refine ⟨6348798351831786590960129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232532234554524393973419 6348798351831786590960129)
                ·
                  refine ⟨4761598763873839943220097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348798351831786590960129 4761598763873839943220097)
                  ·
                    refine ⟨3571199072905379957415073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761598763873839943220097 3571199072905379957415073)
                    ·
                      refine ⟨2678399304679034968061305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571199072905379957415073 2678399304679034968061305)
                      ·
                        rfl

theorem cell23_5216164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_5216164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216164 prefixEnd_5216164 := by exact prefixLift 5216164
  have htrace : WordTrace (prefixWord ++ tailWord_5216164) baseStart_5216164 baseEnd_5216164 := by
    simpa [prefixWord, tailWord_5216164, baseEnd_5216164] using wordTrace_append hprefix tailTrace_5216164
  have hstable : (prefixWord ++ tailWord_5216164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216164).length < 2 ^ (prefixWord ++ tailWord_5216164).sum := by decide
  have hdescent : baseEnd_5216164 < baseStart_5216164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216203 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 2, 4, 2]
def baseStart_5216203 : Nat := 118140960795 + 5216203 * 2 ^ 59
def prefixEnd_5216203 : Nat := 4983230072969 + 3 ^ 40 * 5216203 * 2
def baseEnd_5216203 : Nat := 2678419330424560315473625

theorem tailTrace_5216203 : CollatzResearch.WordTrace tailWord_5216203 prefixEnd_5216203 2678419330424560315473625 := by
  unfold tailWord_5216203
  simp only [CollatzResearch.WordTrace]
  refine ⟨190250553121594862392797263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126833702081063241595198175 190250553121594862392797263)
  ·
    refine ⟨285375829682392293589195895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190250553121594862392797263 285375829682392293589195895)
    ·
      refine ⟨428063744523588440383793843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285375829682392293589195895 428063744523588440383793843)
      ·
        refine ⟨642095616785382660575690765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428063744523588440383793843 642095616785382660575690765)
        ·
          refine ⟨240785856294518497715884037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642095616785382660575690765 240785856294518497715884037)
          ·
            refine ⟨45147348055222218321728257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240785856294518497715884037 45147348055222218321728257)
            ·
              refine ⟨33860511041416663741296193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45147348055222218321728257 33860511041416663741296193)
              ·
                refine ⟨25395383281062497805972145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33860511041416663741296193 25395383281062497805972145)
                ·
                  refine ⟨19046537460796873354479109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25395383281062497805972145 19046537460796873354479109)
                  ·
                    refine ⟨3571225773899413753964833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19046537460796873354479109 3571225773899413753964833)
                    ·
                      refine ⟨2678419330424560315473625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571225773899413753964833 2678419330424560315473625)
                      ·
                        rfl

theorem cell23_5216203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4, 2].length) (baseStart_5216203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216203 prefixEnd_5216203 := by exact prefixLift 5216203
  have htrace : WordTrace (prefixWord ++ tailWord_5216203) baseStart_5216203 baseEnd_5216203 := by
    simpa [prefixWord, tailWord_5216203, baseEnd_5216203] using wordTrace_append hprefix tailTrace_5216203
  have hstable : (prefixWord ++ tailWord_5216203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216203).length < 2 ^ (prefixWord ++ tailWord_5216203).sum := by decide
  have hdescent : baseEnd_5216203 < baseStart_5216203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216206 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_5216206 : Nat := 118140960795 + 5216206 * 2 ^ 59
def prefixEnd_5216206 : Nat := 4983230072969 + 3 ^ 40 * 5216206 * 2
def baseEnd_5216206 : Nat := 2678420870866523803736111

theorem tailTrace_5216206 : CollatzResearch.WordTrace tailWord_5216206 prefixEnd_5216206 2678420870866523803736111 := by
  unfold tailWord_5216206
  simp only [CollatzResearch.WordTrace]
  refine ⟨23781332817572999238144559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126833775027055995936770981 23781332817572999238144559)
  ·
    refine ⟨35671999226359498857216839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23781332817572999238144559 35671999226359498857216839)
    ·
      refine ⟨53507998839539248285825259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35671999226359498857216839 53507998839539248285825259)
      ·
        refine ⟨80261998259308872428737889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53507998839539248285825259 80261998259308872428737889)
        ·
          refine ⟨60196498694481654321553417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80261998259308872428737889 60196498694481654321553417)
          ·
            refine ⟨45147374020861240741165063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60196498694481654321553417 45147374020861240741165063)
            ·
              refine ⟨67721061031291861111747595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45147374020861240741165063 67721061031291861111747595)
              ·
                refine ⟨101581591546937791667621393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67721061031291861111747595 101581591546937791667621393)
                ·
                  refine ⟨76186193660203343750716045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101581591546937791667621393 76186193660203343750716045)
                  ·
                    refine ⟨28569822622576253906518517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76186193660203343750716045 28569822622576253906518517)
                    ·
                      refine ⟨2678420870866523803736111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28569822622576253906518517 2678420870866523803736111)
                      ·
                        rfl

theorem cell23_5216206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_5216206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216206 prefixEnd_5216206 := by exact prefixLift 5216206
  have htrace : WordTrace (prefixWord ++ tailWord_5216206) baseStart_5216206 baseEnd_5216206 := by
    simpa [prefixWord, tailWord_5216206, baseEnd_5216206] using wordTrace_append hprefix tailTrace_5216206
  have hstable : (prefixWord ++ tailWord_5216206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216206).length < 2 ^ (prefixWord ++ tailWord_5216206).sum := by decide
  have hdescent : baseEnd_5216206 < baseStart_5216206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216256 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 5, 5]
def baseStart_5216256 : Nat := 118140960795 + 5216256 * 2 ^ 59
def prefixEnd_5216256 : Nat := 4983230072969 + 3 ^ 40 * 5216256 * 2
def baseEnd_5216256 : Nat := 892815514966416202703627

theorem tailTrace_5216256 : CollatzResearch.WordTrace tailWord_5216256 prefixEnd_5216256 892815514966416202703627 := by
  unfold tailWord_5216256
  simp only [CollatzResearch.WordTrace]
  refine ⟨95126243095201426222238311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126834990793601901629651081 95126243095201426222238311)
  ·
    refine ⟨142689364642802139333357467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95126243095201426222238311 142689364642802139333357467)
    ·
      refine ⟨214034046964203209000036201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142689364642802139333357467 214034046964203209000036201)
      ·
        refine ⟨160525535223152406750027151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214034046964203209000036201 160525535223152406750027151)
        ·
          refine ⟨240788302834728610125040727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160525535223152406750027151 240788302834728610125040727)
          ·
            refine ⟨361182454252092915187561091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240788302834728610125040727 361182454252092915187561091)
            ·
              refine ⟨541773681378139372781341637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361182454252092915187561091 541773681378139372781341637)
              ·
                refine ⟨101582565258401132396501557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541773681378139372781341637 101582565258401132396501557)
                ·
                  refine ⟨9523365492975106162172021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101582565258401132396501557 9523365492975106162172021)
                  ·
                    refine ⟨892815514966416202703627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9523365492975106162172021 892815514966416202703627)
                    ·
                      rfl

theorem cell23_5216256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_5216256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216256 prefixEnd_5216256 := by exact prefixLift 5216256
  have htrace : WordTrace (prefixWord ++ tailWord_5216256) baseStart_5216256 baseEnd_5216256 := by
    simpa [prefixWord, tailWord_5216256, baseEnd_5216256] using wordTrace_append hprefix tailTrace_5216256
  have hstable : (prefixWord ++ tailWord_5216256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216256).length < 2 ^ (prefixWord ++ tailWord_5216256).sum := by decide
  have hdescent : baseEnd_5216256 < baseStart_5216256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216260 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 8]
def baseStart_5216260 : Nat := 118140960795 + 5216260 * 2 ^ 59
def prefixEnd_5216260 : Nat := 4983230072969 + 3 ^ 40 * 5216260 * 2
def baseEnd_5216260 : Nat := 297605399869096288051207

theorem tailTrace_5216260 : CollatzResearch.WordTrace tailWord_5216260 prefixEnd_5216260 297605399869096288051207 := by
  unfold tailWord_5216260
  simp only [CollatzResearch.WordTrace]
  refine ⟨95126316041194180563811117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126835088054925574085081489 95126316041194180563811117)
  ·
    refine ⟨35672368515447817711429169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95126316041194180563811117 35672368515447817711429169)
    ·
      refine ⟨26754276386585863283571877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35672368515447817711429169 26754276386585863283571877)
      ·
        refine ⟨5016426822484849365669727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26754276386585863283571877 5016426822484849365669727)
        ·
          refine ⟨7524640233727274048504591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016426822484849365669727 7524640233727274048504591)
          ·
            refine ⟨11286960350590911072756887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524640233727274048504591 11286960350590911072756887)
            ·
              refine ⟨16930440525886366609135331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11286960350590911072756887 16930440525886366609135331)
              ·
                refine ⟨25395660788829549913702997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16930440525886366609135331 25395660788829549913702997)
                ·
                  refine ⟨297605399869096288051207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25395660788829549913702997 297605399869096288051207)
                  ·
                    rfl

theorem cell23_5216260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_5216260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216260 prefixEnd_5216260 := by exact prefixLift 5216260
  have htrace : WordTrace (prefixWord ++ tailWord_5216260) baseStart_5216260 baseEnd_5216260 := by
    simpa [prefixWord, tailWord_5216260, baseEnd_5216260] using wordTrace_append hprefix tailTrace_5216260
  have hstable : (prefixWord ++ tailWord_5216260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216260).length < 2 ^ (prefixWord ++ tailWord_5216260).sum := by decide
  have hdescent : baseEnd_5216260 < baseStart_5216260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216290 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_5216290 : Nat := 118140960795 + 5216290 * 2 ^ 59
def prefixEnd_5216290 : Nat := 4983230072969 + 3 ^ 40 * 5216290 * 2
def baseEnd_5216290 : Nat := 892821334413833825028575

theorem tailTrace_5216290 : CollatzResearch.WordTrace tailWord_5216290 prefixEnd_5216290 892821334413833825028575 := by
  unfold tailWord_5216290
  simp only [CollatzResearch.WordTrace]
  refine ⟨47563431568069919062803581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126835817514853117500809549 47563431568069919062803581)
  ·
    refine ⟨17836286838026219648551343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47563431568069919062803581 17836286838026219648551343)
    ·
      refine ⟨26754430257039329472827015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17836286838026219648551343 26754430257039329472827015)
      ·
        refine ⟨40131645385558994209240523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26754430257039329472827015 40131645385558994209240523)
        ·
          refine ⟨60197468078338491313860785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40131645385558994209240523 60197468078338491313860785)
          ·
            refine ⟨45148101058753868485395589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60197468078338491313860785 45148101058753868485395589)
            ·
              refine ⟨8465268948516350341011673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45148101058753868485395589 8465268948516350341011673)
              ·
                refine ⟨6348951711387262755758755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8465268948516350341011673 6348951711387262755758755)
                ·
                  refine ⟨9523427567080894133638133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6348951711387262755758755 9523427567080894133638133)
                  ·
                    refine ⟨892821334413833825028575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9523427567080894133638133 892821334413833825028575)
                    ·
                      rfl

theorem cell23_5216290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_5216290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216290 prefixEnd_5216290 := by exact prefixLift 5216290
  have htrace : WordTrace (prefixWord ++ tailWord_5216290) baseStart_5216290 baseEnd_5216290 := by
    simpa [prefixWord, tailWord_5216290, baseEnd_5216290] using wordTrace_append hprefix tailTrace_5216290
  have hstable : (prefixWord ++ tailWord_5216290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216290).length < 2 ^ (prefixWord ++ tailWord_5216290).sum := by decide
  have hdescent : baseEnd_5216290 < baseStart_5216290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216304 : List Nat := [2, 1, 1, 1, 2, 7, 1, 3, 1, 1, 3]
def baseStart_5216304 : Nat := 118140960795 + 5216304 * 2 ^ 59
def prefixEnd_5216304 : Nat := 4983230072969 + 3 ^ 40 * 5216304 * 2
def baseEnd_5216304 : Nat := 2678471191970664420310661

theorem tailTrace_5216304 : CollatzResearch.WordTrace tailWord_5216304 prefixEnd_5216304 2678471191970664420310661 := by
  unfold tailWord_5216304
  simp only [CollatzResearch.WordTrace]
  refine ⟨95127118447114478321111983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126836157929485971094815977 95127118447114478321111983)
  ·
    refine ⟨142690677670671717481667975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95127118447114478321111983 142690677670671717481667975)
    ·
      refine ⟨214036016506007576222501963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142690677670671717481667975 214036016506007576222501963)
      ·
        refine ⟨321054024759011364333752945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214036016506007576222501963 321054024759011364333752945)
        ·
          refine ⟨240790518569258523250314709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321054024759011364333752945 240790518569258523250314709)
          ·
            refine ⟨5643527778966996638679251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 240790518569258523250314709 5643527778966996638679251)
            ·
              refine ⟨8465291668450494958018877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643527778966996638679251 8465291668450494958018877)
              ·
                refine ⟨3174484375668935609257079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8465291668450494958018877 3174484375668935609257079)
                ·
                  refine ⟨4761726563503403413885619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174484375668935609257079 4761726563503403413885619)
                  ·
                    refine ⟨7142589845255105120828429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761726563503403413885619 7142589845255105120828429)
                    ·
                      refine ⟨2678471191970664420310661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142589845255105120828429 2678471191970664420310661)
                      ·
                        rfl

theorem cell23_5216304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 1, 3].length) (baseStart_5216304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216304 prefixEnd_5216304 := by exact prefixLift 5216304
  have htrace : WordTrace (prefixWord ++ tailWord_5216304) baseStart_5216304 baseEnd_5216304 := by
    simpa [prefixWord, tailWord_5216304, baseEnd_5216304] using wordTrace_append hprefix tailTrace_5216304
  have hstable : (prefixWord ++ tailWord_5216304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216304).length < 2 ^ (prefixWord ++ tailWord_5216304).sum := by decide
  have hdescent : baseEnd_5216304 < baseStart_5216304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216321 : List Nat := [1, 2, 5, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5216321 : Nat := 118140960795 + 5216321 * 2 ^ 59
def prefixEnd_5216321 : Nat := 4983230072969 + 3 ^ 40 * 5216321 * 2
def baseEnd_5216321 : Nat := 2678479921141790853798083

theorem tailTrace_5216321 : CollatzResearch.WordTrace tailWord_5216321 prefixEnd_5216321 2678479921141790853798083 := by
  unfold tailWord_5216321
  simp only [CollatzResearch.WordTrace]
  refine ⟨190254856935167368545592817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126836571290111579030395211 190254856935167368545592817)
  ·
    refine ⟨142691142701375526409194613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190254856935167368545592817 142691142701375526409194613)
    ·
      refine ⟨13377294628253955600861995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142691142701375526409194613 13377294628253955600861995)
      ·
        refine ⟨20065941942380933401292993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13377294628253955600861995 20065941942380933401292993)
        ·
          refine ⟨15049456456785700050969745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20065941942380933401292993 15049456456785700050969745)
          ·
            refine ⟨11287092342589275038227309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15049456456785700050969745 11287092342589275038227309)
            ·
              refine ⟨4232659628470978139335241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11287092342589275038227309 4232659628470978139335241)
              ·
                refine ⟨3174494721353233604501431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4232659628470978139335241 3174494721353233604501431)
                ·
                  refine ⟨4761742082029850406752147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174494721353233604501431 4761742082029850406752147)
                  ·
                    refine ⟨7142613123044775610128221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761742082029850406752147 7142613123044775610128221)
                    ·
                      refine ⟨2678479921141790853798083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142613123044775610128221 2678479921141790853798083)
                      ·
                        rfl

theorem cell23_5216321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5216321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216321 prefixEnd_5216321 := by exact prefixLift 5216321
  have htrace : WordTrace (prefixWord ++ tailWord_5216321) baseStart_5216321 baseEnd_5216321 := by
    simpa [prefixWord, tailWord_5216321, baseEnd_5216321] using wordTrace_append hprefix tailTrace_5216321
  have hstable : (prefixWord ++ tailWord_5216321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216321).length < 2 ^ (prefixWord ++ tailWord_5216321).sum := by decide
  have hdescent : baseEnd_5216321 < baseStart_5216321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216377 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 3]
def baseStart_5216377 : Nat := 118140960795 + 5216377 * 2 ^ 59
def prefixEnd_5216377 : Nat := 4983230072969 + 3 ^ 40 * 5216377 * 2
def baseEnd_5216377 : Nat := 2678508676058442634697825

theorem tailTrace_5216377 : CollatzResearch.WordTrace tailWord_5216377 prefixEnd_5216377 2678508676058442634697825 := by
  unfold tailWord_5216377
  simp only [CollatzResearch.WordTrace]
  refine ⟨190256899422964490109631385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126837932948642993406420923 190256899422964490109631385)
  ·
    refine ⟨142692674567223367582223539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190256899422964490109631385 142692674567223367582223539)
    ·
      refine ⟨214039011850835051373335309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142692674567223367582223539 214039011850835051373335309)
      ·
        refine ⟨80264629444063144265000741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214039011850835051373335309 80264629444063144265000741)
        ·
          refine ⟨15049618020761839549687639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80264629444063144265000741 15049618020761839549687639)
          ·
            refine ⟨22574427031142759324531459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15049618020761839549687639 22574427031142759324531459)
            ·
              refine ⟨33861640546714138986797189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22574427031142759324531459 33861640546714138986797189)
              ·
                refine ⟨6349057602508901060024473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33861640546714138986797189 6349057602508901060024473)
                ·
                  refine ⟨4761793201881675795018355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6349057602508901060024473 4761793201881675795018355)
                  ·
                    refine ⟨7142689802822513692527533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761793201881675795018355 7142689802822513692527533)
                    ·
                      refine ⟨2678508676058442634697825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142689802822513692527533 2678508676058442634697825)
                      ·
                        rfl

theorem cell23_5216377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_5216377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216377 prefixEnd_5216377 := by exact prefixLift 5216377
  have htrace : WordTrace (prefixWord ++ tailWord_5216377) baseStart_5216377 baseEnd_5216377 := by
    simpa [prefixWord, tailWord_5216377, baseEnd_5216377] using wordTrace_append hprefix tailTrace_5216377
  have hstable : (prefixWord ++ tailWord_5216377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216377).length < 2 ^ (prefixWord ++ tailWord_5216377).sum := by decide
  have hdescent : baseEnd_5216377 < baseStart_5216377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216393 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 2, 6]
def baseStart_5216393 : Nat := 118140960795 + 5216393 * 2 ^ 59
def prefixEnd_5216393 : Nat := 4983230072969 + 3 ^ 40 * 5216393 * 2
def baseEnd_5216393 : Nat := 892838963916304857365917

theorem tailTrace_5216393 : CollatzResearch.WordTrace tailWord_5216393 prefixEnd_5216393 892838963916304857365917 := by
  unfold tailWord_5216393
  simp only [CollatzResearch.WordTrace]
  refine ⟨190257482990906524842213833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126838321993937683228142555 190257482990906524842213833)
  ·
    refine ⟨142693112243179893631660375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190257482990906524842213833 142693112243179893631660375)
    ·
      refine ⟨214039668364769840447490563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142693112243179893631660375 214039668364769840447490563)
      ·
        refine ⟨321059502547154760671235845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214039668364769840447490563 321059502547154760671235845)
        ·
          refine ⟨60198656727591517625856721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 321059502547154760671235845 60198656727591517625856721)
          ·
            refine ⟨45148992545693638219392541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60198656727591517625856721 45148992545693638219392541)
            ·
              refine ⟨16930872204635114332272203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45148992545693638219392541 16930872204635114332272203)
              ·
                refine ⟨25396308306952671498408305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16930872204635114332272203 25396308306952671498408305)
                ·
                  refine ⟨19047231230214503623806229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25396308306952671498408305 19047231230214503623806229)
                  ·
                    refine ⟨892838963916304857365917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19047231230214503623806229 892838963916304857365917)
                    ·
                      rfl

theorem cell23_5216393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_5216393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216393 prefixEnd_5216393 := by exact prefixLift 5216393
  have htrace : WordTrace (prefixWord ++ tailWord_5216393) baseStart_5216393 baseEnd_5216393 := by
    simpa [prefixWord, tailWord_5216393, baseEnd_5216393] using wordTrace_append hprefix tailTrace_5216393
  have hstable : (prefixWord ++ tailWord_5216393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216393).length < 2 ^ (prefixWord ++ tailWord_5216393).sum := by decide
  have hdescent : baseEnd_5216393 < baseStart_5216393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216403 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 3]
def baseStart_5216403 : Nat := 118140960795 + 5216403 * 2 ^ 59
def prefixEnd_5216403 : Nat := 4983230072969 + 3 ^ 40 * 5216403 * 2
def baseEnd_5216403 : Nat := 2678522026555459532972705

theorem tailTrace_5216403 : CollatzResearch.WordTrace tailWord_5216403 prefixEnd_5216403 2678522026555459532972705 := by
  unfold tailWord_5216403
  simp only [CollatzResearch.WordTrace]
  refine ⟨190257847720870296550077863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126838565147246864366718575 190257847720870296550077863)
  ·
    refine ⟨285386771581305444825116795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190257847720870296550077863 285386771581305444825116795)
    ·
      refine ⟨428080157371958167237675193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285386771581305444825116795 428080157371958167237675193)
      ·
        refine ⟨321060118028968625428256395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428080157371958167237675193 321060118028968625428256395)
        ·
          refine ⟨481590177043452938142384593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321060118028968625428256395 481590177043452938142384593)
          ·
            refine ⟨361192632782589703606788445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481590177043452938142384593 361192632782589703606788445)
            ·
              refine ⟨135447237293471138852545667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361192632782589703606788445 135447237293471138852545667)
              ·
                refine ⟨203170855940206708278818501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135447237293471138852545667 203170855940206708278818501)
                ·
                  refine ⟨38094535488788757802278469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203170855940206708278818501 38094535488788757802278469)
                  ·
                    refine ⟨7142725404147892087927213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38094535488788757802278469 7142725404147892087927213)
                    ·
                      refine ⟨2678522026555459532972705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142725404147892087927213 2678522026555459532972705)
                      ·
                        rfl

theorem cell23_5216403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_5216403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216403 prefixEnd_5216403 := by exact prefixLift 5216403
  have htrace : WordTrace (prefixWord ++ tailWord_5216403) baseStart_5216403 baseEnd_5216403 := by
    simpa [prefixWord, tailWord_5216403, baseEnd_5216403] using wordTrace_append hprefix tailTrace_5216403
  have hstable : (prefixWord ++ tailWord_5216403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216403).length < 2 ^ (prefixWord ++ tailWord_5216403).sum := by decide
  have hdescent : baseEnd_5216403 < baseStart_5216403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216417 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5216417 : Nat := 118140960795 + 5216417 * 2 ^ 59
def prefixEnd_5216417 : Nat := 4983230072969 + 3 ^ 40 * 5216417 * 2
def baseEnd_5216417 : Nat := 2678529215284622478197641

theorem tailTrace_5216417 : CollatzResearch.WordTrace tailWord_5216417 prefixEnd_5216417 2678529215284622478197641 := by
  unfold tailWord_5216417
  simp only [CollatzResearch.WordTrace]
  refine ⟨190258358342819576941087505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126838905561879717960725003 190258358342819576941087505)
  ·
    refine ⟨142693768757114682705815629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190258358342819576941087505 142693768757114682705815629)
    ·
      refine ⟨53510163283918006014680861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142693768757114682705815629 53510163283918006014680861)
      ·
        refine ⟨20066311231469252255505323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53510163283918006014680861 20066311231469252255505323)
        ·
          refine ⟨30099466847203878383257985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20066311231469252255505323 30099466847203878383257985)
          ·
            refine ⟨22574600135402908787443489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30099466847203878383257985 22574600135402908787443489)
            ·
              refine ⟨16930950101552181590582617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22574600135402908787443489 16930950101552181590582617)
              ·
                refine ⟨12698212576164136192936963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16930950101552181590582617 12698212576164136192936963)
                ·
                  refine ⟨19047318864246204289405445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12698212576164136192936963 19047318864246204289405445)
                  ·
                    refine ⟨3571372287046163304263521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19047318864246204289405445 3571372287046163304263521)
                    ·
                      refine ⟨2678529215284622478197641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571372287046163304263521 2678529215284622478197641)
                      ·
                        rfl

theorem cell23_5216417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5216417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216417 prefixEnd_5216417 := by exact prefixLift 5216417
  have htrace : WordTrace (prefixWord ++ tailWord_5216417) baseStart_5216417 baseEnd_5216417 := by
    simpa [prefixWord, tailWord_5216417, baseEnd_5216417] using wordTrace_append hprefix tailTrace_5216417
  have hstable : (prefixWord ++ tailWord_5216417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216417).length < 2 ^ (prefixWord ++ tailWord_5216417).sum := by decide
  have hdescent : baseEnd_5216417 < baseStart_5216417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216440 : List Nat := [2, 1, 2, 1, 2, 1, 3, 6, 5]
def baseStart_5216440 : Nat := 118140960795 + 5216440 * 2 ^ 59
def prefixEnd_5216440 : Nat := 4983230072969 + 3 ^ 40 * 5216440 * 2
def baseEnd_5216440 : Nat := 297615669482186209801115

theorem tailTrace_5216440 : CollatzResearch.WordTrace tailWord_5216440 prefixEnd_5216440 297615669482186209801115 := by
  unfold tailWord_5216440
  simp only [CollatzResearch.WordTrace]
  refine ⟨95129598610868125934587387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126839464814490834579449849 95129598610868125934587387)
  ·
    refine ⟨142694397916302188901881081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95129598610868125934587387 142694397916302188901881081)
    ·
      refine ⟨107020798437226641676410811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142694397916302188901881081 107020798437226641676410811)
      ·
        refine ⟨160531197655839962514616217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107020798437226641676410811 160531197655839962514616217)
        ·
          refine ⟨120398398241879971885962163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160531197655839962514616217 120398398241879971885962163)
          ·
            refine ⟨180597597362819957828943245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120398398241879971885962163 180597597362819957828943245)
            ·
              refine ⟨67724099011057484185853717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180597597362819957828943245 67724099011057484185853717)
              ·
                refine ⟨3174567141143319571211893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67724099011057484185853717 3174567141143319571211893)
                ·
                  refine ⟨297615669482186209801115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3174567141143319571211893 297615669482186209801115)
                  ·
                    rfl

theorem cell23_5216440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 5].length) (baseStart_5216440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216440 prefixEnd_5216440 := by exact prefixLift 5216440
  have htrace : WordTrace (prefixWord ++ tailWord_5216440) baseStart_5216440 baseEnd_5216440 := by
    simpa [prefixWord, tailWord_5216440, baseEnd_5216440] using wordTrace_append hprefix tailTrace_5216440
  have hstable : (prefixWord ++ tailWord_5216440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216440).length < 2 ^ (prefixWord ++ tailWord_5216440).sum := by decide
  have hdescent : baseEnd_5216440 < baseStart_5216440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216453 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_5216453 : Nat := 118140960795 + 5216453 * 2 ^ 59
def prefixEnd_5216453 : Nat := 4983230072969 + 3 ^ 40 * 5216453 * 2
def baseEnd_5216453 : Nat := 892849233529394779115825

theorem tailTrace_5216453 : CollatzResearch.WordTrace tailWord_5216453 prefixEnd_5216453 892849233529394779115825 := by
  unfold tailWord_5216453
  simp only [CollatzResearch.WordTrace]
  refine ⟨190259671370689155089398013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126839780913792770059598675 190259671370689155089398013)
  ·
    refine ⟨71347376764008433158524255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190259671370689155089398013 71347376764008433158524255)
    ·
      refine ⟨107021065146012649737786383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71347376764008433158524255 107021065146012649737786383)
      ·
        refine ⟨160531597719018974606679575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107021065146012649737786383 160531597719018974606679575)
        ·
          refine ⟨240797396578528461910019363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160531597719018974606679575 240797396578528461910019363)
          ·
            refine ⟨361196094867792692865029045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240797396578528461910019363 361196094867792692865029045)
            ·
              refine ⟨33862133893855564956096473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 361196094867792692865029045 33862133893855564956096473)
              ·
                refine ⟨25396600420391673717072355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33862133893855564956096473 25396600420391673717072355)
                ·
                  refine ⟨38094900630587510575608533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25396600420391673717072355 38094900630587510575608533)
                  ·
                    refine ⟨892849233529394779115825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38094900630587510575608533 892849233529394779115825)
                    ·
                      rfl

theorem cell23_5216453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_5216453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216453 prefixEnd_5216453 := by exact prefixLift 5216453
  have htrace : WordTrace (prefixWord ++ tailWord_5216453) baseStart_5216453 baseEnd_5216453 := by
    simpa [prefixWord, tailWord_5216453, baseEnd_5216453] using wordTrace_append hprefix tailTrace_5216453
  have hstable : (prefixWord ++ tailWord_5216453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216453).length < 2 ^ (prefixWord ++ tailWord_5216453).sum := by decide
  have hdescent : baseEnd_5216453 < baseStart_5216453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216487 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 2, 5]
def baseStart_5216487 : Nat := 118140960795 + 5216487 * 2 ^ 59
def prefixEnd_5216487 : Nat := 4983230072969 + 3 ^ 40 * 5216487 * 2
def baseEnd_5216487 : Nat := 892855052976812401440773

theorem tailTrace_5216487 : CollatzResearch.WordTrace tailWord_5216487 prefixEnd_5216487 892855052976812401440773 := by
  unfold tailWord_5216487
  simp only [CollatzResearch.WordTrace]
  refine ⟨190260911452565978896135715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126840607635043985930757143 190260911452565978896135715)
  ·
    refine ⟨285391367178848968344203573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190260911452565978896135715 285391367178848968344203573)
    ·
      refine ⟨26755440673017090782269085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285391367178848968344203573 26755440673017090782269085)
      ·
        refine ⟨10033290252381409043350907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26755440673017090782269085 10033290252381409043350907)
        ·
          refine ⟨15049935378572113565026361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10033290252381409043350907 15049935378572113565026361)
          ·
            refine ⟨11287451533929085173769771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15049935378572113565026361 11287451533929085173769771)
            ·
              refine ⟨16931177300893627760654657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11287451533929085173769771 16931177300893627760654657)
              ·
                refine ⟨12698382975670220820490993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16931177300893627760654657 12698382975670220820490993)
                ·
                  refine ⟨9523787231752665615368245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12698382975670220820490993 9523787231752665615368245)
                  ·
                    refine ⟨892855052976812401440773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9523787231752665615368245 892855052976812401440773)
                    ·
                      rfl

theorem cell23_5216487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_5216487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216487 prefixEnd_5216487 := by exact prefixLift 5216487
  have htrace : WordTrace (prefixWord ++ tailWord_5216487) baseStart_5216487 baseEnd_5216487 := by
    simpa [prefixWord, tailWord_5216487, baseEnd_5216487] using wordTrace_append hprefix tailTrace_5216487
  have hstable : (prefixWord ++ tailWord_5216487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216487).length < 2 ^ (prefixWord ++ tailWord_5216487).sum := by decide
  have hdescent : baseEnd_5216487 < baseStart_5216487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216567 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 4, 3, 2]
def baseStart_5216567 : Nat := 118140960795 + 5216567 * 2 ^ 59
def prefixEnd_5216567 : Nat := 4983230072969 + 3 ^ 40 * 5216567 * 2
def baseEnd_5216567 : Nat := 2678606237382796891321951

theorem tailTrace_5216567 : CollatzResearch.WordTrace tailWord_5216567 prefixEnd_5216567 2678606237382796891321951 := by
  unfold tailWord_5216567
  simp only [CollatzResearch.WordTrace]
  refine ⟨190263829292276152559047955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126842552861517435039365303 190263829292276152559047955)
  ·
    refine ⟨285395743938414228838571933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190263829292276152559047955 285395743938414228838571933)
    ·
      refine ⟨107023403976905335814464475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285395743938414228838571933 107023403976905335814464475)
      ·
        refine ⟨160535105965358003721696713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107023403976905335814464475 160535105965358003721696713)
        ·
          refine ⟨120401329474018502791272535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160535105965358003721696713 120401329474018502791272535)
          ·
            refine ⟨180601994211027754186908803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120401329474018502791272535 180601994211027754186908803)
            ·
              refine ⟨270902991316541631280363205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180601994211027754186908803 270902991316541631280363205)
              ·
                refine ⟨50794310871851555865068101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270902991316541631280363205 50794310871851555865068101)
                ·
                  refine ⟨9523933288472166724700269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50794310871851555865068101 9523933288472166724700269)
                  ·
                    refine ⟨3571474983177062521762601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9523933288472166724700269 3571474983177062521762601)
                    ·
                      refine ⟨2678606237382796891321951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571474983177062521762601 2678606237382796891321951)
                      ·
                        rfl

theorem cell23_5216567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_5216567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216567 prefixEnd_5216567 := by exact prefixLift 5216567
  have htrace : WordTrace (prefixWord ++ tailWord_5216567) baseStart_5216567 baseEnd_5216567 := by
    simpa [prefixWord, tailWord_5216567, baseEnd_5216567] using wordTrace_append hprefix tailTrace_5216567
  have hstable : (prefixWord ++ tailWord_5216567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216567).length < 2 ^ (prefixWord ++ tailWord_5216567).sum := by decide
  have hdescent : baseEnd_5216567 < baseStart_5216567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216574 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_5216574 : Nat := 118140960795 + 5216574 * 2 ^ 59
def prefixEnd_5216574 : Nat := 4983230072969 + 3 ^ 40 * 5216574 * 2
def baseEnd_5216574 : Nat := 2678609831747378363934419

theorem tailTrace_5216574 : CollatzResearch.WordTrace tailWord_5216574 prefixEnd_5216574 2678609831747378363934419 := by
  unfold tailWord_5216574
  simp only [CollatzResearch.WordTrace]
  refine ⟨23783010575406349094319097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126842723068833861836368517 23783010575406349094319097)
  ·
    refine ⟨17837257931554761820739323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23783010575406349094319097 17837257931554761820739323)
    ·
      refine ⟨26755886897332142731108985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17837257931554761820739323 26755886897332142731108985)
      ·
        refine ⟨20066915172999107048331739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26755886897332142731108985 20066915172999107048331739)
        ·
          refine ⟨30100372759498660572497609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20066915172999107048331739 30100372759498660572497609)
          ·
            refine ⟨22575279569623995429373207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30100372759498660572497609 22575279569623995429373207)
            ·
              refine ⟨33862919354435993144059811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22575279569623995429373207 33862919354435993144059811)
              ·
                refine ⟨50794379031653989716089717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33862919354435993144059811 50794379031653989716089717)
                ·
                  refine ⟨4761973034217561535883411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50794379031653989716089717 4761973034217561535883411)
                  ·
                    refine ⟨7142959551326342303825117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761973034217561535883411 7142959551326342303825117)
                    ·
                      refine ⟨2678609831747378363934419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7142959551326342303825117 2678609831747378363934419)
                      ·
                        rfl

theorem cell23_5216574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_5216574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216574 prefixEnd_5216574 := by exact prefixLift 5216574
  have htrace : WordTrace (prefixWord ++ tailWord_5216574) baseStart_5216574 baseEnd_5216574 := by
    simpa [prefixWord, tailWord_5216574, baseEnd_5216574] using wordTrace_append hprefix tailTrace_5216574
  have hstable : (prefixWord ++ tailWord_5216574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216574).length < 2 ^ (prefixWord ++ tailWord_5216574).sum := by decide
  have hdescent : baseEnd_5216574 < baseStart_5216574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216584 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_5216584 : Nat := 118140960795 + 5216584 * 2 ^ 59
def prefixEnd_5216584 : Nat := 4983230072969 + 3 ^ 40 * 5216584 * 2
def baseEnd_5216584 : Nat := 2678614966553923324809373

theorem tailTrace_5216584 : CollatzResearch.WordTrace tailWord_5216584 prefixEnd_5216584 2678614966553923324809373 := by
  unfold tailWord_5216584
  simp only [CollatzResearch.WordTrace]
  refine ⟨95132224666607282231208403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126842966222143042974944537 95132224666607282231208403)
  ·
    refine ⟨142698336999910923346812605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95132224666607282231208403 142698336999910923346812605)
    ·
      refine ⟨53511876374966596255054727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142698336999910923346812605 53511876374966596255054727)
      ·
        refine ⟨80267814562449894382582091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53511876374966596255054727 80267814562449894382582091)
        ·
          refine ⟨120401721843674841573873137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80267814562449894382582091 120401721843674841573873137)
          ·
            refine ⟨90301291382756131180404853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120401721843674841573873137 90301291382756131180404853)
            ·
              refine ⟨8465746067133387298162955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90301291382756131180404853 8465746067133387298162955)
              ·
                refine ⟨12698619100700080947244433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8465746067133387298162955 12698619100700080947244433)
                ·
                  refine ⟨9523964325525060710433325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12698619100700080947244433 9523964325525060710433325)
                  ·
                    refine ⟨3571486622071897766412497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9523964325525060710433325 3571486622071897766412497)
                    ·
                      refine ⟨2678614966553923324809373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571486622071897766412497 2678614966553923324809373)
                      ·
                        rfl

theorem cell23_5216584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_5216584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216584 prefixEnd_5216584 := by exact prefixLift 5216584
  have htrace : WordTrace (prefixWord ++ tailWord_5216584) baseStart_5216584 baseEnd_5216584 := by
    simpa [prefixWord, tailWord_5216584, baseEnd_5216584] using wordTrace_append hprefix tailTrace_5216584
  have hstable : (prefixWord ++ tailWord_5216584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216584).length < 2 ^ (prefixWord ++ tailWord_5216584).sum := by decide
  have hdescent : baseEnd_5216584 < baseStart_5216584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216590 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_5216590 : Nat := 118140960795 + 5216590 * 2 ^ 59
def prefixEnd_5216590 : Nat := 4983230072969 + 3 ^ 40 * 5216590 * 2
def baseEnd_5216590 : Nat := 892872682479283433778115

theorem tailTrace_5216590 : CollatzResearch.WordTrace tailWord_5216590 prefixEnd_5216590 892872682479283433778115 := by
  unfold tailWord_5216590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23783083521399103435891903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126843112114128551658090149 23783083521399103435891903)
  ·
    refine ⟨35674625282098655153837855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23783083521399103435891903 35674625282098655153837855)
    ·
      refine ⟨53511937923147982730756783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35674625282098655153837855 53511937923147982730756783)
      ·
        refine ⟨80267906884721974096135175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53511937923147982730756783 80267906884721974096135175)
        ·
          refine ⟨120401860327082961144202763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80267906884721974096135175 120401860327082961144202763)
          ·
            refine ⟨180602790490624441716304145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120401860327082961144202763 180602790490624441716304145)
            ·
              refine ⟨135452092867968331287228109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180602790490624441716304145 135452092867968331287228109)
              ·
                refine ⟨50794534825488124232710541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135452092867968331287228109 50794534825488124232710541)
                ·
                  refine ⟨19047950559558046587266453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50794534825488124232710541 19047950559558046587266453)
                  ·
                    refine ⟨892872682479283433778115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19047950559558046587266453 892872682479283433778115)
                    ·
                      rfl

theorem cell23_5216590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_5216590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216590 prefixEnd_5216590 := by exact prefixLift 5216590
  have htrace : WordTrace (prefixWord ++ tailWord_5216590) baseStart_5216590 baseEnd_5216590 := by
    simpa [prefixWord, tailWord_5216590, baseEnd_5216590] using wordTrace_append hprefix tailTrace_5216590
  have hstable : (prefixWord ++ tailWord_5216590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216590).length < 2 ^ (prefixWord ++ tailWord_5216590).sum := by decide
  have hdescent : baseEnd_5216590 < baseStart_5216590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216594 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_5216594 : Nat := 118140960795 + 5216594 * 2 ^ 59
def prefixEnd_5216594 : Nat := 4983230072969 + 3 ^ 40 * 5216594 * 2
def baseEnd_5216594 : Nat := 892873367120156095228109

theorem tailTrace_5216594 : CollatzResearch.WordTrace tailWord_5216594 prefixEnd_5216594 892873367120156095228109 := by
  unfold tailWord_5216594
  simp only [CollatzResearch.WordTrace]
  refine ⟨47566203515794584042570209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126843209375452224113520557 47566203515794584042570209)
  ·
    refine ⟨35674652636845938031927657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47566203515794584042570209 35674652636845938031927657)
    ·
      refine ⟨26755989477634453523945743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35674652636845938031927657 26755989477634453523945743)
      ·
        refine ⟨40133984216451680285918615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26755989477634453523945743 40133984216451680285918615)
        ·
          refine ⟨60200976324677520428877923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40133984216451680285918615 60200976324677520428877923)
          ·
            refine ⟨90301464487016280643316885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60200976324677520428877923 90301464487016280643316885)
            ·
              refine ⟨4232881147828888155155479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90301464487016280643316885 4232881147828888155155479)
              ·
                refine ⟨6349321721743332232733219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232881147828888155155479 6349321721743332232733219)
                ·
                  refine ⟨9523982582614998349099829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349321721743332232733219 9523982582614998349099829)
                  ·
                    refine ⟨892873367120156095228109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9523982582614998349099829 892873367120156095228109)
                    ·
                      rfl

theorem cell23_5216594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_5216594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216594 prefixEnd_5216594 := by exact prefixLift 5216594
  have htrace : WordTrace (prefixWord ++ tailWord_5216594) baseStart_5216594 baseEnd_5216594 := by
    simpa [prefixWord, tailWord_5216594, baseEnd_5216594] using wordTrace_append hprefix tailTrace_5216594
  have hstable : (prefixWord ++ tailWord_5216594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216594).length < 2 ^ (prefixWord ++ tailWord_5216594).sum := by decide
  have hdescent : baseEnd_5216594 < baseStart_5216594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216637 : List Nat := [1, 4, 1, 1, 2, 3, 4, 7]
def baseStart_5216637 : Nat := 118140960795 + 5216637 * 2 ^ 59
def prefixEnd_5216637 : Nat := 4983230072969 + 3 ^ 40 * 5216637 * 2
def baseEnd_5216637 : Nat := 99208969667726356201727

theorem tailTrace_5216637 : CollatzResearch.WordTrace tailWord_5216637 prefixEnd_5216637 99208969667726356201727 := by
  unfold tailWord_5216637
  simp only [CollatzResearch.WordTrace]
  refine ⟨190266382402022554514096165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126844254934681703009397443 190266382402022554514096165)
  ·
    refine ⟨35674946700379228971393031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190266382402022554514096165 35674946700379228971393031)
    ·
      refine ⟨53512420050568843457089547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35674946700379228971393031 53512420050568843457089547)
      ·
        refine ⟨80268630075853265185634321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53512420050568843457089547 80268630075853265185634321)
        ·
          refine ⟨60201472556889948889225741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80268630075853265185634321 60201472556889948889225741)
          ·
            refine ⟨22575552208833730833459653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60201472556889948889225741 22575552208833730833459653)
            ·
              refine ⟨4232916039156324531273685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22575552208833730833459653 4232916039156324531273685)
              ·
                refine ⟨99208969667726356201727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4232916039156324531273685 99208969667726356201727)
                ·
                  rfl

theorem cell23_5216637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 7].length) (baseStart_5216637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216637 prefixEnd_5216637 := by exact prefixLift 5216637
  have htrace : WordTrace (prefixWord ++ tailWord_5216637) baseStart_5216637 baseEnd_5216637 := by
    simpa [prefixWord, tailWord_5216637, baseEnd_5216637] using wordTrace_append hprefix tailTrace_5216637
  have hstable : (prefixWord ++ tailWord_5216637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216637).length < 2 ^ (prefixWord ++ tailWord_5216637).sum := by decide
  have hdescent : baseEnd_5216637 < baseStart_5216637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216642 : List Nat := [3, 4, 2, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5216642 : Nat := 118140960795 + 5216642 * 2 ^ 59
def prefixEnd_5216642 : Nat := 4983230072969 + 3 ^ 40 * 5216642 * 2
def baseEnd_5216642 : Nat := 2678644748431884097884107

theorem tailTrace_5216642 : CollatzResearch.WordTrace tailWord_5216642 prefixEnd_5216642 2678644748431884097884107 := by
  unfold tailWord_5216642
  simp only [CollatzResearch.WordTrace]
  refine ⟨47566641191751110092007045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126844376511336293578685453 47566641191751110092007045)
  ·
    refine ⟨8918745223453333142251321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47566641191751110092007045 8918745223453333142251321)
    ·
      refine ⟨6689058917589999856688491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8918745223453333142251321 6689058917589999856688491)
      ·
        refine ⟨10033588376384999785032737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6689058917589999856688491 10033588376384999785032737)
        ·
          refine ⟨7525191282288749838774553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10033588376384999785032737 7525191282288749838774553)
          ·
            refine ⟨5643893461716562379080915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7525191282288749838774553 5643893461716562379080915)
            ·
              refine ⟨8465840192574843568621373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643893461716562379080915 8465840192574843568621373)
              ·
                refine ⟨3174690072215566338233015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8465840192574843568621373 3174690072215566338233015)
                ·
                  refine ⟨4762035108323349507349523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174690072215566338233015 4762035108323349507349523)
                  ·
                    refine ⟨7143052662485024261024285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4762035108323349507349523 7143052662485024261024285)
                    ·
                      refine ⟨2678644748431884097884107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7143052662485024261024285 2678644748431884097884107)
                      ·
                        rfl

theorem cell23_5216642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5216642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216642 prefixEnd_5216642 := by exact prefixLift 5216642
  have htrace : WordTrace (prefixWord ++ tailWord_5216642) baseStart_5216642 baseEnd_5216642 := by
    simpa [prefixWord, tailWord_5216642, baseEnd_5216642] using wordTrace_append hprefix tailTrace_5216642
  have hstable : (prefixWord ++ tailWord_5216642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216642).length < 2 ^ (prefixWord ++ tailWord_5216642).sum := by decide
  have hdescent : baseEnd_5216642 < baseStart_5216642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216647 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_5216647 : Nat := 118140960795 + 5216647 * 2 ^ 59
def prefixEnd_5216647 : Nat := 4983230072969 + 3 ^ 40 * 5216647 * 2
def baseEnd_5216647 : Nat := 2678647315835156578321583

theorem tailTrace_5216647 : CollatzResearch.WordTrace tailWord_5216647 prefixEnd_5216647 2678647315835156578321583 := by
  unfold tailWord_5216647
  simp only [CollatzResearch.WordTrace]
  refine ⟨190266747131986326221960195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126844498087990884147973463 190266747131986326221960195)
  ·
    refine ⟨285400120697979489332940293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190266747131986326221960195 285400120697979489332940293)
    ·
      refine ⟨53512522630871154249926305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285400120697979489332940293 53512522630871154249926305)
      ·
        refine ⟨40134391973153365687444729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53512522630871154249926305 40134391973153365687444729)
        ·
          refine ⟨30100793979865024265583547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40134391973153365687444729 30100793979865024265583547)
          ·
            refine ⟨45151190969797536398375321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30100793979865024265583547 45151190969797536398375321)
            ·
              refine ⟨33863393227348152298781491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45151190969797536398375321 33863393227348152298781491)
              ·
                refine ⟨50795089841022228448172237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33863393227348152298781491 50795089841022228448172237)
                ·
                  refine ⟨19048158690383335668064589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50795089841022228448172237 19048158690383335668064589)
                  ·
                    refine ⟨7143059508893750875524221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19048158690383335668064589 7143059508893750875524221)
                    ·
                      refine ⟨2678647315835156578321583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7143059508893750875524221 2678647315835156578321583)
                      ·
                        rfl

theorem cell23_5216647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_5216647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216647 prefixEnd_5216647 := by exact prefixLift 5216647
  have htrace : WordTrace (prefixWord ++ tailWord_5216647) baseStart_5216647 baseEnd_5216647 := by
    simpa [prefixWord, tailWord_5216647, baseEnd_5216647] using wordTrace_append hprefix tailTrace_5216647
  have hstable : (prefixWord ++ tailWord_5216647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216647).length < 2 ^ (prefixWord ++ tailWord_5216647).sum := by decide
  have hdescent : baseEnd_5216647 < baseStart_5216647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216682 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5216682 : Nat := 118140960795 + 5216682 * 2 ^ 59
def prefixEnd_5216682 : Nat := 4983230072969 + 3 ^ 40 * 5216682 * 2
def baseEnd_5216682 : Nat := 2678665287658063941383923

theorem tailTrace_5216682 : CollatzResearch.WordTrace tailWord_5216682 prefixEnd_5216682 2678665287658063941383923 := by
  unfold tailWord_5216682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47567005921714881799871075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126845349124573018132989533 47567005921714881799871075)
  ·
    refine ⟨71350508882572322699806613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47567005921714881799871075 71350508882572322699806613)
    ·
      refine ⟨3344555103870577626553435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71350508882572322699806613 3344555103870577626553435)
      ·
        refine ⟨5016832655805866439830153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3344555103870577626553435 5016832655805866439830153)
        ·
          refine ⟨3762624491854399829872615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5016832655805866439830153 3762624491854399829872615)
          ·
            refine ⟨5643936737781599744808923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762624491854399829872615 5643936737781599744808923)
            ·
              refine ⟨8465905106672399617213385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643936737781599744808923 8465905106672399617213385)
              ·
                refine ⟨6349428830004299712910039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8465905106672399617213385 6349428830004299712910039)
                ·
                  refine ⟨9524143245006449569365059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349428830004299712910039 9524143245006449569365059)
                  ·
                    refine ⟨14286214867509674354047589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9524143245006449569365059 14286214867509674354047589)
                    ·
                      refine ⟨2678665287658063941383923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14286214867509674354047589 2678665287658063941383923)
                      ·
                        rfl

theorem cell23_5216682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5216682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216682 prefixEnd_5216682 := by exact prefixLift 5216682
  have htrace : WordTrace (prefixWord ++ tailWord_5216682) baseStart_5216682 baseEnd_5216682 := by
    simpa [prefixWord, tailWord_5216682, baseEnd_5216682] using wordTrace_append hprefix tailTrace_5216682
  have hstable : (prefixWord ++ tailWord_5216682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216682).length < 2 ^ (prefixWord ++ tailWord_5216682).sum := by decide
  have hdescent : baseEnd_5216682 < baseStart_5216682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216685 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5216685 : Nat := 118140960795 + 5216685 * 2 ^ 59
def prefixEnd_5216685 : Nat := 4983230072969 + 3 ^ 40 * 5216685 * 2
def baseEnd_5216685 : Nat := 2678666828100027429646409

theorem tailTrace_5216685 : CollatzResearch.WordTrace tailWord_5216685 prefixEnd_5216685 2678666828100027429646409 := by
  unfold tailWord_5216685
  simp only [CollatzResearch.WordTrace]
  refine ⟨190268133105848658711843509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126845422070565772474562339 190268133105848658711843509)
  ·
    refine ⟨17837637478673311754235329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190268133105848658711843509 17837637478673311754235329)
    ·
      refine ⟨13378228109004983815676497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17837637478673311754235329 13378228109004983815676497)
      ·
        refine ⟨10033671081753737861757373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13378228109004983815676497 10033671081753737861757373)
        ·
          refine ⟨3762626655657651698159015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10033671081753737861757373 3762626655657651698159015)
          ·
            refine ⟨5643939983486477547238523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762626655657651698159015 5643939983486477547238523)
            ·
              refine ⟨8465909975229716320857785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643939983486477547238523 8465909975229716320857785)
              ·
                refine ⟨6349432481422287240643339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8465909975229716320857785 6349432481422287240643339)
                ·
                  refine ⟨9524148722133430860965009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349432481422287240643339 9524148722133430860965009)
                  ·
                    refine ⟨7143111541600073145723757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9524148722133430860965009 7143111541600073145723757)
                    ·
                      refine ⟨2678666828100027429646409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7143111541600073145723757 2678666828100027429646409)
                      ·
                        rfl

theorem cell23_5216685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5216685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216685 prefixEnd_5216685 := by exact prefixLift 5216685
  have htrace : WordTrace (prefixWord ++ tailWord_5216685) baseStart_5216685 baseEnd_5216685 := by
    simpa [prefixWord, tailWord_5216685, baseEnd_5216685] using wordTrace_append hprefix tailTrace_5216685
  have hstable : (prefixWord ++ tailWord_5216685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216685).length < 2 ^ (prefixWord ++ tailWord_5216685).sum := by decide
  have hdescent : baseEnd_5216685 < baseStart_5216685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216724 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5216724 : Nat := 118140960795 + 5216724 * 2 ^ 59
def prefixEnd_5216724 : Nat := 4983230072969 + 3 ^ 40 * 5216724 * 2
def baseEnd_5216724 : Nat := 2678686853845552777058729

theorem tailTrace_5216724 : CollatzResearch.WordTrace tailWord_5216724 prefixEnd_5216724 2678686853845552777058729 := by
  unfold tailWord_5216724
  simp only [CollatzResearch.WordTrace]
  refine ⟨95134777776353684186256613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126846370368471578915008817 95134777776353684186256613)
  ·
    refine ⟨17837770833066315784923115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95134777776353684186256613 17837770833066315784923115)
    ·
      refine ⟨26756656249599473677384673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17837770833066315784923115 26756656249599473677384673)
      ·
        refine ⟨20067492187199605258038505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26756656249599473677384673 20067492187199605258038505)
        ·
          refine ⟨15050619140399703943528879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20067492187199605258038505 15050619140399703943528879)
          ·
            refine ⟨22575928710599555915293319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15050619140399703943528879 22575928710599555915293319)
            ·
              refine ⟨33863893065899333872939979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22575928710599555915293319 33863893065899333872939979)
              ·
                refine ⟨50795839598849000809409969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33863893065899333872939979 50795839598849000809409969)
                ·
                  refine ⟨38096879699136750607057477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50795839598849000809409969 38096879699136750607057477)
                  ·
                    refine ⟨7143164943588140738823277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38096879699136750607057477 7143164943588140738823277)
                    ·
                      refine ⟨2678686853845552777058729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7143164943588140738823277 2678686853845552777058729)
                      ·
                        rfl

theorem cell23_5216724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5216724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216724 prefixEnd_5216724 := by exact prefixLift 5216724
  have htrace : WordTrace (prefixWord ++ tailWord_5216724) baseStart_5216724 baseEnd_5216724 := by
    simpa [prefixWord, tailWord_5216724, baseEnd_5216724] using wordTrace_append hprefix tailTrace_5216724
  have hstable : (prefixWord ++ tailWord_5216724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216724).length < 2 ^ (prefixWord ++ tailWord_5216724).sum := by decide
  have hdescent : baseEnd_5216724 < baseStart_5216724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216817 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 8]
def baseStart_5216817 : Nat := 118140960795 + 5216817 * 2 ^ 59
def prefixEnd_5216817 : Nat := 4983230072969 + 3 ^ 40 * 5216817 * 2
def baseEnd_5216817 : Nat := 297637178616268990355089

theorem tailTrace_5216817 : CollatzResearch.WordTrace tailWord_5216817 prefixEnd_5216817 297637178616268990355089 := by
  unfold tailWord_5216817
  simp only [CollatzResearch.WordTrace]
  refine ⟨190272947541370445255648705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126848631694246963503765803 190272947541370445255648705)
  ·
    refine ⟨142704710656027833941736529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190272947541370445255648705 142704710656027833941736529)
    ·
      refine ⟨107028532992020875456302397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142704710656027833941736529 107028532992020875456302397)
      ·
        refine ⟨40135699872007828296113399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107028532992020875456302397 40135699872007828296113399)
        ·
          refine ⟨60203549808011742444170099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40135699872007828296113399 60203549808011742444170099)
          ·
            refine ⟨90305324712017613666255149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60203549808011742444170099 90305324712017613666255149)
            ·
              refine ⟨33864496767006605124845681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90305324712017613666255149 33864496767006605124845681)
              ·
                refine ⟨25398372575254953843634261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33864496767006605124845681 25398372575254953843634261)
                ·
                  refine ⟨297637178616268990355089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25398372575254953843634261 297637178616268990355089)
                  ·
                    rfl

theorem cell23_5216817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 8].length) (baseStart_5216817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216817 prefixEnd_5216817 := by exact prefixLift 5216817
  have htrace : WordTrace (prefixWord ++ tailWord_5216817) baseStart_5216817 baseEnd_5216817 := by
    simpa [prefixWord, tailWord_5216817, baseEnd_5216817] using wordTrace_append hprefix tailTrace_5216817
  have hstable : (prefixWord ++ tailWord_5216817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216817).length < 2 ^ (prefixWord ++ tailWord_5216817).sum := by decide
  have hdescent : baseEnd_5216817 < baseStart_5216817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216862 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5216862 : Nat := 118140960795 + 5216862 * 2 ^ 59
def prefixEnd_5216862 : Nat := 4983230072969 + 3 ^ 40 * 5216862 * 2
def baseEnd_5216862 : Nat := 2678757714175873237133095

theorem tailTrace_5216862 : CollatzResearch.WordTrace tailWord_5216862 prefixEnd_5216862 2678757714175873237133095 := by
  unfold tailWord_5216862
  simp only [CollatzResearch.WordTrace]
  refine ⟨23784323603275927242629605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126849725884138278627357893 23784323603275927242629605)
  ·
    refine ⟨4459560675614236357993051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23784323603275927242629605 4459560675614236357993051)
    ·
      refine ⟨6689341013421354536989577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4459560675614236357993051 6689341013421354536989577)
      ·
        refine ⟨5017005760066015902742183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6689341013421354536989577 5017005760066015902742183)
        ·
          refine ⟨7525508640099023854113275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017005760066015902742183 7525508640099023854113275)
          ·
            refine ⟨11288262960148535781169913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7525508640099023854113275 11288262960148535781169913)
            ·
              refine ⟨8466197220111401835877435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11288262960148535781169913 8466197220111401835877435)
              ·
                refine ⟨12699295830167102753816153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8466197220111401835877435 12699295830167102753816153)
                ·
                  refine ⟨9524471872625327065362115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12699295830167102753816153 9524471872625327065362115)
                  ·
                    refine ⟨14286707808937990598043173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9524471872625327065362115 14286707808937990598043173)
                    ·
                      refine ⟨2678757714175873237133095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14286707808937990598043173 2678757714175873237133095)
                      ·
                        rfl

theorem cell23_5216862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5216862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216862 prefixEnd_5216862 := by exact prefixLift 5216862
  have htrace : WordTrace (prefixWord ++ tailWord_5216862) baseStart_5216862 baseEnd_5216862 := by
    simpa [prefixWord, tailWord_5216862, baseEnd_5216862] using wordTrace_append hprefix tailTrace_5216862
  have hstable : (prefixWord ++ tailWord_5216862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216862).length < 2 ^ (prefixWord ++ tailWord_5216862).sum := by decide
  have hdescent : baseEnd_5216862 < baseStart_5216862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216907 : List Nat := [1, 1, 1, 1, 4, 1, 2, 12]
def baseStart_5216907 : Nat := 118140960795 + 5216907 * 2 ^ 59
def prefixEnd_5216907 : Nat := 4983230072969 + 3 ^ 40 * 5216907 * 2
def baseEnd_5216907 : Nat := 99214104474271317076681

theorem tailTrace_5216907 : CollatzResearch.WordTrace tailWord_5216907 prefixEnd_5216907 99214104474271317076681 := by
  unfold tailWord_5216907
  simp only [CollatzResearch.WordTrace]
  refine ⟨190276230111044390626424975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126850820074029593750949983 190276230111044390626424975)
  ·
    refine ⟨285414345166566585939637463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190276230111044390626424975 285414345166566585939637463)
    ·
      refine ⟨428121517749849878909456195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285414345166566585939637463 428121517749849878909456195)
      ·
        refine ⟨642182276624774818364184293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428121517749849878909456195 642182276624774818364184293)
        ·
          refine ⟨120409176867145278443284555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 642182276624774818364184293 120409176867145278443284555)
          ·
            refine ⟨180613765300717917664926833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120409176867145278443284555 180613765300717917664926833)
            ·
              refine ⟨135460323975538438248695125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180613765300717917664926833 135460323975538438248695125)
              ·
                refine ⟨99214104474271317076681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 135460323975538438248695125 99214104474271317076681)
                ·
                  rfl

theorem cell23_5216907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 12].length) (baseStart_5216907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216907 prefixEnd_5216907 := by exact prefixLift 5216907
  have htrace : WordTrace (prefixWord ++ tailWord_5216907) baseStart_5216907 baseEnd_5216907 := by
    simpa [prefixWord, tailWord_5216907, baseEnd_5216907] using wordTrace_append hprefix tailTrace_5216907
  have hstable : (prefixWord ++ tailWord_5216907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216907).length < 2 ^ (prefixWord ++ tailWord_5216907).sum := by decide
  have hdescent : baseEnd_5216907 < baseStart_5216907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216921 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 3]
def baseStart_5216921 : Nat := 118140960795 + 5216921 * 2 ^ 59
def prefixEnd_5216921 : Nat := 4983230072969 + 3 ^ 40 * 5216921 * 2
def baseEnd_5216921 : Nat := 2678788009534488506295323

theorem tailTrace_5216921 : CollatzResearch.WordTrace tailWord_5216921 prefixEnd_5216921 2678788009534488506295323 := by
  unfold tailWord_5216921
  simp only [CollatzResearch.WordTrace]
  refine ⟨190276740732993671017434617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126851160488662447344956411 190276740732993671017434617)
  ·
    refine ⟨142707555549745253263075963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190276740732993671017434617 142707555549745253263075963)
    ·
      refine ⟨214061333324617879894613945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142707555549745253263075963 214061333324617879894613945)
      ·
        refine ⟨160545999993463409920960459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214061333324617879894613945 160545999993463409920960459)
        ·
          refine ⟨240818999990195114881440689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160545999993463409920960459 240818999990195114881440689)
          ·
            refine ⟨180614249992646336161080517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240818999990195114881440689 180614249992646336161080517)
            ·
              refine ⟨33865171873621188030202597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180614249992646336161080517 33865171873621188030202597)
              ·
                refine ⟨6349719726303972755662987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33865171873621188030202597 6349719726303972755662987)
                ·
                  refine ⟨9524579589455959133494481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349719726303972755662987 9524579589455959133494481)
                  ·
                    refine ⟨7143434692091969350120861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9524579589455959133494481 7143434692091969350120861)
                    ·
                      refine ⟨2678788009534488506295323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7143434692091969350120861 2678788009534488506295323)
                      ·
                        rfl

theorem cell23_5216921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_5216921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216921 prefixEnd_5216921 := by exact prefixLift 5216921
  have htrace : WordTrace (prefixWord ++ tailWord_5216921) baseStart_5216921 baseEnd_5216921 := by
    simpa [prefixWord, tailWord_5216921, baseEnd_5216921] using wordTrace_append hprefix tailTrace_5216921
  have hstable : (prefixWord ++ tailWord_5216921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216921).length < 2 ^ (prefixWord ++ tailWord_5216921).sum := by decide
  have hdescent : baseEnd_5216921 < baseStart_5216921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216922 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5216922 : Nat := 118140960795 + 5216922 * 2 ^ 59
def prefixEnd_5216922 : Nat := 4983230072969 + 3 ^ 40 * 5216922 * 2
def baseEnd_5216922 : Nat := 2678788523015143002382819

theorem tailTrace_5216922 : CollatzResearch.WordTrace tailWord_5216922 prefixEnd_5216922 2678788523015143002382819 := by
  unfold tailWord_5216922
  simp only [CollatzResearch.WordTrace]
  refine ⟨47569194301497512047055255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126851184803993365458814013 47569194301497512047055255)
  ·
    refine ⟨71353791452246268070582883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47569194301497512047055255 71353791452246268070582883)
    ·
      refine ⟨107030687178369402105874325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71353791452246268070582883 107030687178369402105874325)
      ·
        refine ⟨5017063461486065723712859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107030687178369402105874325 5017063461486065723712859)
        ·
          refine ⟨7525595192229098585569289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017063461486065723712859 7525595192229098585569289)
          ·
            refine ⟨5644196394171823939176967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7525595192229098585569289 5644196394171823939176967)
            ·
              refine ⟨8466294591257735908765451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644196394171823939176967 8466294591257735908765451)
              ·
                refine ⟨12699441886886603863148177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8466294591257735908765451 12699441886886603863148177)
                ·
                  refine ⟨9524581415164952897361133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12699441886886603863148177 9524581415164952897361133)
                  ·
                    refine ⟨3571718030686857336510425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9524581415164952897361133 3571718030686857336510425)
                    ·
                      refine ⟨2678788523015143002382819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571718030686857336510425 2678788523015143002382819)
                      ·
                        rfl

theorem cell23_5216922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5216922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216922 prefixEnd_5216922 := by exact prefixLift 5216922
  have htrace : WordTrace (prefixWord ++ tailWord_5216922) baseStart_5216922 baseEnd_5216922 := by
    simpa [prefixWord, tailWord_5216922, baseEnd_5216922] using wordTrace_append hprefix tailTrace_5216922
  have hstable : (prefixWord ++ tailWord_5216922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216922).length < 2 ^ (prefixWord ++ tailWord_5216922).sum := by decide
  have hdescent : baseEnd_5216922 < baseStart_5216922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216935 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5216935 : Nat := 118140960795 + 5216935 * 2 ^ 59
def prefixEnd_5216935 : Nat := 4983230072969 + 3 ^ 40 * 5216935 * 2
def baseEnd_5216935 : Nat := 2678795198263651451520259

theorem tailTrace_5216935 : CollatzResearch.WordTrace tailWord_5216935 prefixEnd_5216935 2678795198263651451520259 := by
  unfold tailWord_5216935
  simp only [CollatzResearch.WordTrace]
  refine ⟨190277251354942951408444259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126851500903295300938962839 190277251354942951408444259)
  ·
    refine ⟨285415877032414427112666389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190277251354942951408444259 285415877032414427112666389)
    ·
      refine ⟨13378869235894426270906237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 285415877032414427112666389 13378869235894426270906237)
      ·
        refine ⟨5017075963460409851589839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13378869235894426270906237 5017075963460409851589839)
        ·
          refine ⟨7525613945190614777384759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017075963460409851589839 7525613945190614777384759)
          ·
            refine ⟨11288420917785922166077139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7525613945190614777384759 11288420917785922166077139)
            ·
              refine ⟨16932631376678883249115709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11288420917785922166077139 16932631376678883249115709)
              ·
                refine ⟨6349736766254581218418391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16932631376678883249115709 6349736766254581218418391)
                ·
                  refine ⟨9524605149381871827627587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349736766254581218418391 9524605149381871827627587)
                  ·
                    refine ⟨14286907724072807741441381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9524605149381871827627587 14286907724072807741441381)
                    ·
                      refine ⟨2678795198263651451520259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14286907724072807741441381 2678795198263651451520259)
                      ·
                        rfl

theorem cell23_5216935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5216935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216935 prefixEnd_5216935 := by exact prefixLift 5216935
  have htrace : WordTrace (prefixWord ++ tailWord_5216935) baseStart_5216935 baseEnd_5216935 := by
    simpa [prefixWord, tailWord_5216935, baseEnd_5216935] using wordTrace_append hprefix tailTrace_5216935
  have hstable : (prefixWord ++ tailWord_5216935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216935).length < 2 ^ (prefixWord ++ tailWord_5216935).sum := by decide
  have hdescent : baseEnd_5216935 < baseStart_5216935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216968 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_5216968 : Nat := 118140960795 + 5216968 * 2 ^ 59
def prefixEnd_5216968 : Nat := 4983230072969 + 3 ^ 40 * 5216968 * 2
def baseEnd_5216968 : Nat := 2678812143125249822407607

theorem tailTrace_5216968 : CollatzResearch.WordTrace tailWord_5216968 prefixEnd_5216968 2678812143125249822407607 := by
  unfold tailWord_5216968
  simp only [CollatzResearch.WordTrace]
  refine ⟨95139227481911699022197779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126852303309215598696263705 95139227481911699022197779)
  ·
    refine ⟨142708841222867548533296669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95139227481911699022197779 142708841222867548533296669)
    ·
      refine ⟨53515815458575330699986251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142708841222867548533296669 53515815458575330699986251)
      ·
        refine ⟨80273723187862996049979377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53515815458575330699986251 80273723187862996049979377)
        ·
          refine ⟨60205292390897247037484533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80273723187862996049979377 60205292390897247037484533)
          ·
            refine ⟨5644246161646616909764175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60205292390897247037484533 5644246161646616909764175)
            ·
              refine ⟨8466369242469925364646263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644246161646616909764175 8466369242469925364646263)
              ·
                refine ⟨12699553863704888046969395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8466369242469925364646263 12699553863704888046969395)
                ·
                  refine ⟨19049330795557332070454093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12699553863704888046969395 19049330795557332070454093)
                  ·
                    refine ⟨7143499048333999526420285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19049330795557332070454093 7143499048333999526420285)
                    ·
                      refine ⟨2678812143125249822407607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7143499048333999526420285 2678812143125249822407607)
                      ·
                        rfl

theorem cell23_5216968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_5216968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216968 prefixEnd_5216968 := by exact prefixLift 5216968
  have htrace : WordTrace (prefixWord ++ tailWord_5216968) baseStart_5216968 baseEnd_5216968 := by
    simpa [prefixWord, tailWord_5216968, baseEnd_5216968] using wordTrace_append hprefix tailTrace_5216968
  have hstable : (prefixWord ++ tailWord_5216968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216968).length < 2 ^ (prefixWord ++ tailWord_5216968).sum := by decide
  have hdescent : baseEnd_5216968 < baseStart_5216968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5216995 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5216995 : Nat := 118140960795 + 5216995 * 2 ^ 59
def prefixEnd_5216995 : Nat := 4983230072969 + 3 ^ 40 * 5216995 * 2
def baseEnd_5216995 : Nat := 2678826007102921216769983

theorem tailTrace_5216995 : CollatzResearch.WordTrace tailWord_5216995 prefixEnd_5216995 2678826007102921216769983 := by
  unfold tailWord_5216995
  simp only [CollatzResearch.WordTrace]
  refine ⟨190279439734725581655628439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126852959823150387770418959 190279439734725581655628439)
  ·
    refine ⟨285419159602088372483442659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190279439734725581655628439 285419159602088372483442659)
    ·
      refine ⟨428128739403132558725163989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285419159602088372483442659 428128739403132558725163989)
      ·
        refine ⟨10034267329760919345121031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 428128739403132558725163989 10034267329760919345121031)
        ·
          refine ⟨15051400994641379017681547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10034267329760919345121031 15051400994641379017681547)
          ·
            refine ⟨22577101491962068526522321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15051400994641379017681547 22577101491962068526522321)
            ·
              refine ⟨16932826118971551394891741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22577101491962068526522321 16932826118971551394891741)
              ·
                refine ⟨6349809794614331773084403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16932826118971551394891741 6349809794614331773084403)
                ·
                  refine ⟨9524714691921497659626605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349809794614331773084403 9524714691921497659626605)
                  ·
                    refine ⟨3571768009470561622359977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9524714691921497659626605 3571768009470561622359977)
                    ·
                      refine ⟨2678826007102921216769983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571768009470561622359977 2678826007102921216769983)
                      ·
                        rfl

theorem cell23_5216995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5216995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5216995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5216995 prefixEnd_5216995 := by exact prefixLift 5216995
  have htrace : WordTrace (prefixWord ++ tailWord_5216995) baseStart_5216995 baseEnd_5216995 := by
    simpa [prefixWord, tailWord_5216995, baseEnd_5216995] using wordTrace_append hprefix tailTrace_5216995
  have hstable : (prefixWord ++ tailWord_5216995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5216995).length < 2 ^ (prefixWord ++ tailWord_5216995).sum := by decide
  have hdescent : baseEnd_5216995 < baseStart_5216995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5216995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217008 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 4, 2, 2]
def baseStart_5217008 : Nat := 118140960795 + 5217008 * 2 ^ 59
def prefixEnd_5217008 : Nat := 4983230072969 + 3 ^ 40 * 5217008 * 2
def baseEnd_5217008 : Nat := 2678832682351429665907423

theorem tailTrace_5217008 : CollatzResearch.WordTrace tailWord_5217008 prefixEnd_5217008 2678832682351429665907423 := by
  unfold tailWord_5217008
  simp only [CollatzResearch.WordTrace]
  refine ⟨95139956941839242437925839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126853275922452323250567785 95139956941839242437925839)
  ·
    refine ⟨142709935412758863656888759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95139956941839242437925839 142709935412758863656888759)
    ·
      refine ⟨214064903119138295485333139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142709935412758863656888759 214064903119138295485333139)
      ·
        refine ⟨321097354678707443227999709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214064903119138295485333139 321097354678707443227999709)
        ·
          refine ⟨120411508004515291210499891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321097354678707443227999709 120411508004515291210499891)
          ·
            refine ⟨180617262006772936815749837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120411508004515291210499891 180617262006772936815749837)
            ·
              refine ⟨67731473252539851305906189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180617262006772936815749837 67731473252539851305906189)
              ·
                refine ⟨25399302469702444239714821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67731473252539851305906189 25399302469702444239714821)
                ·
                  refine ⟨4762369213069208294946529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25399302469702444239714821 4762369213069208294946529)
                  ·
                    refine ⟨3571776909801906221209897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4762369213069208294946529 3571776909801906221209897)
                    ·
                      refine ⟨2678832682351429665907423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571776909801906221209897 2678832682351429665907423)
                      ·
                        rfl

theorem cell23_5217008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 2, 2].length) (baseStart_5217008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217008 prefixEnd_5217008 := by exact prefixLift 5217008
  have htrace : WordTrace (prefixWord ++ tailWord_5217008) baseStart_5217008 baseEnd_5217008 := by
    simpa [prefixWord, tailWord_5217008, baseEnd_5217008] using wordTrace_append hprefix tailTrace_5217008
  have hstable : (prefixWord ++ tailWord_5217008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217008).length < 2 ^ (prefixWord ++ tailWord_5217008).sum := by decide
  have hdescent : baseEnd_5217008 < baseStart_5217008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217042 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5217042 : Nat := 118140960795 + 5217042 * 2 ^ 59
def prefixEnd_5217042 : Nat := 4983230072969 + 3 ^ 40 * 5217042 * 2
def baseEnd_5217042 : Nat := 2678850140693682532882267

theorem tailTrace_5217042 : CollatzResearch.WordTrace tailWord_5217042 prefixEnd_5217042 2678850140693682532882267 := by
  unfold tailWord_5217042
  simp only [CollatzResearch.WordTrace]
  refine ⟨47570288491388827170647345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126854102643703539121726253 47570288491388827170647345)
  ·
    refine ⟨35677716368541620377985509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47570288491388827170647345 35677716368541620377985509)
    ·
      refine ⟨6689571819101553820872283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35677716368541620377985509 6689571819101553820872283)
      ·
        refine ⟨10034357728652330731308425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6689571819101553820872283 10034357728652330731308425)
        ·
          refine ⟨7525768296489248048481319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10034357728652330731308425 7525768296489248048481319)
          ·
            refine ⟨11288652444733872072721979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7525768296489248048481319 11288652444733872072721979)
            ·
              refine ⟨16932978667100808109082969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11288652444733872072721979 16932978667100808109082969)
              ·
                refine ⟨12699734000325606081812227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16932978667100808109082969 12699734000325606081812227)
                ·
                  refine ⟨19049601000488409122718341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12699734000325606081812227 19049601000488409122718341)
                  ·
                    refine ⟨3571800187591576710509689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19049601000488409122718341 3571800187591576710509689)
                    ·
                      refine ⟨2678850140693682532882267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571800187591576710509689 2678850140693682532882267)
                      ·
                        rfl

theorem cell23_5217042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5217042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217042 prefixEnd_5217042 := by exact prefixLift 5217042
  have htrace : WordTrace (prefixWord ++ tailWord_5217042) baseStart_5217042 baseEnd_5217042 := by
    simpa [prefixWord, tailWord_5217042, baseEnd_5217042] using wordTrace_append hprefix tailTrace_5217042
  have hstable : (prefixWord ++ tailWord_5217042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217042).length < 2 ^ (prefixWord ++ tailWord_5217042).sum := by decide
  have hdescent : baseEnd_5217042 < baseStart_5217042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217051 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 7, 2]
def baseStart_5217051 : Nat := 118140960795 + 5217051 * 2 ^ 59
def prefixEnd_5217051 : Nat := 4983230072969 + 3 ^ 40 * 5217051 * 2
def baseEnd_5217051 : Nat := 2678854762019572997669725

theorem tailTrace_5217051 : CollatzResearch.WordTrace tailWord_5217051 prefixEnd_5217051 2678854762019572997669725 := by
  unfold tailWord_5217051
  simp only [CollatzResearch.WordTrace]
  refine ⟨190281482222522703219667007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126854321481681802146444671 190281482222522703219667007)
  ·
    refine ⟨285422223333784054829500511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190281482222522703219667007 285422223333784054829500511)
    ·
      refine ⟨428133335000676082244250767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285422223333784054829500511 428133335000676082244250767)
      ·
        refine ⟨642200002501014123366376151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428133335000676082244250767 642200002501014123366376151)
        ·
          refine ⟨963300003751521185049564227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642200002501014123366376151 963300003751521185049564227)
          ·
            refine ⟨1444950005627281777574346341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963300003751521185049564227 1444950005627281777574346341)
            ·
              refine ⟨270928126055115333295189939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1444950005627281777574346341 270928126055115333295189939)
              ·
                refine ⟨406392189082672999942784909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270928126055115333295189939 406392189082672999942784909)
                ·
                  refine ⟨152397070906002374978544341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406392189082672999942784909 152397070906002374978544341)
                  ·
                    refine ⟨3571806349359430663559633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 152397070906002374978544341 3571806349359430663559633)
                    ·
                      refine ⟨2678854762019572997669725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571806349359430663559633 2678854762019572997669725)
                      ·
                        rfl

theorem cell23_5217051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7, 2].length) (baseStart_5217051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217051 prefixEnd_5217051 := by exact prefixLift 5217051
  have htrace : WordTrace (prefixWord ++ tailWord_5217051) baseStart_5217051 baseEnd_5217051 := by
    simpa [prefixWord, tailWord_5217051, baseEnd_5217051] using wordTrace_append hprefix tailTrace_5217051
  have hstable : (prefixWord ++ tailWord_5217051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217051).length < 2 ^ (prefixWord ++ tailWord_5217051).sum := by decide
  have hdescent : baseEnd_5217051 < baseStart_5217051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217061 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_5217061 : Nat := 118140960795 + 5217061 * 2 ^ 59
def prefixEnd_5217061 : Nat := 4983230072969 + 3 ^ 40 * 5217061 * 2
def baseEnd_5217061 : Nat := 892953298942039319514893

theorem tailTrace_5217061 : CollatzResearch.WordTrace tailWord_5217061 prefixEnd_5217061 892953298942039319514893 := by
  unfold tailWord_5217061
  simp only [CollatzResearch.WordTrace]
  refine ⟨190281846952486474927531037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126854564634990983285020691 190281846952486474927531037)
  ·
    refine ⟨71355692607182428097824139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190281846952486474927531037 71355692607182428097824139)
    ·
      refine ⟨107033538910773642146736209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71355692607182428097824139 107033538910773642146736209)
      ·
        refine ⟨80275154183080231610052157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107033538910773642146736209 80275154183080231610052157)
        ·
          refine ⟨30103182818655086853769559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80275154183080231610052157 30103182818655086853769559)
          ·
            refine ⟨45154774227982630280654339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30103182818655086853769559 45154774227982630280654339)
            ·
              refine ⟨67732161341973945420981509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45154774227982630280654339 67732161341973945420981509)
              ·
                refine ⟨12699780251620114766434033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67732161341973945420981509 12699780251620114766434033)
                ·
                  refine ⟨9524835188715086074825525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12699780251620114766434033 9524835188715086074825525)
                  ·
                    refine ⟨892953298942039319514893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9524835188715086074825525 892953298942039319514893)
                    ·
                      rfl

theorem cell23_5217061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_5217061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217061 prefixEnd_5217061 := by exact prefixLift 5217061
  have htrace : WordTrace (prefixWord ++ tailWord_5217061) baseStart_5217061 baseEnd_5217061 := by
    simpa [prefixWord, tailWord_5217061, baseEnd_5217061] using wordTrace_append hprefix tailTrace_5217061
  have hstable : (prefixWord ++ tailWord_5217061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217061).length < 2 ^ (prefixWord ++ tailWord_5217061).sum := by decide
  have hdescent : baseEnd_5217061 < baseStart_5217061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217111 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_5217111 : Nat := 118140960795 + 5217111 * 2 ^ 59
def prefixEnd_5217111 : Nat := 4983230072969 + 3 ^ 40 * 5217111 * 2
def baseEnd_5217111 : Nat := 2678885570858842762919449

theorem tailTrace_5217111 : CollatzResearch.WordTrace tailWord_5217111 prefixEnd_5217111 2678885570858842762919449 := by
  unfold tailWord_5217111
  simp only [CollatzResearch.WordTrace]
  refine ⟨190283670602305333466851187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126855780401536888977900791 190283670602305333466851187)
  ·
    refine ⟨285425505903458000200276781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190283670602305333466851187 285425505903458000200276781)
    ·
      refine ⟨107034564713796750075103793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285425505903458000200276781 107034564713796750075103793)
      ·
        refine ⟨80275923535347562556327845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107034564713796750075103793 80275923535347562556327845)
        ·
          refine ⟨15051735662877667979311471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80275923535347562556327845 15051735662877667979311471)
          ·
            refine ⟨22577603494316501968967207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15051735662877667979311471 22577603494316501968967207)
            ·
              refine ⟨33866405241474752953450811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22577603494316501968967207 33866405241474752953450811)
              ·
                refine ⟨50799607862212129430176217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33866405241474752953450811 50799607862212129430176217)
                ·
                  refine ⟨38099705896659097072632163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50799607862212129430176217 38099705896659097072632163)
                  ·
                    refine ⟨57149558844988645608948245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38099705896659097072632163 57149558844988645608948245)
                    ·
                      refine ⟨2678885570858842762919449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57149558844988645608948245 2678885570858842762919449)
                      ·
                        rfl

theorem cell23_5217111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_5217111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217111 prefixEnd_5217111 := by exact prefixLift 5217111
  have htrace : WordTrace (prefixWord ++ tailWord_5217111) baseStart_5217111 baseEnd_5217111 := by
    simpa [prefixWord, tailWord_5217111, baseEnd_5217111] using wordTrace_append hprefix tailTrace_5217111
  have hstable : (prefixWord ++ tailWord_5217111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217111).length < 2 ^ (prefixWord ++ tailWord_5217111).sum := by decide
  have hdescent : baseEnd_5217111 < baseStart_5217111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217121 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 6]
def baseStart_5217121 : Nat := 118140960795 + 5217121 * 2 ^ 59
def prefixEnd_5217121 : Nat := 4983230072969 + 3 ^ 40 * 5217121 * 2
def baseEnd_5217121 : Nat := 297654522851709747088267

theorem tailTrace_5217121 : CollatzResearch.WordTrace tailWord_5217121 prefixEnd_5217121 297654522851709747088267 := by
  unfold tailWord_5217121
  simp only [CollatzResearch.WordTrace]
  refine ⟨190284035332269105174715217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126856023554846070116476811 190284035332269105174715217)
  ·
    refine ⟨142713026499201828881036413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190284035332269105174715217 142713026499201828881036413)
    ·
      refine ⟨53517384937200685830388655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142713026499201828881036413 53517384937200685830388655)
      ·
        refine ⟨80276077405801028745582983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53517384937200685830388655 80276077405801028745582983)
        ·
          refine ⟨120414116108701543118374475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80276077405801028745582983 120414116108701543118374475)
          ·
            refine ⟨180621174163052314677561713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120414116108701543118374475 180621174163052314677561713)
            ·
              refine ⟨135465880622289236008171285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180621174163052314677561713 135465880622289236008171285)
              ·
                refine ⟨6349963154169807937883029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135465880622289236008171285 6349963154169807937883029)
                ·
                  refine ⟨297654522851709747088267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6349963154169807937883029 297654522851709747088267)
                  ·
                    rfl

theorem cell23_5217121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 6].length) (baseStart_5217121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217121 prefixEnd_5217121 := by exact prefixLift 5217121
  have htrace : WordTrace (prefixWord ++ tailWord_5217121) baseStart_5217121 baseEnd_5217121 := by
    simpa [prefixWord, tailWord_5217121, baseEnd_5217121] using wordTrace_append hprefix tailTrace_5217121
  have hstable : (prefixWord ++ tailWord_5217121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217121).length < 2 ^ (prefixWord ++ tailWord_5217121).sum := by decide
  have hdescent : baseEnd_5217121 < baseStart_5217121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217125 : List Nat := [1, 3, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_5217125 : Nat := 118140960795 + 5217125 * 2 ^ 59
def prefixEnd_5217125 : Nat := 4983230072969 + 3 ^ 40 * 5217125 * 2
def baseEnd_5217125 : Nat := 892964253196001902714795

theorem tailTrace_5217125 : CollatzResearch.WordTrace tailWord_5217125 prefixEnd_5217125 892964253196001902714795 := by
  unfold tailWord_5217125
  simp only [CollatzResearch.WordTrace]
  refine ⟨190284181224254613857860829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126856120816169742571907219 190284181224254613857860829)
  ·
    refine ⟨71356567959095480196697811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190284181224254613857860829 71356567959095480196697811)
    ·
      refine ⟨107034851938643220295046717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71356567959095480196697811 107034851938643220295046717)
      ·
        refine ⟨40138069476991207610642519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107034851938643220295046717 40138069476991207610642519)
        ·
          refine ⟨60207104215486811415963779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40138069476991207610642519 60207104215486811415963779)
          ·
            refine ⟨90310656323230217123945669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60207104215486811415963779 90310656323230217123945669)
            ·
              refine ⟨16933248060605665710739813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90310656323230217123945669 16933248060605665710739813)
              ·
                refine ⟨3174984011363562320763715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16933248060605665710739813 3174984011363562320763715)
                ·
                  refine ⟨4762476017045343481145573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174984011363562320763715 4762476017045343481145573)
                  ·
                    refine ⟨892964253196001902714795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4762476017045343481145573 892964253196001902714795)
                    ·
                      rfl

theorem cell23_5217125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_5217125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217125 prefixEnd_5217125 := by exact prefixLift 5217125
  have htrace : WordTrace (prefixWord ++ tailWord_5217125) baseStart_5217125 baseEnd_5217125 := by
    simpa [prefixWord, tailWord_5217125, baseEnd_5217125] using wordTrace_append hprefix tailTrace_5217125
  have hstable : (prefixWord ++ tailWord_5217125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217125).length < 2 ^ (prefixWord ++ tailWord_5217125).sum := by decide
  have hdescent : baseEnd_5217125 < baseStart_5217125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217151 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 3, 5]
def baseStart_5217151 : Nat := 118140960795 + 5217151 * 2 ^ 59
def prefixEnd_5217151 : Nat := 4983230072969 + 3 ^ 40 * 5217151 * 2
def baseEnd_5217151 : Nat := 892968703361674202139755

theorem tailTrace_5217151 : CollatzResearch.WordTrace tailWord_5217151 prefixEnd_5217151 892968703361674202139755 := by
  unfold tailWord_5217151
  simp only [CollatzResearch.WordTrace]
  refine ⟨190285129522160420298307307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126856753014773613532204871 190285129522160420298307307)
  ·
    refine ⟨285427694283240630447460961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190285129522160420298307307 285427694283240630447460961)
    ·
      refine ⟨214070770712430472835595721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285427694283240630447460961 214070770712430472835595721)
      ·
        refine ⟨160553078034322854626696791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214070770712430472835595721 160553078034322854626696791)
        ·
          refine ⟨240829617051484281940045187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160553078034322854626696791 240829617051484281940045187)
          ·
            refine ⟨361244425577226422910067781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240829617051484281940045187 361244425577226422910067781)
            ·
              refine ⟨67733329795729954295637709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 361244425577226422910067781 67733329795729954295637709)
              ·
                refine ⟨25399998673398732860864141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67733329795729954295637709 25399998673398732860864141)
                ·
                  refine ⟨9524999502524524822824053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25399998673398732860864141 9524999502524524822824053)
                  ·
                    refine ⟨892968703361674202139755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9524999502524524822824053 892968703361674202139755)
                    ·
                      rfl

theorem cell23_5217151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_5217151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217151 prefixEnd_5217151 := by exact prefixLift 5217151
  have htrace : WordTrace (prefixWord ++ tailWord_5217151) baseStart_5217151 baseEnd_5217151 := by
    simpa [prefixWord, tailWord_5217151, baseEnd_5217151] using wordTrace_append hprefix tailTrace_5217151
  have hstable : (prefixWord ++ tailWord_5217151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217151).length < 2 ^ (prefixWord ++ tailWord_5217151).sum := by decide
  have hdescent : baseEnd_5217151 < baseStart_5217151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217175 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 2, 3, 2]
def baseStart_5217175 : Nat := 118140960795 + 5217175 * 2 ^ 59
def prefixEnd_5217175 : Nat := 4983230072969 + 3 ^ 40 * 5217175 * 2
def baseEnd_5217175 : Nat := 2678918433620730512519155

theorem tailTrace_5217175 : CollatzResearch.WordTrace tailWord_5217175 prefixEnd_5217175 2678918433620730512519155 := by
  unfold tailWord_5217175
  simp only [CollatzResearch.WordTrace]
  refine ⟨190286004874073472397180979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126857336582715648264787319 190286004874073472397180979)
  ·
    refine ⟨285429007311110208595771469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190286004874073472397180979 285429007311110208595771469)
    ·
      refine ⟨107035877741666328223414301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285429007311110208595771469 107035877741666328223414301)
      ·
        refine ⟨40138454153124873083780363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107035877741666328223414301 40138454153124873083780363)
        ·
          refine ⟨60207681229687309625670545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40138454153124873083780363 60207681229687309625670545)
          ·
            refine ⟨45155760922265482219252909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60207681229687309625670545 45155760922265482219252909)
            ·
              refine ⟨16933410345849555832219841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45155760922265482219252909 16933410345849555832219841)
              ·
                refine ⟨12700057759387166874164881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16933410345849555832219841 12700057759387166874164881)
                ·
                  refine ⟨9525043319540375155623661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12700057759387166874164881 9525043319540375155623661)
                  ·
                    refine ⟨3571891244827640683358873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9525043319540375155623661 3571891244827640683358873)
                    ·
                      refine ⟨2678918433620730512519155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3571891244827640683358873 2678918433620730512519155)
                      ·
                        rfl

theorem cell23_5217175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_5217175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217175 prefixEnd_5217175 := by exact prefixLift 5217175
  have htrace : WordTrace (prefixWord ++ tailWord_5217175) baseStart_5217175 baseEnd_5217175 := by
    simpa [prefixWord, tailWord_5217175, baseEnd_5217175] using wordTrace_append hprefix tailTrace_5217175
  have hstable : (prefixWord ++ tailWord_5217175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217175).length < 2 ^ (prefixWord ++ tailWord_5217175).sum := by decide
  have hdescent : baseEnd_5217175 < baseStart_5217175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217188 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_5217188 : Nat := 118140960795 + 5217188 * 2 ^ 59
def prefixEnd_5217188 : Nat := 4983230072969 + 3 ^ 40 * 5217188 * 2
def baseEnd_5217188 : Nat := 2678925108869238961656595

theorem tailTrace_5217188 : CollatzResearch.WordTrace tailWord_5217188 prefixEnd_5217188 2678925108869238961656595 := by
  unfold tailWord_5217188
  simp only [CollatzResearch.WordTrace]
  refine ⟨95143239511513187808702109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126857652682017583744936145 95143239511513187808702109)
  ·
    refine ⟨35678714816817445428263291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95143239511513187808702109 35678714816817445428263291)
    ·
      refine ⟨53518072225226168142394937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35678714816817445428263291 53518072225226168142394937)
      ·
        refine ⟨40138554168919626106796203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53518072225226168142394937 40138554168919626106796203)
        ·
          refine ⟨60207831253379439160194305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40138554168919626106796203 60207831253379439160194305)
          ·
            refine ⟨45155873440034579370145729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60207831253379439160194305 45155873440034579370145729)
            ·
              refine ⟨33866905080025934527609297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45155873440034579370145729 33866905080025934527609297)
              ·
                refine ⟨25400178810019450895706973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33866905080025934527609297 25400178810019450895706973)
                ·
                  refine ⟨9525067053757294085890115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25400178810019450895706973 9525067053757294085890115)
                  ·
                    refine ⟨14287600580635941128835173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9525067053757294085890115 14287600580635941128835173)
                    ·
                      refine ⟨2678925108869238961656595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14287600580635941128835173 2678925108869238961656595)
                      ·
                        rfl

theorem cell23_5217188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_5217188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217188 prefixEnd_5217188 := by exact prefixLift 5217188
  have htrace : WordTrace (prefixWord ++ tailWord_5217188) baseStart_5217188 baseEnd_5217188 := by
    simpa [prefixWord, tailWord_5217188, baseEnd_5217188] using wordTrace_append hprefix tailTrace_5217188
  have hstable : (prefixWord ++ tailWord_5217188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217188).length < 2 ^ (prefixWord ++ tailWord_5217188).sum := by decide
  have hdescent : baseEnd_5217188 < baseStart_5217188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217245 : List Nat := [1, 4, 3, 1, 2, 3, 1, 8]
def baseStart_5217245 : Nat := 118140960795 + 5217245 * 2 ^ 59
def prefixEnd_5217245 : Nat := 4983230072969 + 3 ^ 40 * 5217245 * 2
def baseEnd_5217245 : Nat := 99220532491353527357179

theorem tailTrace_5217245 : CollatzResearch.WordTrace tailWord_5217245 prefixEnd_5217245 99220532491353527357179 := by
  unfold tailWord_5217245
  simp only [CollatzResearch.WordTrace]
  refine ⟨190288557983819874352229189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126859038655879916234819459 190288557983819874352229189)
  ·
    refine ⟨35679104621966226441042973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190288557983819874352229189 35679104621966226441042973)
    ·
      refine ⟨13379664233237334915391115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35679104621966226441042973 13379664233237334915391115)
      ·
        refine ⟨20069496349856002373086673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13379664233237334915391115 20069496349856002373086673)
        ·
          refine ⟨15052122262392001779815005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20069496349856002373086673 15052122262392001779815005)
          ·
            refine ⟨5644545848397000667430627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15052122262392001779815005 5644545848397000667430627)
            ·
              refine ⟨8466818772595501001145941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644545848397000667430627 8466818772595501001145941)
              ·
                refine ⟨99220532491353527357179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8466818772595501001145941 99220532491353527357179)
                ·
                  rfl

theorem cell23_5217245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 8].length) (baseStart_5217245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217245 prefixEnd_5217245 := by exact prefixLift 5217245
  have htrace : WordTrace (prefixWord ++ tailWord_5217245) baseStart_5217245 baseEnd_5217245 := by
    simpa [prefixWord, tailWord_5217245, baseEnd_5217245] using wordTrace_append hprefix tailTrace_5217245
  have hstable : (prefixWord ++ tailWord_5217245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217245).length < 2 ^ (prefixWord ++ tailWord_5217245).sum := by decide
  have hdescent : baseEnd_5217245 < baseStart_5217245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217255 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5217255 : Nat := 118140960795 + 5217255 * 2 ^ 59
def prefixEnd_5217255 : Nat := 4983230072969 + 3 ^ 40 * 5217255 * 2
def baseEnd_5217255 : Nat := 2678959512073090199518787

theorem tailTrace_5217255 : CollatzResearch.WordTrace tailWord_5217255 prefixEnd_5217255 2678959512073090199518787 := by
  unfold tailWord_5217255
  simp only [CollatzResearch.WordTrace]
  refine ⟨190288922713783646060093219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126859281809189097373395479 190288922713783646060093219)
  ·
    refine ⟨285433384070675469090139829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190288922713783646060093219 285433384070675469090139829)
    ·
      refine ⟨26759379756625825227200609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285433384070675469090139829 26759379756625825227200609)
      ·
        refine ⟨20069534817469368920400457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26759379756625825227200609 20069534817469368920400457)
        ·
          refine ⟨15052151113102026690300343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20069534817469368920400457 15052151113102026690300343)
          ·
            refine ⟨22578226669653040035450515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15052151113102026690300343 22578226669653040035450515)
            ·
              refine ⟨33867340004479560053175773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22578226669653040035450515 33867340004479560053175773)
              ·
                refine ⟨12700252501679835019940915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33867340004479560053175773 12700252501679835019940915)
                ·
                  refine ⟨19050378752519752529911373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12700252501679835019940915 19050378752519752529911373)
                  ·
                    refine ⟨7143892032194907198716765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19050378752519752529911373 7143892032194907198716765)
                    ·
                      refine ⟨2678959512073090199518787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7143892032194907198716765 2678959512073090199518787)
                      ·
                        rfl

theorem cell23_5217255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5217255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217255 prefixEnd_5217255 := by exact prefixLift 5217255
  have htrace : WordTrace (prefixWord ++ tailWord_5217255) baseStart_5217255 baseEnd_5217255 := by
    simpa [prefixWord, tailWord_5217255, baseEnd_5217255] using wordTrace_append hprefix tailTrace_5217255
  have hstable : (prefixWord ++ tailWord_5217255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217255).length < 2 ^ (prefixWord ++ tailWord_5217255).sum := by decide
  have hdescent : baseEnd_5217255 < baseStart_5217255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217288 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 2, 6]
def baseStart_5217288 : Nat := 118140960795 + 5217288 * 2 ^ 59
def prefixEnd_5217288 : Nat := 4983230072969 + 3 ^ 40 * 5217288 * 2
def baseEnd_5217288 : Nat := 892992152311562856802045

theorem tailTrace_5217288 : CollatzResearch.WordTrace tailWord_5217288 prefixEnd_5217288 892992152311562856802045 := by
  unfold tailWord_5217288
  simp only [CollatzResearch.WordTrace]
  refine ⟨95145063161332046348022259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126860084215109395130696345 95145063161332046348022259)
  ·
    refine ⟨142717594741998069522033389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95145063161332046348022259 142717594741998069522033389)
    ·
      refine ⟨53519098028249276070762521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142717594741998069522033389 53519098028249276070762521)
      ·
        refine ⟨40139323521186957053071891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53519098028249276070762521 40139323521186957053071891)
        ·
          refine ⟨60208985281780435579607837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40139323521186957053071891 60208985281780435579607837)
          ·
            refine ⟨22578369480667663342352939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60208985281780435579607837 22578369480667663342352939)
            ·
              refine ⟨33867554221001495013529409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22578369480667663342352939 33867554221001495013529409)
              ·
                refine ⟨25400665665751121260147057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33867554221001495013529409 25400665665751121260147057)
                ·
                  refine ⟨19050499249313340945110293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25400665665751121260147057 19050499249313340945110293)
                  ·
                    refine ⟨892992152311562856802045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19050499249313340945110293 892992152311562856802045)
                    ·
                      rfl

theorem cell23_5217288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_5217288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217288 prefixEnd_5217288 := by exact prefixLift 5217288
  have htrace : WordTrace (prefixWord ++ tailWord_5217288) baseStart_5217288 baseEnd_5217288 := by
    simpa [prefixWord, tailWord_5217288, baseEnd_5217288] using wordTrace_append hprefix tailTrace_5217288
  have hstable : (prefixWord ++ tailWord_5217288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217288).length < 2 ^ (prefixWord ++ tailWord_5217288).sum := by decide
  have hdescent : baseEnd_5217288 < baseStart_5217288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217332 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5217332 : Nat := 118140960795 + 5217332 * 2 ^ 59
def prefixEnd_5217332 : Nat := 4983230072969 + 3 ^ 40 * 5217332 * 2
def baseEnd_5217332 : Nat := 2678999050083486398255933

theorem tailTrace_5217332 : CollatzResearch.WordTrace tailWord_5217332 prefixEnd_5217332 2678999050083486398255933 := by
  unfold tailWord_5217332
  simp only [CollatzResearch.WordTrace]
  refine ⟨95145865567252344105323125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126861154089669792140430833 95145865567252344105323125)
  ·
    refine ⟨8919924896929907259874043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95145865567252344105323125 8919924896929907259874043)
    ·
      refine ⟨13379887345394860889811065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8919924896929907259874043 13379887345394860889811065)
      ·
        refine ⟨10034915509046145667358299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13379887345394860889811065 10034915509046145667358299)
        ·
          refine ⟨15052373263569218501037449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10034915509046145667358299 15052373263569218501037449)
          ·
            refine ⟨11289279947676913875778087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15052373263569218501037449 11289279947676913875778087)
            ·
              refine ⟨16933919921515370813667131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11289279947676913875778087 16933919921515370813667131)
              ·
                refine ⟨25400879882273056220500697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16933919921515370813667131 25400879882273056220500697)
                ·
                  refine ⟨19050659911704792165375523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25400879882273056220500697 19050659911704792165375523)
                  ·
                    refine ⟨28575989867557188248063285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19050659911704792165375523 28575989867557188248063285)
                    ·
                      refine ⟨2678999050083486398255933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28575989867557188248063285 2678999050083486398255933)
                      ·
                        rfl

theorem cell23_5217332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5217332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217332 prefixEnd_5217332 := by exact prefixLift 5217332
  have htrace : WordTrace (prefixWord ++ tailWord_5217332) baseStart_5217332 baseEnd_5217332 := by
    simpa [prefixWord, tailWord_5217332, baseEnd_5217332] using wordTrace_append hprefix tailTrace_5217332
  have hstable : (prefixWord ++ tailWord_5217332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217332).length < 2 ^ (prefixWord ++ tailWord_5217332).sum := by decide
  have hdescent : baseEnd_5217332 < baseStart_5217332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217352 : List Nat := [2, 1, 3, 1, 1, 1, 7, 2, 5]
def baseStart_5217352 : Nat := 118140960795 + 5217352 * 2 ^ 59
def prefixEnd_5217352 : Nat := 4983230072969 + 3 ^ 40 * 5217352 * 2
def baseEnd_5217352 : Nat := 297667702188508480000649

theorem tailTrace_5217352 : CollatzResearch.WordTrace tailWord_5217352 prefixEnd_5217352 297667702188508480000649 := by
  unfold tailWord_5217352
  simp only [CollatzResearch.WordTrace]
  refine ⟨95146230297216115813187155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126861640396288154417582873 95146230297216115813187155)
  ·
    refine ⟨142719345445824173719780733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95146230297216115813187155 142719345445824173719780733)
    ·
      refine ⟨53519754542184065144917775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142719345445824173719780733 53519754542184065144917775)
      ·
        refine ⟨80279631813276097717376663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53519754542184065144917775 80279631813276097717376663)
        ·
          refine ⟨120419447719914146576064995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80279631813276097717376663 120419447719914146576064995)
          ·
            refine ⟨180629171579871219864097493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120419447719914146576064995 180629171579871219864097493)
            ·
              refine ⟨4233496208903231715564785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 180629171579871219864097493 4233496208903231715564785)
              ·
                refine ⟨3175122156677423786673589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4233496208903231715564785 3175122156677423786673589)
                ·
                  refine ⟨297667702188508480000649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3175122156677423786673589 297667702188508480000649)
                  ·
                    rfl

theorem cell23_5217352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 5].length) (baseStart_5217352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217352 prefixEnd_5217352 := by exact prefixLift 5217352
  have htrace : WordTrace (prefixWord ++ tailWord_5217352) baseStart_5217352 baseEnd_5217352 := by
    simpa [prefixWord, tailWord_5217352, baseEnd_5217352] using wordTrace_append hprefix tailTrace_5217352
  have hstable : (prefixWord ++ tailWord_5217352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217352).length < 2 ^ (prefixWord ++ tailWord_5217352).sum := by decide
  have hdescent : baseEnd_5217352 < baseStart_5217352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217385 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_5217385 : Nat := 118140960795 + 5217385 * 2 ^ 59
def prefixEnd_5217385 : Nat := 4983230072969 + 3 ^ 40 * 5217385 * 2
def baseEnd_5217385 : Nat := 2679026264558174690893189

theorem tailTrace_5217385 : CollatzResearch.WordTrace tailWord_5217385 prefixEnd_5217385 2679026264558174690893189 := by
  unfold tailWord_5217385
  simp only [CollatzResearch.WordTrace]
  refine ⟨190293664203312678262325609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126862442802208452174883739 190293664203312678262325609)
  ·
    refine ⟨142720248152484508696744207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190293664203312678262325609 142720248152484508696744207)
    ·
      refine ⟨214080372228726763045116311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142720248152484508696744207 214080372228726763045116311)
      ·
        refine ⟨321120558343090144567674467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214080372228726763045116311 321120558343090144567674467)
        ·
          refine ⟨481680837514635216851511701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321120558343090144567674467 481680837514635216851511701)
          ·
            refine ⟨22578789258498525789914611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 481680837514635216851511701 22578789258498525789914611)
            ·
              refine ⟨33868183887747788684871917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22578789258498525789914611 33868183887747788684871917)
              ·
                refine ⟨12700568957905420756826969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33868183887747788684871917 12700568957905420756826969)
                ·
                  refine ⟨9525426718429065567620227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12700568957905420756826969 9525426718429065567620227)
                  ·
                    refine ⟨14288140077643598351430341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9525426718429065567620227 14288140077643598351430341)
                    ·
                      refine ⟨2679026264558174690893189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14288140077643598351430341 2679026264558174690893189)
                      ·
                        rfl

theorem cell23_5217385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_5217385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217385 prefixEnd_5217385 := by exact prefixLift 5217385
  have htrace : WordTrace (prefixWord ++ tailWord_5217385) baseStart_5217385 baseEnd_5217385 := by
    simpa [prefixWord, tailWord_5217385, baseEnd_5217385] using wordTrace_append hprefix tailTrace_5217385
  have hstable : (prefixWord ++ tailWord_5217385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217385).length < 2 ^ (prefixWord ++ tailWord_5217385).sum := by decide
  have hdescent : baseEnd_5217385 < baseStart_5217385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217408 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 8]
def baseStart_5217408 : Nat := 118140960795 + 5217408 * 2 ^ 59
def prefixEnd_5217408 : Nat := 4983230072969 + 3 ^ 40 * 5217408 * 2
def baseEnd_5217408 : Nat := 297670897179247566767287

theorem tailTrace_5217408 : CollatzResearch.WordTrace tailWord_5217408 prefixEnd_5217408 297670897179247566767287 := by
  unfold tailWord_5217408
  simp only [CollatzResearch.WordTrace]
  refine ⟨95147251541114676595206439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126863002054819568793608585 95147251541114676595206439)
  ·
    refine ⟨142720877311672014892809659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95147251541114676595206439 142720877311672014892809659)
    ·
      refine ⟨214081315967508022339214489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142720877311672014892809659 214081315967508022339214489)
      ·
        refine ⟨160560986975631016754410867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214081315967508022339214489 160560986975631016754410867)
        ·
          refine ⟨240841480463446525131616301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160560986975631016754410867 240841480463446525131616301)
          ·
            refine ⟨90315555173792446924356113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240841480463446525131616301 90315555173792446924356113)
            ·
              refine ⟨67736666380344335193267085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90315555173792446924356113 67736666380344335193267085)
              ·
                refine ⟨25401249892629125697475157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67736666380344335193267085 25401249892629125697475157)
                ·
                  refine ⟨297670897179247566767287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25401249892629125697475157 297670897179247566767287)
                  ·
                    rfl

theorem cell23_5217408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_5217408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217408 prefixEnd_5217408 := by exact prefixLift 5217408
  have htrace : WordTrace (prefixWord ++ tailWord_5217408) baseStart_5217408 baseEnd_5217408 := by
    simpa [prefixWord, tailWord_5217408, baseEnd_5217408] using wordTrace_append hprefix tailTrace_5217408
  have hstable : (prefixWord ++ tailWord_5217408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217408).length < 2 ^ (prefixWord ++ tailWord_5217408).sum := by decide
  have hdescent : baseEnd_5217408 < baseStart_5217408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217475 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 4]
def baseStart_5217475 : Nat := 118140960795 + 5217475 * 2 ^ 59
def prefixEnd_5217475 : Nat := 4983230072969 + 3 ^ 40 * 5217475 * 2
def baseEnd_5217475 : Nat := 2679072477817079338767775

theorem tailTrace_5217475 : CollatzResearch.WordTrace tailWord_5217475 prefixEnd_5217475 2679072477817079338767775 := by
  unfold tailWord_5217475
  simp only [CollatzResearch.WordTrace]
  refine ⟨190296946772986623633101879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126864631181991082422067919 190296946772986623633101879)
  ·
    refine ⟨285445420159479935449652819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190296946772986623633101879 285445420159479935449652819)
    ·
      refine ⟨428168130239219903174479229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285445420159479935449652819 428168130239219903174479229)
      ·
        refine ⟨160563048839707463690429711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428168130239219903174479229 160563048839707463690429711)
        ·
          refine ⟨240844573259561195535644567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160563048839707463690429711 240844573259561195535644567)
          ·
            refine ⟨361266859889341793303466851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240844573259561195535644567 361266859889341793303466851)
            ·
              refine ⟨541900289834012689955200277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361266859889341793303466851 541900289834012689955200277)
              ·
                refine ⟨25401576085969344841650013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 541900289834012689955200277 25401576085969344841650013)
                ·
                  refine ⟨9525591032238504315618755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25401576085969344841650013 9525591032238504315618755)
                  ·
                    refine ⟨14288386548357756473428133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9525591032238504315618755 14288386548357756473428133)
                    ·
                      refine ⟨2679072477817079338767775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14288386548357756473428133 2679072477817079338767775)
                      ·
                        rfl

theorem cell23_5217475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_5217475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217475 prefixEnd_5217475 := by exact prefixLift 5217475
  have htrace : WordTrace (prefixWord ++ tailWord_5217475) baseStart_5217475 baseEnd_5217475 := by
    simpa [prefixWord, tailWord_5217475, baseEnd_5217475] using wordTrace_append hprefix tailTrace_5217475
  have hstable : (prefixWord ++ tailWord_5217475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217475).length < 2 ^ (prefixWord ++ tailWord_5217475).sum := by decide
  have hdescent : baseEnd_5217475 < baseStart_5217475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217512 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_5217512 : Nat := 118140960795 + 5217512 * 2 ^ 59
def prefixEnd_5217512 : Nat := 4983230072969 + 3 ^ 40 * 5217512 * 2
def baseEnd_5217512 : Nat := 2679091476601295694005105

theorem tailTrace_5217512 : CollatzResearch.WordTrace tailWord_5217512 prefixEnd_5217512 2679091476601295694005105 := by
  unfold tailWord_5217512
  simp only [CollatzResearch.WordTrace]
  refine ⟨95149148136926289476099395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126865530849235052634799193 95149148136926289476099395)
  ·
    refine ⟨142723722205389434214149093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95149148136926289476099395 142723722205389434214149093)
    ·
      refine ⟨26760697913510518915152955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142723722205389434214149093 26760697913510518915152955)
      ·
        refine ⟨40141046870265778372729433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26760697913510518915152955 40141046870265778372729433)
        ·
          refine ⟨30105785152699333779547075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40141046870265778372729433 30105785152699333779547075)
          ·
            refine ⟨45158677729049000669320613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30105785152699333779547075 45158677729049000669320613)
            ·
              refine ⟨8467252074196687625497615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45158677729049000669320613 8467252074196687625497615)
              ·
                refine ⟨12700878111295031438246423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8467252074196687625497615 12700878111295031438246423)
                ·
                  refine ⟨19051317166942547157369635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12700878111295031438246423 19051317166942547157369635)
                  ·
                    refine ⟨28576975750413820736054453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19051317166942547157369635 28576975750413820736054453)
                    ·
                      refine ⟨2679091476601295694005105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28576975750413820736054453 2679091476601295694005105)
                      ·
                        rfl

theorem cell23_5217512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_5217512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217512 prefixEnd_5217512 := by exact prefixLift 5217512
  have htrace : WordTrace (prefixWord ++ tailWord_5217512) baseStart_5217512 baseEnd_5217512 := by
    simpa [prefixWord, tailWord_5217512, baseEnd_5217512] using wordTrace_append hprefix tailTrace_5217512
  have hstable : (prefixWord ++ tailWord_5217512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217512).length < 2 ^ (prefixWord ++ tailWord_5217512).sum := by decide
  have hdescent : baseEnd_5217512 < baseStart_5217512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217515 : List Nat := [1, 1, 1, 1, 2, 8, 9]
def baseStart_5217515 : Nat := 118140960795 + 5217515 * 2 ^ 59
def prefixEnd_5217515 : Nat := 4983230072969 + 3 ^ 40 * 5217515 * 2
def baseEnd_5217515 : Nat := 33075222432632829410711

theorem tailTrace_5217515 : CollatzResearch.WordTrace tailWord_5217515 prefixEnd_5217515 33075222432632829410711 := by
  unfold tailWord_5217515
  simp only [CollatzResearch.WordTrace]
  refine ⟨190298405692841710464557999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126865603795227806976371999 190298405692841710464557999)
  ·
    refine ⟨285447608539262565696836999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190298405692841710464557999 285447608539262565696836999)
    ·
      refine ⟨428171412808893848545255499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285447608539262565696836999 428171412808893848545255499)
      ·
        refine ⟨642257119213340772817883249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428171412808893848545255499 642257119213340772817883249)
        ·
          refine ⟨481692839410005579613412437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642257119213340772817883249 481692839410005579613412437)
          ·
            refine ⟨5644837961836002886094677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 481692839410005579613412437 5644837961836002886094677)
            ·
              refine ⟨33075222432632829410711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5644837961836002886094677 33075222432632829410711)
              ·
                rfl

theorem cell23_5217515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 9].length) (baseStart_5217515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217515 prefixEnd_5217515 := by exact prefixLift 5217515
  have htrace : WordTrace (prefixWord ++ tailWord_5217515) baseStart_5217515 baseEnd_5217515 := by
    simpa [prefixWord, tailWord_5217515, baseEnd_5217515] using wordTrace_append hprefix tailTrace_5217515
  have hstable : (prefixWord ++ tailWord_5217515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217515).length < 2 ^ (prefixWord ++ tailWord_5217515).sum := by decide
  have hdescent : baseEnd_5217515 < baseStart_5217515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217532 : List Nat := [2, 2, 2, 1, 5, 1, 2, 8]
def baseStart_5217532 : Nat := 118140960795 + 5217532 * 2 ^ 59
def prefixEnd_5217532 : Nat := 4983230072969 + 3 ^ 40 * 5217532 * 2
def baseEnd_5217532 : Nat := 99225990600532800583519

theorem tailTrace_5217532 : CollatzResearch.WordTrace tailWord_5217532 prefixEnd_5217532 99225990600532800583519 := by
  unfold tailWord_5217532
  simp only [CollatzResearch.WordTrace]
  refine ⟨95149512866890061183963425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126866017155853414911951233 95149512866890061183963425)
  ·
    refine ⟨71362134650167545887972569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95149512866890061183963425 71362134650167545887972569)
    ·
      refine ⟨53521600987625659415979427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71362134650167545887972569 53521600987625659415979427)
      ·
        refine ⟨80282401481438489123969141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53521600987625659415979427 80282401481438489123969141)
        ·
          refine ⟨7526475138884858355372107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80282401481438489123969141 7526475138884858355372107)
          ·
            refine ⟨11289712708327287533058161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7526475138884858355372107 11289712708327287533058161)
            ·
              refine ⟨8467284531245465649793621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11289712708327287533058161 8467284531245465649793621)
              ·
                refine ⟨99225990600532800583519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8467284531245465649793621 99225990600532800583519)
                ·
                  rfl

theorem cell23_5217532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 8].length) (baseStart_5217532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217532 prefixEnd_5217532 := by exact prefixLift 5217532
  have htrace : WordTrace (prefixWord ++ tailWord_5217532) baseStart_5217532 baseEnd_5217532 := by
    simpa [prefixWord, tailWord_5217532, baseEnd_5217532] using wordTrace_append hprefix tailTrace_5217532
  have hstable : (prefixWord ++ tailWord_5217532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217532).length < 2 ^ (prefixWord ++ tailWord_5217532).sum := by decide
  have hdescent : baseEnd_5217532 < baseStart_5217532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217576 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_5217576 : Nat := 118140960795 + 5217576 * 2 ^ 59
def prefixEnd_5217576 : Nat := 4983230072969 + 3 ^ 40 * 5217576 * 2
def baseEnd_5217576 : Nat := 2679124339363183443604811

theorem tailTrace_5217576 : CollatzResearch.WordTrace tailWord_5217576 prefixEnd_5217576 2679124339363183443604811 := by
  unfold tailWord_5217576
  simp only [CollatzResearch.WordTrace]
  refine ⟨95150315272810358941264291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126867087030413811921685721 95150315272810358941264291)
  ·
    refine ⟨142725472909215538411896437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95150315272810358941264291 142725472909215538411896437)
    ·
      refine ⟨13380513085238956726115291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142725472909215538411896437 13380513085238956726115291)
      ·
        refine ⟨20070769627858435089172937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13380513085238956726115291 20070769627858435089172937)
        ·
          refine ⟨15053077220893826316879703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20070769627858435089172937 15053077220893826316879703)
          ·
            refine ⟨22579615831340739475319555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15053077220893826316879703 22579615831340739475319555)
            ·
              refine ⟨33869423747011109212979333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22579615831340739475319555 33869423747011109212979333)
              ·
                refine ⟨6350516952564582977433625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33869423747011109212979333 6350516952564582977433625)
                ·
                  refine ⟨4762887714423437233075219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6350516952564582977433625 4762887714423437233075219)
                  ·
                    refine ⟨7144331571635155849612829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4762887714423437233075219 7144331571635155849612829)
                    ·
                      refine ⟨2679124339363183443604811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7144331571635155849612829 2679124339363183443604811)
                      ·
                        rfl

theorem cell23_5217576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_5217576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217576 prefixEnd_5217576 := by exact prefixLift 5217576
  have htrace : WordTrace (prefixWord ++ tailWord_5217576) baseStart_5217576 baseEnd_5217576 := by
    simpa [prefixWord, tailWord_5217576, baseEnd_5217576] using wordTrace_append hprefix tailTrace_5217576
  have hstable : (prefixWord ++ tailWord_5217576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217576).length < 2 ^ (prefixWord ++ tailWord_5217576).sum := by decide
  have hdescent : baseEnd_5217576 < baseStart_5217576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217599 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 1, 4, 2]
def baseStart_5217599 : Nat := 118140960795 + 5217599 * 2 ^ 59
def prefixEnd_5217599 : Nat := 4983230072969 + 3 ^ 40 * 5217599 * 2
def baseEnd_5217599 : Nat := 2679136149418236853617205

theorem tailTrace_5217599 : CollatzResearch.WordTrace tailWord_5217599 prefixEnd_5217599 2679136149418236853617205 := by
  unfold tailWord_5217599
  simp only [CollatzResearch.WordTrace]
  refine ⟨190301469424537392810615851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126867646283024928540410567 190301469424537392810615851)
  ·
    refine ⟨285452204136806089215923777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190301469424537392810615851 285452204136806089215923777)
    ·
      refine ⟨214089153102604566911942833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285452204136806089215923777 214089153102604566911942833)
      ·
        refine ⟨160566864826953425183957125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214089153102604566911942833 160566864826953425183957125)
        ·
          refine ⟨30106287155053767221991961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160566864826953425183957125 30106287155053767221991961)
          ·
            refine ⟨22579715366290325416493971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30106287155053767221991961 22579715366290325416493971)
            ·
              refine ⟨33869573049435488124740957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22579715366290325416493971 33869573049435488124740957)
              ·
                refine ⟨12701089893538308046777859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33869573049435488124740957 12701089893538308046777859)
                ·
                  refine ⟨19051634840307462070166789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12701089893538308046777859 19051634840307462070166789)
                  ·
                    refine ⟨3572181532557649138156273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19051634840307462070166789 3572181532557649138156273)
                    ·
                      refine ⟨2679136149418236853617205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572181532557649138156273 2679136149418236853617205)
                      ·
                        rfl

theorem cell23_5217599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_5217599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217599 prefixEnd_5217599 := by exact prefixLift 5217599
  have htrace : WordTrace (prefixWord ++ tailWord_5217599) baseStart_5217599 baseEnd_5217599 := by
    simpa [prefixWord, tailWord_5217599, baseEnd_5217599] using wordTrace_append hprefix tailTrace_5217599
  have hstable : (prefixWord ++ tailWord_5217599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217599).length < 2 ^ (prefixWord ++ tailWord_5217599).sum := by decide
  have hdescent : baseEnd_5217599 < baseStart_5217599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217639 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 7]
def baseStart_5217639 : Nat := 118140960795 + 5217639 * 2 ^ 59
def prefixEnd_5217639 : Nat := 4983230072969 + 3 ^ 40 * 5217639 * 2
def baseEnd_5217639 : Nat := 297684076516046299679669

theorem tailTrace_5217639 : CollatzResearch.WordTrace tailWord_5217639 prefixEnd_5217639 297684076516046299679669 := by
  unfold tailWord_5217639
  simp only [CollatzResearch.WordTrace]
  refine ⟨190302928344392479642071971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126868618896261653094714647 190302928344392479642071971)
  ·
    refine ⟨285454392516588719463107957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190302928344392479642071971 285454392516588719463107957)
    ·
      refine ⟨26761349298430192449666371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285454392516588719463107957 26761349298430192449666371)
      ·
        refine ⟨40142023947645288674499557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26761349298430192449666371 40142023947645288674499557)
        ·
          refine ⟨7526629490183491626468667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40142023947645288674499557 7526629490183491626468667)
          ·
            refine ⟨11289944235275237439703001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7526629490183491626468667 11289944235275237439703001)
            ·
              refine ⟨8467458176456428079777251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11289944235275237439703001 8467458176456428079777251)
              ·
                refine ⟨12701187264684642119665877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8467458176456428079777251 12701187264684642119665877)
                ·
                  refine ⟨297684076516046299679669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12701187264684642119665877 297684076516046299679669)
                  ·
                    rfl

theorem cell23_5217639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 7].length) (baseStart_5217639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217639 prefixEnd_5217639 := by exact prefixLift 5217639
  have htrace : WordTrace (prefixWord ++ tailWord_5217639) baseStart_5217639 baseEnd_5217639 := by
    simpa [prefixWord, tailWord_5217639, baseEnd_5217639] using wordTrace_append hprefix tailTrace_5217639
  have hstable : (prefixWord ++ tailWord_5217639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217639).length < 2 ^ (prefixWord ++ tailWord_5217639).sum := by decide
  have hdescent : baseEnd_5217639 < baseStart_5217639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217673 : List Nat := [1, 2, 1, 1, 8, 1, 1, 3, 5]
def baseStart_5217673 : Nat := 118140960795 + 5217673 * 2 ^ 59
def prefixEnd_5217673 : Nat := 4983230072969 + 3 ^ 40 * 5217673 * 2
def baseEnd_5217673 : Nat := 297686016331852173787985

theorem tailTrace_5217673 : CollatzResearch.WordTrace tailWord_5217673 prefixEnd_5217673 297686016331852173787985 := by
  unfold tailWord_5217673
  simp only [CollatzResearch.WordTrace]
  refine ⟨190304168426269303448809673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126869445617512868965873115 190304168426269303448809673)
  ·
    refine ⟨142728126319701977586607255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190304168426269303448809673 142728126319701977586607255)
    ·
      refine ⟨214092189479552966379910883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142728126319701977586607255 214092189479552966379910883)
      ·
        refine ⟨321138284219329449569866325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214092189479552966379910883 321138284219329449569866325)
        ·
          refine ⟨3763339268195266987146871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 321138284219329449569866325 3763339268195266987146871)
          ·
            refine ⟨5645008902292900480720307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763339268195266987146871 5645008902292900480720307)
            ·
              refine ⟨8467513353439350721080461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645008902292900480720307 8467513353439350721080461)
              ·
                refine ⟨3175317507539756520405173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8467513353439350721080461 3175317507539756520405173)
                ·
                  refine ⟨297686016331852173787985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3175317507539756520405173 297686016331852173787985)
                  ·
                    rfl

theorem cell23_5217673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 5].length) (baseStart_5217673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217673 prefixEnd_5217673 := by exact prefixLift 5217673
  have htrace : WordTrace (prefixWord ++ tailWord_5217673) baseStart_5217673 baseEnd_5217673 := by
    simpa [prefixWord, tailWord_5217673, baseEnd_5217673] using wordTrace_append hprefix tailTrace_5217673
  have hstable : (prefixWord ++ tailWord_5217673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217673).length < 2 ^ (prefixWord ++ tailWord_5217673).sum := by decide
  have hdescent : baseEnd_5217673 < baseStart_5217673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217689 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_5217689 : Nat := 118140960795 + 5217689 * 2 ^ 59
def prefixEnd_5217689 : Nat := 4983230072969 + 3 ^ 40 * 5217689 * 2
def baseEnd_5217689 : Nat := 2679182362677141501491791

theorem tailTrace_5217689 : CollatzResearch.WordTrace tailWord_5217689 prefixEnd_5217689 2679182362677141501491791 := by
  unfold tailWord_5217689
  simp only [CollatzResearch.WordTrace]
  refine ⟨190304751994211338181392121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126869834662807558787594747 190304751994211338181392121)
  ·
    refine ⟨142728563995658503636044091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190304751994211338181392121 142728563995658503636044091)
    ·
      refine ⟨214092845993487755454066137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142728563995658503636044091 214092845993487755454066137)
      ·
        refine ⟨160569634495115816590549603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214092845993487755454066137 160569634495115816590549603)
        ·
          refine ⟨240854451742673724885824405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160569634495115816590549603 240854451742673724885824405)
          ·
            refine ⟨11290052425437830854023019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 240854451742673724885824405 11290052425437830854023019)
            ·
              refine ⟨16935078638156746281034529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11290052425437830854023019 16935078638156746281034529)
              ·
                refine ⟨12701308978617559710775897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16935078638156746281034529 12701308978617559710775897)
                ·
                  refine ⟨9525981733963169783081923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12701308978617559710775897 9525981733963169783081923)
                  ·
                    refine ⟨14288972600944754674622885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9525981733963169783081923 14288972600944754674622885)
                    ·
                      refine ⟨2679182362677141501491791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14288972600944754674622885 2679182362677141501491791)
                      ·
                        rfl

theorem cell23_5217689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_5217689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217689 prefixEnd_5217689 := by exact prefixLift 5217689
  have htrace : WordTrace (prefixWord ++ tailWord_5217689) baseStart_5217689 baseEnd_5217689 := by
    simpa [prefixWord, tailWord_5217689, baseEnd_5217689] using wordTrace_append hprefix tailTrace_5217689
  have hstable : (prefixWord ++ tailWord_5217689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217689).length < 2 ^ (prefixWord ++ tailWord_5217689).sum := by decide
  have hdescent : baseEnd_5217689 < baseStart_5217689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217750 : List Nat := [5, 2, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_5217750 : Nat := 118140960795 + 5217750 * 2 ^ 59
def prefixEnd_5217750 : Nat := 4983230072969 + 3 ^ 40 * 5217750 * 2
def baseEnd_5217750 : Nat := 893071228332355254276337

theorem tailTrace_5217750 : CollatzResearch.WordTrace tailWord_5217750 prefixEnd_5217750 893071228332355254276337 := by
  unfold tailWord_5217750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894186052936896599960169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126871317897993563732908469 11894186052936896599960169)
  ·
    refine ⟨8920639539702672449970127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11894186052936896599960169 8920639539702672449970127)
    ·
      refine ⟨13380959309554008674955191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8920639539702672449970127 13380959309554008674955191)
      ·
        refine ⟨20071438964331013012432787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13380959309554008674955191 20071438964331013012432787)
        ·
          refine ⟨30107158446496519518649181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20071438964331013012432787 30107158446496519518649181)
          ·
            refine ⟨11290184417436194819493443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30107158446496519518649181 11290184417436194819493443)
            ·
              refine ⟨16935276626154292229240165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11290184417436194819493443 16935276626154292229240165)
              ·
                refine ⟨3175364367403929792982531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16935276626154292229240165 3175364367403929792982531)
                ·
                  refine ⟨4763046551105894689473797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175364367403929792982531 4763046551105894689473797)
                  ·
                    refine ⟨893071228332355254276337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763046551105894689473797 893071228332355254276337)
                    ·
                      rfl

theorem cell23_5217750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_5217750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217750 prefixEnd_5217750 := by exact prefixLift 5217750
  have htrace : WordTrace (prefixWord ++ tailWord_5217750) baseStart_5217750 baseEnd_5217750 := by
    simpa [prefixWord, tailWord_5217750, baseEnd_5217750] using wordTrace_append hprefix tailTrace_5217750
  have hstable : (prefixWord ++ tailWord_5217750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217750).length < 2 ^ (prefixWord ++ tailWord_5217750).sum := by decide
  have hdescent : baseEnd_5217750 < baseStart_5217750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217779 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 8, 2]
def baseStart_5217779 : Nat := 118140960795 + 5217779 * 2 ^ 59
def prefixEnd_5217779 : Nat := 4983230072969 + 3 ^ 40 * 5217779 * 2
def baseEnd_5217779 : Nat := 2679228575936046149366377

theorem tailTrace_5217779 : CollatzResearch.WordTrace tailWord_5217779 prefixEnd_5217779 2679228575936046149366377 := by
  unfold tailWord_5217779
  simp only [CollatzResearch.WordTrace]
  refine ⟨190308034563885283552168391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126872023042590189034778927 190308034563885283552168391)
  ·
    refine ⟨285462051845827925328252587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190308034563885283552168391 285462051845827925328252587)
    ·
      refine ⟨428193077768741887992378881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285462051845827925328252587 428193077768741887992378881)
      ·
        refine ⟨321144808326556415994284161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428193077768741887992378881 321144808326556415994284161)
        ·
          refine ⟨240858606244917311995713121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321144808326556415994284161 240858606244917311995713121)
          ·
            refine ⟨180643954683687983996784841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240858606244917311995713121 180643954683687983996784841)
            ·
              refine ⟨135482966012765987997588631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180643954683687983996784841 135482966012765987997588631)
              ·
                refine ⟨203224449019148981996382947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135482966012765987997588631 203224449019148981996382947)
                ·
                  refine ⟨304836673528723472994574421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203224449019148981996382947 304836673528723472994574421)
                  ·
                    refine ⟨3572304767914728199155169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 304836673528723472994574421 3572304767914728199155169)
                    ·
                      refine ⟨2679228575936046149366377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572304767914728199155169 2679228575936046149366377)
                      ·
                        rfl

theorem cell23_5217779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8, 2].length) (baseStart_5217779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217779 prefixEnd_5217779 := by exact prefixLift 5217779
  have htrace : WordTrace (prefixWord ++ tailWord_5217779) baseStart_5217779 baseEnd_5217779 := by
    simpa [prefixWord, tailWord_5217779, baseEnd_5217779] using wordTrace_append hprefix tailTrace_5217779
  have hstable : (prefixWord ++ tailWord_5217779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217779).length < 2 ^ (prefixWord ++ tailWord_5217779).sum := by decide
  have hdescent : baseEnd_5217779 < baseStart_5217779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217789 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_5217789 : Nat := 118140960795 + 5217789 * 2 ^ 59
def prefixEnd_5217789 : Nat := 4983230072969 + 3 ^ 40 * 5217789 * 2
def baseEnd_5217789 : Nat := 893077903580863703413777

theorem tailTrace_5217789 : CollatzResearch.WordTrace tailWord_5217789 prefixEnd_5217789 893077903580863703413777 := by
  unfold tailWord_5217789
  simp only [CollatzResearch.WordTrace]
  refine ⟨190308399293849055260032421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126872266195899370173354947 190308399293849055260032421)
  ·
    refine ⟨35682824867596697861256079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190308399293849055260032421 35682824867596697861256079)
    ·
      refine ⟨53524237301395046791884119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35682824867596697861256079 53524237301395046791884119)
      ·
        refine ⟨80286355952092570187826179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53524237301395046791884119 80286355952092570187826179)
        ·
          refine ⟨120429533928138855281739269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80286355952092570187826179 120429533928138855281739269)
          ·
            refine ⟨22580537611526035365326113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120429533928138855281739269 22580537611526035365326113)
            ·
              refine ⟨16935403208644526523994585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22580537611526035365326113 16935403208644526523994585)
              ·
                refine ⟨12701552406483394892995939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16935403208644526523994585 12701552406483394892995939)
                ·
                  refine ⟨19052328609725092339493909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12701552406483394892995939 19052328609725092339493909)
                  ·
                    refine ⟨893077903580863703413777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19052328609725092339493909 893077903580863703413777)
                    ·
                      rfl

theorem cell23_5217789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_5217789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217789 prefixEnd_5217789 := by exact prefixLift 5217789
  have htrace : WordTrace (prefixWord ++ tailWord_5217789) baseStart_5217789 baseEnd_5217789 := by
    simpa [prefixWord, tailWord_5217789, baseEnd_5217789] using wordTrace_append hprefix tailTrace_5217789
  have hstable : (prefixWord ++ tailWord_5217789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217789).length < 2 ^ (prefixWord ++ tailWord_5217789).sum := by decide
  have hdescent : baseEnd_5217789 < baseStart_5217789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217813 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_5217813 : Nat := 118140960795 + 5217813 * 2 ^ 59
def prefixEnd_5217813 : Nat := 4983230072969 + 3 ^ 40 * 5217813 * 2
def baseEnd_5217813 : Nat := 2679246034278299016341221

theorem tailTrace_5217813 : CollatzResearch.WordTrace tailWord_5217813 prefixEnd_5217813 2679246034278299016341221 := by
  unfold tailWord_5217813
  simp only [CollatzResearch.WordTrace]
  refine ⟨190309274645762107358906093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126872849763841404905937395 190309274645762107358906093)
  ·
    refine ⟨71365977992160790259589785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190309274645762107358906093 71365977992160790259589785)
    ·
      refine ⟨53524483494120592694692339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71365977992160790259589785 53524483494120592694692339)
      ·
        refine ⟨80286725241180889042038509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53524483494120592694692339 80286725241180889042038509)
        ·
          refine ⟨30107521965442833390764441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80286725241180889042038509 30107521965442833390764441)
          ·
            refine ⟨22580641474082125043073331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30107521965442833390764441 22580641474082125043073331)
            ·
              refine ⟨33870962211123187564609997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22580641474082125043073331 33870962211123187564609997)
              ·
                refine ⟨12701610829171195336728749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33870962211123187564609997 12701610829171195336728749)
                ·
                  refine ⟨4763104060939198251273281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12701610829171195336728749 4763104060939198251273281)
                  ·
                    refine ⟨3572328045704398688454961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763104060939198251273281 3572328045704398688454961)
                    ·
                      refine ⟨2679246034278299016341221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572328045704398688454961 2679246034278299016341221)
                      ·
                        rfl

theorem cell23_5217813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_5217813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217813 prefixEnd_5217813 := by exact prefixLift 5217813
  have htrace : WordTrace (prefixWord ++ tailWord_5217813) baseStart_5217813 baseEnd_5217813 := by
    simpa [prefixWord, tailWord_5217813, baseEnd_5217813] using wordTrace_append hprefix tailTrace_5217813
  have hstable : (prefixWord ++ tailWord_5217813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217813).length < 2 ^ (prefixWord ++ tailWord_5217813).sum := by decide
  have hdescent : baseEnd_5217813 < baseStart_5217813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217816 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_5217816 : Nat := 118140960795 + 5217816 * 2 ^ 59
def prefixEnd_5217816 : Nat := 4983230072969 + 3 ^ 40 * 5217816 * 2
def baseEnd_5217816 : Nat := 2679247574720262504603707

theorem tailTrace_5217816 : CollatzResearch.WordTrace tailWord_5217816 prefixEnd_5217816 2679247574720262504603707 := by
  unfold tailWord_5217816
  simp only [CollatzResearch.WordTrace]
  refine ⟨95154692032375619435632651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126872922709834159247510201 95154692032375619435632651)
  ·
    refine ⟨142732038048563429153448977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95154692032375619435632651 142732038048563429153448977)
    ·
      refine ⟨107049028536422571865086733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142732038048563429153448977 107049028536422571865086733)
      ·
        refine ⟨40143385701158464449407525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107049028536422571865086733 40143385701158464449407525)
        ·
          refine ⟨7526884818967212084263911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40143385701158464449407525 7526884818967212084263911)
          ·
            refine ⟨11290327228450818126395867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7526884818967212084263911 11290327228450818126395867)
            ·
              refine ⟨16935490842676227189593801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11290327228450818126395867 16935490842676227189593801)
              ·
                refine ⟨12701618132007170392195351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16935490842676227189593801 12701618132007170392195351)
                ·
                  refine ⟨19052427198010755588293027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12701618132007170392195351 19052427198010755588293027)
                  ·
                    refine ⟨28578640797016133382439541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19052427198010755588293027 28578640797016133382439541)
                    ·
                      refine ⟨2679247574720262504603707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28578640797016133382439541 2679247574720262504603707)
                      ·
                        rfl

theorem cell23_5217816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_5217816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217816 prefixEnd_5217816 := by exact prefixLift 5217816
  have htrace : WordTrace (prefixWord ++ tailWord_5217816) baseStart_5217816 baseEnd_5217816 := by
    simpa [prefixWord, tailWord_5217816, baseEnd_5217816] using wordTrace_append hprefix tailTrace_5217816
  have hstable : (prefixWord ++ tailWord_5217816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217816).length < 2 ^ (prefixWord ++ tailWord_5217816).sum := by decide
  have hdescent : baseEnd_5217816 < baseStart_5217816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217826 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_5217826 : Nat := 118140960795 + 5217826 * 2 ^ 59
def prefixEnd_5217826 : Nat := 4983230072969 + 3 ^ 40 * 5217826 * 2
def baseEnd_5217826 : Nat := 2679252709526807465478661

theorem tailTrace_5217826 : CollatzResearch.WordTrace tailWord_5217826 prefixEnd_5217826 2679252709526807465478661 := by
  unfold tailWord_5217826
  simp only [CollatzResearch.WordTrace]
  refine ⟨47577437198678752644782333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126873165863143340386086221 47577437198678752644782333)
  ·
    refine ⟨17841538949504532241793375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47577437198678752644782333 17841538949504532241793375)
    ·
      refine ⟨26762308424256798362690063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17841538949504532241793375 26762308424256798362690063)
      ·
        refine ⟨40143462636385197544035095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26762308424256798362690063 40143462636385197544035095)
        ·
          refine ⟨60215193954577796316052643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40143462636385197544035095 60215193954577796316052643)
          ·
            refine ⟨90322790931866694474078965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60215193954577796316052643 90322790931866694474078965)
            ·
              refine ⟨8467761649862502606944903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90322790931866694474078965 8467761649862502606944903)
              ·
                refine ⟨12701642474793753910417355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8467761649862502606944903 12701642474793753910417355)
                ·
                  refine ⟨19052463712190630865626033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12701642474793753910417355 19052463712190630865626033)
                  ·
                    refine ⟨14289347784142973149219525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19052463712190630865626033 14289347784142973149219525)
                    ·
                      refine ⟨2679252709526807465478661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14289347784142973149219525 2679252709526807465478661)
                      ·
                        rfl

theorem cell23_5217826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_5217826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217826 prefixEnd_5217826 := by exact prefixLift 5217826
  have htrace : WordTrace (prefixWord ++ tailWord_5217826) baseStart_5217826 baseEnd_5217826 := by
    simpa [prefixWord, tailWord_5217826, baseEnd_5217826] using wordTrace_append hprefix tailTrace_5217826
  have hstable : (prefixWord ++ tailWord_5217826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217826).length < 2 ^ (prefixWord ++ tailWord_5217826).sum := by decide
  have hdescent : baseEnd_5217826 < baseStart_5217826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217847 : List Nat := [1, 1, 3, 1, 2, 6, 1, 3, 1, 2, 2]
def baseStart_5217847 : Nat := 118140960795 + 5217847 * 2 ^ 59
def prefixEnd_5217847 : Nat := 4983230072969 + 3 ^ 40 * 5217847 * 2
def baseEnd_5217847 : Nat := 2679263492620551883316065

theorem tailTrace_5217847 : CollatzResearch.WordTrace tailWord_5217847 prefixEnd_5217847 2679263492620551883316065 := by
  unfold tailWord_5217847
  simp only [CollatzResearch.WordTrace]
  refine ⟨190310514727638931165643795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126873676485092620777095863 190310514727638931165643795)
  ·
    refine ⟨285465772091458396748465693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190310514727638931165643795 285465772091458396748465693)
    ·
      refine ⟨107049664534296898780674635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285465772091458396748465693 107049664534296898780674635)
      ·
        refine ⟨160574496801445348171011953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107049664534296898780674635 160574496801445348171011953)
        ·
          refine ⟨120430872601084011128258965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160574496801445348171011953 120430872601084011128258965)
          ·
            refine ⟨5645197153175813021637139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120430872601084011128258965 5645197153175813021637139)
            ·
              refine ⟨8467795729763719532455709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645197153175813021637139 8467795729763719532455709)
              ·
                refine ⟨3175423398661394824670891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8467795729763719532455709 3175423398661394824670891)
                ·
                  refine ⟨4763135097992092237006337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175423398661394824670891 4763135097992092237006337)
                  ·
                    refine ⟨3572351323494069177754753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763135097992092237006337 3572351323494069177754753)
                    ·
                      refine ⟨2679263492620551883316065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572351323494069177754753 2679263492620551883316065)
                      ·
                        rfl

theorem cell23_5217847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_5217847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217847 prefixEnd_5217847 := by exact prefixLift 5217847
  have htrace : WordTrace (prefixWord ++ tailWord_5217847) baseStart_5217847 baseEnd_5217847 := by
    simpa [prefixWord, tailWord_5217847, baseEnd_5217847] using wordTrace_append hprefix tailTrace_5217847
  have hstable : (prefixWord ++ tailWord_5217847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217847).length < 2 ^ (prefixWord ++ tailWord_5217847).sum := by decide
  have hdescent : baseEnd_5217847 < baseStart_5217847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217856 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 5, 3, 2]
def baseStart_5217856 : Nat := 118140960795 + 5217856 * 2 ^ 59
def prefixEnd_5217856 : Nat := 4983230072969 + 3 ^ 40 * 5217856 * 2
def baseEnd_5217856 : Nat := 2679268113946442348103523

theorem tailTrace_5217856 : CollatzResearch.WordTrace tailWord_5217856 prefixEnd_5217856 2679268113946442348103523 := by
  unfold tailWord_5217856
  simp only [CollatzResearch.WordTrace]
  refine ⟨95155421492303162851360711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126873895323070883801814281 95155421492303162851360711)
  ·
    refine ⟨142733132238454744277041067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95155421492303162851360711 142733132238454744277041067)
    ·
      refine ⟨214099698357682116415561601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142733132238454744277041067 214099698357682116415561601)
      ·
        refine ⟨160574773768261587311671201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214099698357682116415561601 160574773768261587311671201)
        ·
          refine ⟨120431080326196190483753401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160574773768261587311671201 120431080326196190483753401)
          ·
            refine ⟨90323310244647142862815051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120431080326196190483753401 90323310244647142862815051)
            ·
              refine ⟨135484965366970714294222577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90323310244647142862815051 135484965366970714294222577)
              ·
                refine ⟨101613724025228035720666933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135484965366970714294222577 101613724025228035720666933)
                ·
                  refine ⟨9526286627365128348812525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101613724025228035720666933 9526286627365128348812525)
                  ·
                    refine ⟨3572357485261923130804697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9526286627365128348812525 3572357485261923130804697)
                    ·
                      refine ⟨2679268113946442348103523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572357485261923130804697 2679268113946442348103523)
                      ·
                        rfl

theorem cell23_5217856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_5217856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217856 prefixEnd_5217856 := by exact prefixLift 5217856
  have htrace : WordTrace (prefixWord ++ tailWord_5217856) baseStart_5217856 baseEnd_5217856 := by
    simpa [prefixWord, tailWord_5217856, baseEnd_5217856] using wordTrace_append hprefix tailTrace_5217856
  have hstable : (prefixWord ++ tailWord_5217856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217856).length < 2 ^ (prefixWord ++ tailWord_5217856).sum := by decide
  have hdescent : baseEnd_5217856 < baseStart_5217856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217889 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_5217889 : Nat := 118140960795 + 5217889 * 2 ^ 59
def prefixEnd_5217889 : Nat := 4983230072969 + 3 ^ 40 * 5217889 * 2
def baseEnd_5217889 : Nat := 2679285058808040718990871

theorem tailTrace_5217889 : CollatzResearch.WordTrace tailWord_5217889 prefixEnd_5217889 2679285058808040718990871 := by
  unfold tailWord_5217889
  simp only [CollatzResearch.WordTrace]
  refine ⟨190312046593486772338672721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126874697728991181559115147 190312046593486772338672721)
  ·
    refine ⟨142734034945115079254004541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190312046593486772338672721 142734034945115079254004541)
    ·
      refine ⟨53525263104418154720251703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142734034945115079254004541 53525263104418154720251703)
      ·
        refine ⟨80287894656627232080377555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53525263104418154720251703 80287894656627232080377555)
        ·
          refine ⟨120431841984940848120566333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80287894656627232080377555 120431841984940848120566333)
          ·
            refine ⟨45161940744352818045212375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120431841984940848120566333 45161940744352818045212375)
            ·
              refine ⟨67742911116529227067818563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45161940744352818045212375 67742911116529227067818563)
              ·
                refine ⟨101614366674793840601727845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67742911116529227067818563 101614366674793840601727845)
                ·
                  refine ⟨19052693751523845112823971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101614366674793840601727845 19052693751523845112823971)
                  ·
                    refine ⟨28579040627285767669235957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19052693751523845112823971 28579040627285767669235957)
                    ·
                      refine ⟨2679285058808040718990871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28579040627285767669235957 2679285058808040718990871)
                      ·
                        rfl

theorem cell23_5217889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_5217889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217889 prefixEnd_5217889 := by exact prefixLift 5217889
  have htrace : WordTrace (prefixWord ++ tailWord_5217889) baseStart_5217889 baseEnd_5217889 := by
    simpa [prefixWord, tailWord_5217889, baseEnd_5217889] using wordTrace_append hprefix tailTrace_5217889
  have hstable : (prefixWord ++ tailWord_5217889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217889).length < 2 ^ (prefixWord ++ tailWord_5217889).sum := by decide
  have hdescent : baseEnd_5217889 < baseStart_5217889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217906 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5217906 : Nat := 118140960795 + 5217906 * 2 ^ 59
def prefixEnd_5217906 : Nat := 4983230072969 + 3 ^ 40 * 5217906 * 2
def baseEnd_5217906 : Nat := 2679293787979167152478293

theorem tailTrace_5217906 : CollatzResearch.WordTrace tailWord_5217906 prefixEnd_5217906 2679293787979167152478293 := by
  unfold tailWord_5217906
  simp only [CollatzResearch.WordTrace]
  refine ⟨47578166658606296060510393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126875111089616789494694381 47578166658606296060510393)
  ·
    refine ⟨35683624993954722045382795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47578166658606296060510393 35683624993954722045382795)
    ·
      refine ⟨53525437490932083068074193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35683624993954722045382795 53525437490932083068074193)
      ·
        refine ⟨40144078118199062301055645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53525437490932083068074193 40144078118199062301055645)
        ·
          refine ⟨15054029294324648362895867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40144078118199062301055645 15054029294324648362895867)
          ·
            refine ⟨22581043941486972544343801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15054029294324648362895867 22581043941486972544343801)
            ·
              refine ⟨16935782956115229408257851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22581043941486972544343801 16935782956115229408257851)
              ·
                refine ⟨25403674434172844112386777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16935782956115229408257851 25403674434172844112386777)
                ·
                  refine ⟨19052755825629633084290083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25403674434172844112386777 19052755825629633084290083)
                  ·
                    refine ⟨28579133738444449626435125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19052755825629633084290083 28579133738444449626435125)
                    ·
                      refine ⟨2679293787979167152478293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28579133738444449626435125 2679293787979167152478293)
                      ·
                        rfl

theorem cell23_5217906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5217906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217906 prefixEnd_5217906 := by exact prefixLift 5217906
  have htrace : WordTrace (prefixWord ++ tailWord_5217906) baseStart_5217906 baseEnd_5217906 := by
    simpa [prefixWord, tailWord_5217906, baseEnd_5217906] using wordTrace_append hprefix tailTrace_5217906
  have hstable : (prefixWord ++ tailWord_5217906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217906).length < 2 ^ (prefixWord ++ tailWord_5217906).sum := by decide
  have hdescent : baseEnd_5217906 < baseStart_5217906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217920 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 2, 2, 2]
def baseStart_5217920 : Nat := 118140960795 + 5217920 * 2 ^ 59
def prefixEnd_5217920 : Nat := 4983230072969 + 3 ^ 40 * 5217920 * 2
def baseEnd_5217920 : Nat := 2679300976708330097703229

theorem tailTrace_5217920 : CollatzResearch.WordTrace tailWord_5217920 prefixEnd_5217920 2679300976708330097703229 := by
  unfold tailWord_5217920
  simp only [CollatzResearch.WordTrace]
  refine ⟨95156588628187232316525607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126875451504249643088700809 95156588628187232316525607)
  ·
    refine ⟨142734882942280848474788411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95156588628187232316525607 142734882942280848474788411)
    ·
      refine ⟨214102324413421272712182617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142734882942280848474788411 214102324413421272712182617)
      ·
        refine ⟨160576743310065954534136963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214102324413421272712182617 160576743310065954534136963)
        ·
          refine ⟨240865114965098931801205445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160576743310065954534136963 240865114965098931801205445)
          ·
            refine ⟨45162209055956049712726021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240865114965098931801205445 45162209055956049712726021)
            ·
              refine ⟨8467914197991759321136129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45162209055956049712726021 8467914197991759321136129)
              ·
                refine ⟨6350935648493819490852097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8467914197991759321136129 6350935648493819490852097)
                ·
                  refine ⟨4763201736370364618139073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6350935648493819490852097 4763201736370364618139073)
                  ·
                    refine ⟨3572401302277773463604305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763201736370364618139073 3572401302277773463604305)
                    ·
                      refine ⟨2679300976708330097703229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572401302277773463604305 2679300976708330097703229)
                      ·
                        rfl

theorem cell23_5217920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_5217920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217920 prefixEnd_5217920 := by exact prefixLift 5217920
  have htrace : WordTrace (prefixWord ++ tailWord_5217920) baseStart_5217920 baseEnd_5217920 := by
    simpa [prefixWord, tailWord_5217920, baseEnd_5217920] using wordTrace_append hprefix tailTrace_5217920
  have hstable : (prefixWord ++ tailWord_5217920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217920).length < 2 ^ (prefixWord ++ tailWord_5217920).sum := by decide
  have hdescent : baseEnd_5217920 < baseStart_5217920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217956 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_5217956 : Nat := 118140960795 + 5217956 * 2 ^ 59
def prefixEnd_5217956 : Nat := 4983230072969 + 3 ^ 40 * 5217956 * 2
def baseEnd_5217956 : Nat := 893106487337297318951021

theorem tailTrace_5217956 : CollatzResearch.WordTrace tailWord_5217956 prefixEnd_5217956 893106487337297318951021 := by
  unfold tailWord_5217956
  simp only [CollatzResearch.WordTrace]
  refine ⟨95157245142122021390680861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126876326856162695187574481 95157245142122021390680861)
  ·
    refine ⟨35683966928295758021505323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95157245142122021390680861 35683966928295758021505323)
    ·
      refine ⟨53525950392443637032257985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35683966928295758021505323 53525950392443637032257985)
      ·
        refine ⟨40144462794332727774193489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53525950392443637032257985 40144462794332727774193489)
        ·
          refine ⟨30108347095749545830645117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40144462794332727774193489 30108347095749545830645117)
          ·
            refine ⟨11290630160906079686491919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30108347095749545830645117 11290630160906079686491919)
            ·
              refine ⟨16935945241359119529737879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11290630160906079686491919 16935945241359119529737879)
              ·
                refine ⟨25403917862038679294606819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16935945241359119529737879 25403917862038679294606819)
                ·
                  refine ⟨38105876793058018941910229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25403917862038679294606819 38105876793058018941910229)
                  ·
                    refine ⟨893106487337297318951021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38105876793058018941910229 893106487337297318951021)
                    ·
                      rfl

theorem cell23_5217956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_5217956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217956 prefixEnd_5217956 := by exact prefixLift 5217956
  have htrace : WordTrace (prefixWord ++ tailWord_5217956) baseStart_5217956 baseEnd_5217956 := by
    simpa [prefixWord, tailWord_5217956, baseEnd_5217956] using wordTrace_append hprefix tailTrace_5217956
  have hstable : (prefixWord ++ tailWord_5217956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217956).length < 2 ^ (prefixWord ++ tailWord_5217956).sum := by decide
  have hdescent : baseEnd_5217956 < baseStart_5217956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217976 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_5217976 : Nat := 118140960795 + 5217976 * 2 ^ 59
def prefixEnd_5217976 : Nat := 4983230072969 + 3 ^ 40 * 5217976 * 2
def baseEnd_5217976 : Nat := 2679329731624981878602971

theorem tailTrace_5217976 : CollatzResearch.WordTrace tailWord_5217976 prefixEnd_5217976 2679329731624981878602971 := by
  unfold tailWord_5217976
  simp only [CollatzResearch.WordTrace]
  refine ⟨95157609872085793098544891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126876813162781057464726521 95157609872085793098544891)
  ·
    refine ⟨142736414808128689647817337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95157609872085793098544891 142736414808128689647817337)
    ·
      refine ⟨107052311106096517235863003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142736414808128689647817337 107052311106096517235863003)
      ·
        refine ⟨160578466659144775853794505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107052311106096517235863003 160578466659144775853794505)
        ·
          refine ⟨120433849994358581890345879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160578466659144775853794505 120433849994358581890345879)
          ·
            refine ⟨180650774991537872835518819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120433849994358581890345879 180650774991537872835518819)
            ·
              refine ⟨270976162487306809253278229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180650774991537872835518819 270976162487306809253278229)
              ·
                refine ⟨12702007616592506683747417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270976162487306809253278229 12702007616592506683747417)
                ·
                  refine ⟨9526505712444380012810563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12702007616592506683747417 9526505712444380012810563)
                  ·
                    refine ⟨14289758568666570019215845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9526505712444380012810563 14289758568666570019215845)
                    ·
                      refine ⟨2679329731624981878602971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14289758568666570019215845 2679329731624981878602971)
                      ·
                        rfl

theorem cell23_5217976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_5217976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217976 prefixEnd_5217976 := by exact prefixLift 5217976
  have htrace : WordTrace (prefixWord ++ tailWord_5217976) baseStart_5217976 baseEnd_5217976 := by
    simpa [prefixWord, tailWord_5217976, baseEnd_5217976] using wordTrace_append hprefix tailTrace_5217976
  have hstable : (prefixWord ++ tailWord_5217976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217976).length < 2 ^ (prefixWord ++ tailWord_5217976).sum := by decide
  have hdescent : baseEnd_5217976 < baseStart_5217976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217979 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5]
def baseStart_5217979 : Nat := 118140960795 + 5217979 * 2 ^ 59
def prefixEnd_5217979 : Nat := 4983230072969 + 3 ^ 40 * 5217979 * 2
def baseEnd_5217979 : Nat := 2679331272066945366865457

theorem tailTrace_5217979 : CollatzResearch.WordTrace tailWord_5217979 prefixEnd_5217979 2679331272066945366865457 := by
  unfold tailWord_5217979
  simp only [CollatzResearch.WordTrace]
  refine ⟨190315329163160717709448991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126876886108773811806299327 190315329163160717709448991)
  ·
    refine ⟨285472993744741076564173487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190315329163160717709448991 285472993744741076564173487)
    ·
      refine ⟨428209490617111614846260231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285472993744741076564173487 428209490617111614846260231)
      ·
        refine ⟨642314235925667422269390347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428209490617111614846260231 642314235925667422269390347)
        ·
          refine ⟨963471353888501133404085521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642314235925667422269390347 963471353888501133404085521)
          ·
            refine ⟨722603515416375850053064141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963471353888501133404085521 722603515416375850053064141)
            ·
              refine ⟨270976318281140943769899053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722603515416375850053064141 270976318281140943769899053)
              ·
                refine ⟨101616119355427853913712145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270976318281140943769899053 101616119355427853913712145)
                ·
                  refine ⟨76212089516570890435284109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101616119355427853913712145 76212089516570890435284109)
                  ·
                    refine ⟨28579533568714083913231541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76212089516570890435284109 28579533568714083913231541)
                    ·
                      refine ⟨2679331272066945366865457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28579533568714083913231541 2679331272066945366865457)
                      ·
                        rfl

theorem cell23_5217979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_5217979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217979 prefixEnd_5217979 := by exact prefixLift 5217979
  have htrace : WordTrace (prefixWord ++ tailWord_5217979) baseStart_5217979 baseEnd_5217979 := by
    simpa [prefixWord, tailWord_5217979, baseEnd_5217979] using wordTrace_append hprefix tailTrace_5217979
  have hstable : (prefixWord ++ tailWord_5217979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217979).length < 2 ^ (prefixWord ++ tailWord_5217979).sum := by decide
  have hdescent : baseEnd_5217979 < baseStart_5217979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217990 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_5217990 : Nat := 118140960795 + 5217990 * 2 ^ 59
def prefixEnd_5217990 : Nat := 4983230072969 + 3 ^ 40 * 5217990 * 2
def baseEnd_5217990 : Nat := 893112306784714941275969

theorem tailTrace_5217990 : CollatzResearch.WordTrace tailWord_5217990 prefixEnd_5217990 893112306784714941275969 := by
  unfold tailWord_5217990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947366573941277080878107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126877153577413911058732949 5947366573941277080878107)
  ·
    refine ⟨8921049860911915621317161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5947366573941277080878107 8921049860911915621317161)
    ·
      refine ⟨6690787395683936715987871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8921049860911915621317161 6690787395683936715987871)
      ·
        refine ⟨10036181093525905073981807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6690787395683936715987871 10036181093525905073981807)
        ·
          refine ⟨15054271640288857610972711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10036181093525905073981807 15054271640288857610972711)
          ·
            refine ⟨22581407460433286416459067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15054271640288857610972711 22581407460433286416459067)
            ·
              refine ⟨33872111190649929624688601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22581407460433286416459067 33872111190649929624688601)
              ·
                refine ⟨25404083392987447218516451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33872111190649929624688601 25404083392987447218516451)
                ·
                  refine ⟨38106125089481170827774677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25404083392987447218516451 38106125089481170827774677)
                  ·
                    refine ⟨893112306784714941275969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38106125089481170827774677 893112306784714941275969)
                    ·
                      rfl

theorem cell23_5217990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_5217990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5217990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5217990 prefixEnd_5217990 := by exact prefixLift 5217990
  have htrace : WordTrace (prefixWord ++ tailWord_5217990) baseStart_5217990 baseEnd_5217990 := by
    simpa [prefixWord, tailWord_5217990, baseEnd_5217990] using wordTrace_append hprefix tailTrace_5217990
  have hstable : (prefixWord ++ tailWord_5217990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217990).length < 2 ^ (prefixWord ++ tailWord_5217990).sum := by decide
  have hdescent : baseEnd_5217990 < baseStart_5217990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218043 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 3]
def baseStart_5218043 : Nat := 118140960795 + 5218043 * 2 ^ 59
def prefixEnd_5218043 : Nat := 4983230072969 + 3 ^ 40 * 5218043 * 2
def baseEnd_5218043 : Nat := 2679364134828833116465163

theorem tailTrace_5218043 : CollatzResearch.WordTrace tailWord_5218043 prefixEnd_5218043 2679364134828833116465163 := by
  unfold tailWord_5218043
  simp only [CollatzResearch.WordTrace]
  refine ⟨190317663434928856639778783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126878442289952571093185855 190317663434928856639778783)
  ·
    refine ⟨285476495152393284959668175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190317663434928856639778783 285476495152393284959668175)
    ·
      refine ⟨428214742728589927439502263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285476495152393284959668175 428214742728589927439502263)
      ·
        refine ⟨642322114092884891159253395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428214742728589927439502263 642322114092884891159253395)
        ·
          refine ⟨963483171139327336738880093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642322114092884891159253395 963483171139327336738880093)
          ·
            refine ⟨361306189177247751277080035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 963483171139327336738880093 361306189177247751277080035)
            ·
              refine ⟨541959283765871626915620053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361306189177247751277080035 541959283765871626915620053)
              ·
                refine ⟨12702170713262616255834845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 541959283765871626915620053 12702170713262616255834845)
                ·
                  refine ⟨4763314017473481095938067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12702170713262616255834845 4763314017473481095938067)
                  ·
                    refine ⟨7144971026210221643907101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4763314017473481095938067 7144971026210221643907101)
                    ·
                      refine ⟨2679364134828833116465163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7144971026210221643907101 2679364134828833116465163)
                      ·
                        rfl

theorem cell23_5218043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 3].length) (baseStart_5218043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218043 prefixEnd_5218043 := by exact prefixLift 5218043
  have htrace : WordTrace (prefixWord ++ tailWord_5218043) baseStart_5218043 baseEnd_5218043 := by
    simpa [prefixWord, tailWord_5218043, baseEnd_5218043] using wordTrace_append hprefix tailTrace_5218043
  have hstable : (prefixWord ++ tailWord_5218043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218043).length < 2 ^ (prefixWord ++ tailWord_5218043).sum := by decide
  have hdescent : baseEnd_5218043 < baseStart_5218043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218061 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5218061 : Nat := 118140960795 + 5218061 * 2 ^ 59
def prefixEnd_5218061 : Nat := 4983230072969 + 3 ^ 40 * 5218061 * 2
def baseEnd_5218061 : Nat := 2679373377480614046040081

theorem tailTrace_5218061 : CollatzResearch.WordTrace tailWord_5218061 prefixEnd_5218061 2679373377480614046040081 := by
  unfold tailWord_5218061
  simp only [CollatzResearch.WordTrace]
  refine ⟨190318319948863645713934037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126878879965909097142622691 190318319948863645713934037)
  ·
    refine ⟨4460585623801491696420329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 190318319948863645713934037 4460585623801491696420329)
    ·
      refine ⟨3345439217851118772315247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4460585623801491696420329 3345439217851118772315247)
      ·
        refine ⟨5018158826776678158472871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345439217851118772315247 5018158826776678158472871)
        ·
          refine ⟨7527238240165017237709307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5018158826776678158472871 7527238240165017237709307)
          ·
            refine ⟨11290857360247525856563961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7527238240165017237709307 11290857360247525856563961)
            ·
              refine ⟨8468143020185644392422971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11290857360247525856563961 8468143020185644392422971)
              ·
                refine ⟨12702214530278466588634457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468143020185644392422971 12702214530278466588634457)
                ·
                  refine ⟨9526660897708849941475843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12702214530278466588634457 9526660897708849941475843)
                  ·
                    refine ⟨14289991346563274912213765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9526660897708849941475843 14289991346563274912213765)
                    ·
                      refine ⟨2679373377480614046040081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14289991346563274912213765 2679373377480614046040081)
                      ·
                        rfl

theorem cell23_5218061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5218061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218061 prefixEnd_5218061 := by exact prefixLift 5218061
  have htrace : WordTrace (prefixWord ++ tailWord_5218061) baseStart_5218061 baseEnd_5218061 := by
    simpa [prefixWord, tailWord_5218061, baseEnd_5218061] using wordTrace_append hprefix tailTrace_5218061
  have hstable : (prefixWord ++ tailWord_5218061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218061).length < 2 ^ (prefixWord ++ tailWord_5218061).sum := by decide
  have hdescent : baseEnd_5218061 < baseStart_5218061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218080 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 1, 5]
def baseStart_5218080 : Nat := 118140960795 + 5218080 * 2 ^ 59
def prefixEnd_5218080 : Nat := 4983230072969 + 3 ^ 40 * 5218080 * 2
def baseEnd_5218080 : Nat := 893127711204349823900831

theorem tailTrace_5218080 : CollatzResearch.WordTrace tailWord_5218080 prefixEnd_5218080 893127711204349823900831 := by
  unfold tailWord_5218080
  simp only [CollatzResearch.WordTrace]
  refine ⟨95159506467897405979437847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126879341957196541305917129 95159506467897405979437847)
  ·
    refine ⟨142739259701846108969156771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95159506467897405979437847 142739259701846108969156771)
    ·
      refine ⟨214108889552769163453735157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142739259701846108969156771 214108889552769163453735157)
      ·
        refine ⟨20072708395572109073787671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214108889552769163453735157 20072708395572109073787671)
        ·
          refine ⟨30109062593358163610681507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20072708395572109073787671 30109062593358163610681507)
          ·
            refine ⟨45163593890037245416022261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30109062593358163610681507 45163593890037245416022261)
            ·
              refine ⟨4234086927190991757752087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45163593890037245416022261 4234086927190991757752087)
              ·
                refine ⟨6351130390786487636628131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234086927190991757752087 6351130390786487636628131)
                ·
                  refine ⟨9526695586179731454942197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6351130390786487636628131 9526695586179731454942197)
                  ·
                    refine ⟨893127711204349823900831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9526695586179731454942197 893127711204349823900831)
                    ·
                      rfl

theorem cell23_5218080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 5].length) (baseStart_5218080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218080 prefixEnd_5218080 := by exact prefixLift 5218080
  have htrace : WordTrace (prefixWord ++ tailWord_5218080) baseStart_5218080 baseEnd_5218080 := by
    simpa [prefixWord, tailWord_5218080, baseEnd_5218080] using wordTrace_append hprefix tailTrace_5218080
  have hstable : (prefixWord ++ tailWord_5218080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218080).length < 2 ^ (prefixWord ++ tailWord_5218080).sum := by decide
  have hdescent : baseEnd_5218080 < baseStart_5218080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218083 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 4]
def baseStart_5218083 : Nat := 118140960795 + 5218083 * 2 ^ 59
def prefixEnd_5218083 : Nat := 4983230072969 + 3 ^ 40 * 5218083 * 2
def baseEnd_5218083 : Nat := 2679384674055012959964979

theorem tailTrace_5218083 : CollatzResearch.WordTrace tailWord_5218083 prefixEnd_5218083 2679384674055012959964979 := by
  unfold tailWord_5218083
  simp only [CollatzResearch.WordTrace]
  refine ⟨190319122354783943471234903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126879414903189295647489935 190319122354783943471234903)
  ·
    refine ⟨285478683532175915206852355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190319122354783943471234903 285478683532175915206852355)
    ·
      refine ⟨428218025298263872810278533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285478683532175915206852355 428218025298263872810278533)
      ·
        refine ⟨80290879743424476151927225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428218025298263872810278533 80290879743424476151927225)
        ·
          refine ⟨60218159807568357113945419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80290879743424476151927225 60218159807568357113945419)
          ·
            refine ⟨90327239711352535670918129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60218159807568357113945419 90327239711352535670918129)
            ·
              refine ⟨67745429783514401753188597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90327239711352535670918129 67745429783514401753188597)
              ·
                refine ⟨6351134042204475164361431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67745429783514401753188597 6351134042204475164361431)
                ·
                  refine ⟨9526701063306712746542147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6351134042204475164361431 9526701063306712746542147)
                  ·
                    refine ⟨14290051594960069119813221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9526701063306712746542147 14290051594960069119813221)
                    ·
                      refine ⟨2679384674055012959964979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14290051594960069119813221 2679384674055012959964979)
                      ·
                        rfl

theorem cell23_5218083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_5218083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218083 prefixEnd_5218083 := by exact prefixLift 5218083
  have htrace : WordTrace (prefixWord ++ tailWord_5218083) baseStart_5218083 baseEnd_5218083 := by
    simpa [prefixWord, tailWord_5218083, baseEnd_5218083] using wordTrace_append hprefix tailTrace_5218083
  have hstable : (prefixWord ++ tailWord_5218083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218083).length < 2 ^ (prefixWord ++ tailWord_5218083).sum := by decide
  have hdescent : baseEnd_5218083 < baseStart_5218083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218100 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5218100 : Nat := 118140960795 + 5218100 * 2 ^ 59
def prefixEnd_5218100 : Nat := 4983230072969 + 3 ^ 40 * 5218100 * 2
def baseEnd_5218100 : Nat := 2679393403226139393452401

theorem tailTrace_5218100 : CollatzResearch.WordTrace tailWord_5218100 prefixEnd_5218100 2679393403226139393452401 := by
  unfold tailWord_5218100
  simp only [CollatzResearch.WordTrace]
  refine ⟨95159871197861177687301877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126879828263814903583069169 95159871197861177687301877)
  ·
    refine ⟨8921237924799485408184551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95159871197861177687301877 8921237924799485408184551)
    ·
      refine ⟨13381856887199228112276827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8921237924799485408184551 13381856887199228112276827)
      ·
        refine ⟨20072785330798842168415241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13381856887199228112276827 20072785330798842168415241)
        ·
          refine ⟨15054588998099131626311431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20072785330798842168415241 15054588998099131626311431)
          ·
            refine ⟨22581883497148697439467147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15054588998099131626311431 22581883497148697439467147)
            ·
              refine ⟨33872825245723046159200721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22581883497148697439467147 33872825245723046159200721)
              ·
                refine ⟨25404618934292284619400541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33872825245723046159200721 25404618934292284619400541)
                ·
                  refine ⟨9526732100359606732275203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25404618934292284619400541 9526732100359606732275203)
                  ·
                    refine ⟨14290098150539410098412805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9526732100359606732275203 14290098150539410098412805)
                    ·
                      refine ⟨2679393403226139393452401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14290098150539410098412805 2679393403226139393452401)
                      ·
                        rfl

theorem cell23_5218100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5218100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218100 prefixEnd_5218100 := by exact prefixLift 5218100
  have htrace : WordTrace (prefixWord ++ tailWord_5218100) baseStart_5218100 baseEnd_5218100 := by
    simpa [prefixWord, tailWord_5218100, baseEnd_5218100] using wordTrace_append hprefix tailTrace_5218100
  have hstable : (prefixWord ++ tailWord_5218100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218100).length < 2 ^ (prefixWord ++ tailWord_5218100).sum := by decide
  have hdescent : baseEnd_5218100 < baseStart_5218100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218110 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_5218110 : Nat := 118140960795 + 5218110 * 2 ^ 59
def prefixEnd_5218110 : Nat := 4983230072969 + 3 ^ 40 * 5218110 * 2
def baseEnd_5218110 : Nat := 893132846010894784775785

theorem tailTrace_5218110 : CollatzResearch.WordTrace tailWord_5218110 prefixEnd_5218110 893132846010894784775785 := by
  unfold tailWord_5218110
  simp only [CollatzResearch.WordTrace]
  refine ⟨23790013390710765885308473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126880071417124084721645189 23790013390710765885308473)
  ·
    refine ⟨17842510043033074413981355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23790013390710765885308473 17842510043033074413981355)
    ·
      refine ⟨26763765064549611620972033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17842510043033074413981355 26763765064549611620972033)
      ·
        refine ⟨20072823798412208715729025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26763765064549611620972033 20072823798412208715729025)
        ·
          refine ⟨15054617848809156536796769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20072823798412208715729025 15054617848809156536796769)
          ·
            refine ⟨11290963386606867402597577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15054617848809156536796769 11290963386606867402597577)
            ·
              refine ⟨8468222539955150551948183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11290963386606867402597577 8468222539955150551948183)
              ·
                refine ⟨12702333809932725827922275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468222539955150551948183 12702333809932725827922275)
                ·
                  refine ⟨19053500714899088741883413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12702333809932725827922275 19053500714899088741883413)
                  ·
                    refine ⟨893132846010894784775785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19053500714899088741883413 893132846010894784775785)
                    ·
                      rfl

theorem cell23_5218110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_5218110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218110 prefixEnd_5218110 := by exact prefixLift 5218110
  have htrace : WordTrace (prefixWord ++ tailWord_5218110) baseStart_5218110 baseEnd_5218110 := by
    simpa [prefixWord, tailWord_5218110, baseEnd_5218110] using wordTrace_append hprefix tailTrace_5218110
  have hstable : (prefixWord ++ tailWord_5218110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218110).length < 2 ^ (prefixWord ++ tailWord_5218110).sum := by decide
  have hdescent : baseEnd_5218110 < baseStart_5218110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218194 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5218194 : Nat := 118140960795 + 5218194 * 2 ^ 59
def prefixEnd_5218194 : Nat := 4983230072969 + 3 ^ 40 * 5218194 * 2
def baseEnd_5218194 : Nat := 2679441670407662025676969

theorem tailTrace_5218194 : CollatzResearch.WordTrace tailWord_5218194 prefixEnd_5218194 2679441670407662025676969 := by
  unfold tailWord_5218194
  simp only [CollatzResearch.WordTrace]
  refine ⟨47580792714345452357131409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126882113904921206285683757 47580792714345452357131409)
  ·
    refine ⟨35685594535759089267848557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47580792714345452357131409 35685594535759089267848557)
    ·
      refine ⟨13382097950909658475443209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35685594535759089267848557 13382097950909658475443209)
      ·
        refine ⟨10036573463182243856582407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13382097950909658475443209 10036573463182243856582407)
        ·
          refine ⟨15054860194773365784873611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10036573463182243856582407 15054860194773365784873611)
          ·
            refine ⟨22582290292160048677310417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15054860194773365784873611 22582290292160048677310417)
            ·
              refine ⟨16936717719120036507982813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22582290292160048677310417 16936717719120036507982813)
              ·
                refine ⟨6351269144670013690493555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16936717719120036507982813 6351269144670013690493555)
                ·
                  refine ⟨9526903717005020535740333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6351269144670013690493555 9526903717005020535740333)
                  ·
                    refine ⟨3572588893876882700902625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9526903717005020535740333 3572588893876882700902625)
                    ·
                      refine ⟨2679441670407662025676969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572588893876882700902625 2679441670407662025676969)
                      ·
                        rfl

theorem cell23_5218194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5218194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218194 prefixEnd_5218194 := by exact prefixLift 5218194
  have htrace : WordTrace (prefixWord ++ tailWord_5218194) baseStart_5218194 baseEnd_5218194 := by
    simpa [prefixWord, tailWord_5218194, baseEnd_5218194] using wordTrace_append hprefix tailTrace_5218194
  have hstable : (prefixWord ++ tailWord_5218194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218194).length < 2 ^ (prefixWord ++ tailWord_5218194).sum := by decide
  have hdescent : baseEnd_5218194 < baseStart_5218194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218223 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 3]
def baseStart_5218223 : Nat := 118140960795 + 5218223 * 2 ^ 59
def prefixEnd_5218223 : Nat := 4983230072969 + 3 ^ 40 * 5218223 * 2
def baseEnd_5218223 : Nat := 2679456561346642412214335

theorem tailTrace_5218223 : CollatzResearch.WordTrace tailWord_5218223 prefixEnd_5218223 2679456561346642412214335 := by
  unfold tailWord_5218223
  simp only [CollatzResearch.WordTrace]
  refine ⟨190324228574276747381331323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126882819049517831587554215 190324228574276747381331323)
  ·
    refine ⟨285486342861415121071996985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190324228574276747381331323 285486342861415121071996985)
    ·
      refine ⟨214114757146061340803997739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285486342861415121071996985 214114757146061340803997739)
      ·
        refine ⟨321172135719092011205996609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214114757146061340803997739 321172135719092011205996609)
        ·
          refine ⟨240879101789319008404497457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321172135719092011205996609 240879101789319008404497457)
          ·
            refine ⟨180659326341989256303373093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240879101789319008404497457 180659326341989256303373093)
            ·
              refine ⟨33873623689122985556882455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180659326341989256303373093 33873623689122985556882455)
              ·
                refine ⟨50810435533684478335323683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33873623689122985556882455 50810435533684478335323683)
                ·
                  refine ⟨76215653300526717502985525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50810435533684478335323683 76215653300526717502985525)
                  ·
                    refine ⟨7145217496924379765904893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76215653300526717502985525 7145217496924379765904893)
                    ·
                      refine ⟨2679456561346642412214335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145217496924379765904893 2679456561346642412214335)
                      ·
                        rfl

theorem cell23_5218223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_5218223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218223 prefixEnd_5218223 := by exact prefixLift 5218223
  have htrace : WordTrace (prefixWord ++ tailWord_5218223) baseStart_5218223 baseEnd_5218223 := by
    simpa [prefixWord, tailWord_5218223, baseEnd_5218223] using wordTrace_append hprefix tailTrace_5218223
  have hstable : (prefixWord ++ tailWord_5218223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218223).length < 2 ^ (prefixWord ++ tailWord_5218223).sum := by decide
  have hdescent : baseEnd_5218223 < baseStart_5218223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218228 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5218228 : Nat := 118140960795 + 5218228 * 2 ^ 59
def prefixEnd_5218228 : Nat := 4983230072969 + 3 ^ 40 * 5218228 * 2
def baseEnd_5218228 : Nat := 2679459128749914892651813

theorem tailTrace_5218228 : CollatzResearch.WordTrace tailWord_5218228 prefixEnd_5218228 2679459128749914892651813 := by
  unfold tailWord_5218228
  simp only [CollatzResearch.WordTrace]
  refine ⟨95162205469629316617631669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126882940626172422156842225 95162205469629316617631669)
  ·
    refine ⟨8921456762777748432902969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95162205469629316617631669 8921456762777748432902969)
    ·
      refine ⟨6691092572083311324677227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8921456762777748432902969 6691092572083311324677227)
      ·
        refine ⟨10036638858124966987015841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691092572083311324677227 10036638858124966987015841)
        ·
          refine ⟨7527479143593725240261881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10036638858124966987015841 7527479143593725240261881)
          ·
            refine ⟨5645609357695293930196411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7527479143593725240261881 5645609357695293930196411)
            ·
              refine ⟨8468414036542940895294617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645609357695293930196411 8468414036542940895294617)
              ·
                refine ⟨6351310527407205671470963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8468414036542940895294617 6351310527407205671470963)
                ·
                  refine ⟨9526965791110808507206445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6351310527407205671470963 9526965791110808507206445)
                  ·
                    refine ⟨3572612171666553190202417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9526965791110808507206445 3572612171666553190202417)
                    ·
                      refine ⟨2679459128749914892651813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572612171666553190202417 2679459128749914892651813)
                      ·
                        rfl

theorem cell23_5218228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5218228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218228 prefixEnd_5218228 := by exact prefixLift 5218228
  have htrace : WordTrace (prefixWord ++ tailWord_5218228) baseStart_5218228 baseEnd_5218228 := by
    simpa [prefixWord, tailWord_5218228, baseEnd_5218228] using wordTrace_append hprefix tailTrace_5218228
  have hstable : (prefixWord ++ tailWord_5218228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218228).length < 2 ^ (prefixWord ++ tailWord_5218228).sum := by decide
  have hdescent : baseEnd_5218228 < baseStart_5218228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218260 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5218260 : Nat := 118140960795 + 5218260 * 2 ^ 59
def prefixEnd_5218260 : Nat := 4983230072969 + 3 ^ 40 * 5218260 * 2
def baseEnd_5218260 : Nat := 893158520043619589150555

theorem tailTrace_5218260 : CollatzResearch.WordTrace tailWord_5218260 prefixEnd_5218260 893158520043619589150555 := by
  unfold tailWord_5218260
  simp only [CollatzResearch.WordTrace]
  refine ⟨95162789037571351350214117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126883718716761801800285489 95162789037571351350214117)
  ·
    refine ⟨17843022944544628378165147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95162789037571351350214117 17843022944544628378165147)
    ·
      refine ⟨26764534416816942567247721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17843022944544628378165147 26764534416816942567247721)
      ·
        refine ⟨20073400812612706925435791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26764534416816942567247721 20073400812612706925435791)
        ·
          refine ⟨30110101218919060388153687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20073400812612706925435791 30110101218919060388153687)
          ·
            refine ⟨45165151828378590582230531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30110101218919060388153687 45165151828378590582230531)
            ·
              refine ⟨67747727742567885873345797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45165151828378590582230531 67747727742567885873345797)
              ·
                refine ⟨12702698951731478601252337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67747727742567885873345797 12702698951731478601252337)
                ·
                  refine ⟨9527024213798608950939253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12702698951731478601252337 9527024213798608950939253)
                  ·
                    refine ⟨893158520043619589150555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9527024213798608950939253 893158520043619589150555)
                    ·
                      rfl

theorem cell23_5218260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5218260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218260 prefixEnd_5218260 := by exact prefixLift 5218260
  have htrace : WordTrace (prefixWord ++ tailWord_5218260) baseStart_5218260 baseEnd_5218260 := by
    simpa [prefixWord, tailWord_5218260, baseEnd_5218260] using wordTrace_append hprefix tailTrace_5218260
  have hstable : (prefixWord ++ tailWord_5218260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218260).length < 2 ^ (prefixWord ++ tailWord_5218260).sum := by decide
  have hdescent : baseEnd_5218260 < baseStart_5218260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218274 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5218274 : Nat := 118140960795 + 5218274 * 2 ^ 59
def prefixEnd_5218274 : Nat := 4983230072969 + 3 ^ 40 * 5218274 * 2
def baseEnd_5218274 : Nat := 2679482748860021712676601

theorem tailTrace_5218274 : CollatzResearch.WordTrace tailWord_5218274 prefixEnd_5218274 2679482748860021712676601 := by
  unfold tailWord_5218274
  simp only [CollatzResearch.WordTrace]
  refine ⟨47581522174272995772859469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126884059131394655394291917 47581522174272995772859469)
  ·
    refine ⟨17843070815352373414822301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47581522174272995772859469 17843070815352373414822301)
    ·
      refine ⟨6691151555757140030558363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17843070815352373414822301 6691151555757140030558363)
      ·
        refine ⟨10036727333635710045837545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691151555757140030558363 10036727333635710045837545)
        ·
          refine ⟨7527545500226782534378159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10036727333635710045837545 7527545500226782534378159)
          ·
            refine ⟨11291318250340173801567239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7527545500226782534378159 11291318250340173801567239)
            ·
              refine ⟨16936977375510260702350859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11291318250340173801567239 16936977375510260702350859)
              ·
                refine ⟨25405466063265391053526289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16936977375510260702350859 25405466063265391053526289)
                ·
                  refine ⟨19054099547449043290144717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25405466063265391053526289 19054099547449043290144717)
                  ·
                    refine ⟨7145287330293391233804269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19054099547449043290144717 7145287330293391233804269)
                    ·
                      refine ⟨2679482748860021712676601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145287330293391233804269 2679482748860021712676601)
                      ·
                        rfl

theorem cell23_5218274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5218274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218274 prefixEnd_5218274 := by exact prefixLift 5218274
  have htrace : WordTrace (prefixWord ++ tailWord_5218274) baseStart_5218274 baseEnd_5218274 := by
    simpa [prefixWord, tailWord_5218274, baseEnd_5218274] using wordTrace_append hprefix tailTrace_5218274
  have hstable : (prefixWord ++ tailWord_5218274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218274).length < 2 ^ (prefixWord ++ tailWord_5218274).sum := by decide
  have hdescent : baseEnd_5218274 < baseStart_5218274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218294 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_5218294 : Nat := 118140960795 + 5218294 * 2 ^ 59
def prefixEnd_5218294 : Nat := 4983230072969 + 3 ^ 40 * 5218294 * 2
def baseEnd_5218294 : Nat := 893164339491037211475503

theorem tailTrace_5218294 : CollatzResearch.WordTrace tailWord_5218294 prefixEnd_5218294 893164339491037211475503 := by
  unfold tailWord_5218294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11895426134813720406697871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126884545438013017671443957 11895426134813720406697871)
  ·
    refine ⟨17843139202220580610046807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11895426134813720406697871 17843139202220580610046807)
    ·
      refine ⟨26764708803330870915070211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17843139202220580610046807 26764708803330870915070211)
      ·
        refine ⟨40147063204996306372605317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26764708803330870915070211 40147063204996306372605317)
        ·
          refine ⟨7527574350936807444863497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40147063204996306372605317 7527574350936807444863497)
          ·
            refine ⟨5645680763202605583647623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7527574350936807444863497 5645680763202605583647623)
            ·
              refine ⟨8468521144803908375471435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645680763202605583647623 8468521144803908375471435)
              ·
                refine ⟨12702781717205862563207153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468521144803908375471435 12702781717205862563207153)
                ·
                  refine ⟨9527086287904396922405365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12702781717205862563207153 9527086287904396922405365)
                  ·
                    refine ⟨893164339491037211475503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9527086287904396922405365 893164339491037211475503)
                    ·
                      rfl

theorem cell23_5218294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_5218294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218294 prefixEnd_5218294 := by exact prefixLift 5218294
  have htrace : WordTrace (prefixWord ++ tailWord_5218294) baseStart_5218294 baseEnd_5218294 := by
    simpa [prefixWord, tailWord_5218294, baseEnd_5218294] using wordTrace_append hprefix tailTrace_5218294
  have hstable : (prefixWord ++ tailWord_5218294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218294).length < 2 ^ (prefixWord ++ tailWord_5218294).sum := by decide
  have hdescent : baseEnd_5218294 < baseStart_5218294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218297 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 4]
def baseStart_5218297 : Nat := 118140960795 + 5218297 * 2 ^ 59
def prefixEnd_5218297 : Nat := 4983230072969 + 3 ^ 40 * 5218297 * 2
def baseEnd_5218297 : Nat := 2679494558915075122688995

theorem tailTrace_5218297 : CollatzResearch.WordTrace tailWord_5218297 prefixEnd_5218297 2679494558915075122688995 := by
  unfold tailWord_5218297
  simp only [CollatzResearch.WordTrace]
  refine ⟨190326927576008658019525145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126884618384005772013016763 190326927576008658019525145)
  ·
    refine ⟨142745195682006493514643859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190326927576008658019525145 142745195682006493514643859)
    ·
      refine ⟨214117793523009740271965789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142745195682006493514643859 214117793523009740271965789)
      ·
        refine ⟨80294172571128652601987171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214117793523009740271965789 80294172571128652601987171)
        ·
          refine ⟨120441258856692978902980757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80294172571128652601987171 120441258856692978902980757)
          ·
            refine ⟨5645684008907483386077223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120441258856692978902980757 5645684008907483386077223)
            ·
              refine ⟨8468526013361225079115835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645684008907483386077223 8468526013361225079115835)
              ·
                refine ⟨12702789020041837618673753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468526013361225079115835 12702789020041837618673753)
                ·
                  refine ⟨9527091765031378214005315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12702789020041837618673753 9527091765031378214005315)
                  ·
                    refine ⟨14290637647547067321007973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9527091765031378214005315 14290637647547067321007973)
                    ·
                      refine ⟨2679494558915075122688995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14290637647547067321007973 2679494558915075122688995)
                      ·
                        rfl

theorem cell23_5218297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_5218297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218297 prefixEnd_5218297 := by exact prefixLift 5218297
  have htrace : WordTrace (prefixWord ++ tailWord_5218297) baseStart_5218297 baseEnd_5218297 := by
    simpa [prefixWord, tailWord_5218297, baseEnd_5218297] using wordTrace_append hprefix tailTrace_5218297
  have hstable : (prefixWord ++ tailWord_5218297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218297).length < 2 ^ (prefixWord ++ tailWord_5218297).sum := by decide
  have hdescent : baseEnd_5218297 < baseStart_5218297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218300 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_5218300 : Nat := 118140960795 + 5218300 * 2 ^ 59
def prefixEnd_5218300 : Nat := 4983230072969 + 3 ^ 40 * 5218300 * 2
def baseEnd_5218300 : Nat := 2679496099357038610951481

theorem tailTrace_5218300 : CollatzResearch.WordTrace tailWord_5218300 prefixEnd_5218300 2679496099357038610951481 := by
  unfold tailWord_5218300
  simp only [CollatzResearch.WordTrace]
  refine ⟨95163518497498894765942177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126884691329998526354589569 95163518497498894765942177)
  ·
    refine ⟨71372638873124171074456633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95163518497498894765942177 71372638873124171074456633)
    ·
      refine ⟨53529479154843128305842475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71372638873124171074456633 53529479154843128305842475)
      ·
        refine ⟨80294218732264692458763713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53529479154843128305842475 80294218732264692458763713)
        ·
          refine ⟨60220664049198519344072785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80294218732264692458763713 60220664049198519344072785)
          ·
            refine ⟨45165498036898889508054589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60220664049198519344072785 45165498036898889508054589)
            ·
              refine ⟨16937061763837083565520471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45165498036898889508054589 16937061763837083565520471)
              ·
                refine ⟨25405592645755625348280707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16937061763837083565520471 25405592645755625348280707)
                ·
                  refine ⟨38108388968633438022421061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25405592645755625348280707 38108388968633438022421061)
                  ·
                    refine ⟨7145322931618769629203949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38108388968633438022421061 7145322931618769629203949)
                    ·
                      refine ⟨2679496099357038610951481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145322931618769629203949 2679496099357038610951481)
                      ·
                        rfl

theorem cell23_5218300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_5218300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218300 prefixEnd_5218300 := by exact prefixLift 5218300
  have htrace : WordTrace (prefixWord ++ tailWord_5218300) baseStart_5218300 baseEnd_5218300 := by
    simpa [prefixWord, tailWord_5218300, baseEnd_5218300] using wordTrace_append hprefix tailTrace_5218300
  have hstable : (prefixWord ++ tailWord_5218300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218300).length < 2 ^ (prefixWord ++ tailWord_5218300).sum := by decide
  have hdescent : baseEnd_5218300 < baseStart_5218300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218323 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6]
def baseStart_5218323 : Nat := 118140960795 + 5218323 * 2 ^ 59
def prefixEnd_5218323 : Nat := 4983230072969 + 3 ^ 40 * 5218323 * 2
def baseEnd_5218323 : Nat := 2679507909412092020963875

theorem tailTrace_5218323 : CollatzResearch.WordTrace tailWord_5218323 prefixEnd_5218323 2679507909412092020963875 := by
  unfold tailWord_5218323
  simp only [CollatzResearch.WordTrace]
  refine ⟨190327875873914464459971623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126885250582609642973314415 190327875873914464459971623)
  ·
    refine ⟨285491813810871696689957435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190327875873914464459971623 285491813810871696689957435)
    ·
      refine ⟨428237720716307545034936153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285491813810871696689957435 428237720716307545034936153)
      ·
        refine ⟨321178290537230658776202115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428237720716307545034936153 321178290537230658776202115)
        ·
          refine ⟨481767435805845988164303173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321178290537230658776202115 481767435805845988164303173)
          ·
            refine ⟨90331394213596122780806845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 481767435805845988164303173 90331394213596122780806845)
            ·
              refine ⟨33874272830098546042802567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90331394213596122780806845 33874272830098546042802567)
              ·
                refine ⟨50811409245147819064203851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33874272830098546042802567 50811409245147819064203851)
                ·
                  refine ⟨76217113867721728596305777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50811409245147819064203851 76217113867721728596305777)
                  ·
                    refine ⟨57162835400791296447229333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76217113867721728596305777 57162835400791296447229333)
                    ·
                      refine ⟨2679507909412092020963875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57162835400791296447229333 2679507909412092020963875)
                      ·
                        rfl

theorem cell23_5218323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_5218323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218323 prefixEnd_5218323 := by exact prefixLift 5218323
  have htrace : WordTrace (prefixWord ++ tailWord_5218323) baseStart_5218323 baseEnd_5218323 := by
    simpa [prefixWord, tailWord_5218323, baseEnd_5218323] using wordTrace_append hprefix tailTrace_5218323
  have hstable : (prefixWord ++ tailWord_5218323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218323).length < 2 ^ (prefixWord ++ tailWord_5218323).sum := by decide
  have hdescent : baseEnd_5218323 < baseStart_5218323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218357 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_5218357 : Nat := 118140960795 + 5218357 * 2 ^ 59
def prefixEnd_5218357 : Nat := 4983230072969 + 3 ^ 40 * 5218357 * 2
def baseEnd_5218357 : Nat := 2679525367754344887938719

theorem tailTrace_5218357 : CollatzResearch.WordTrace tailWord_5218357 prefixEnd_5218357 2679525367754344887938719 := by
  unfold tailWord_5218357
  simp only [CollatzResearch.WordTrace]
  refine ⟨190329115955791288266709325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126886077303860858844472883 190329115955791288266709325)
  ·
    refine ⟨71373418483421733100015997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190329115955791288266709325 71373418483421733100015997)
    ·
      refine ⟨26765031931283149912505999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71373418483421733100015997 26765031931283149912505999)
      ·
        refine ⟨40147547896924724868758999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26765031931283149912505999 40147547896924724868758999)
        ·
          refine ⟨60221321845387087303138499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40147547896924724868758999 60221321845387087303138499)
          ·
            refine ⟨90331982768080630954707749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60221321845387087303138499 90331982768080630954707749)
            ·
              refine ⟨16937246769015118304007703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90331982768080630954707749 16937246769015118304007703)
              ·
                refine ⟨25405870153522677456011555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16937246769015118304007703 25405870153522677456011555)
                ·
                  refine ⟨38108805230284016184017333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25405870153522677456011555 38108805230284016184017333)
                  ·
                    refine ⟨3572700490339126517251625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38108805230284016184017333 3572700490339126517251625)
                    ·
                      refine ⟨2679525367754344887938719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572700490339126517251625 2679525367754344887938719)
                      ·
                        rfl

theorem cell23_5218357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_5218357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218357 prefixEnd_5218357 := by exact prefixLift 5218357
  have htrace : WordTrace (prefixWord ++ tailWord_5218357) baseStart_5218357 baseEnd_5218357 := by
    simpa [prefixWord, tailWord_5218357, baseEnd_5218357] using wordTrace_append hprefix tailTrace_5218357
  have hstable : (prefixWord ++ tailWord_5218357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218357).length < 2 ^ (prefixWord ++ tailWord_5218357).sum := by decide
  have hdescent : baseEnd_5218357 < baseStart_5218357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218400 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_5218400 : Nat := 118140960795 + 5218400 * 2 ^ 59
def prefixEnd_5218400 : Nat := 4983230072969 + 3 ^ 40 * 5218400 * 2
def baseEnd_5218400 : Nat := 2679547447422488219701021

theorem tailTrace_5218400 : CollatzResearch.WordTrace tailWord_5218400 prefixEnd_5218400 2679547447422488219701021 := by
  unfold tailWord_5218400
  simp only [CollatzResearch.WordTrace]
  refine ⟨95165342147317753305262327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126887122863090337740349769 95165342147317753305262327)
  ·
    refine ⟨142748013220976629957893491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95165342147317753305262327 142748013220976629957893491)
    ·
      refine ⟨214122019831464944936840237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142748013220976629957893491 214122019831464944936840237)
      ·
        refine ⟨80295757436799354351315089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214122019831464944936840237 80295757436799354351315089)
        ·
          refine ⟨60221818077599515763486317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80295757436799354351315089 60221818077599515763486317)
          ·
            refine ⟨22583181779099818411307369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60221818077599515763486317 22583181779099818411307369)
            ·
              refine ⟨16937386334324863808480527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22583181779099818411307369 16937386334324863808480527)
              ·
                refine ⟨25406079501487295712720791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16937386334324863808480527 25406079501487295712720791)
                ·
                  refine ⟨38109119252230943569081187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25406079501487295712720791 38109119252230943569081187)
                  ·
                    refine ⟨57163678878346415353621781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38109119252230943569081187 57163678878346415353621781)
                    ·
                      refine ⟨2679547447422488219701021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57163678878346415353621781 2679547447422488219701021)
                      ·
                        rfl

theorem cell23_5218400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_5218400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218400 prefixEnd_5218400 := by exact prefixLift 5218400
  have htrace : WordTrace (prefixWord ++ tailWord_5218400) baseStart_5218400 baseEnd_5218400 := by
    simpa [prefixWord, tailWord_5218400, baseEnd_5218400] using wordTrace_append hprefix tailTrace_5218400
  have hstable : (prefixWord ++ tailWord_5218400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218400).length < 2 ^ (prefixWord ++ tailWord_5218400).sum := by decide
  have hdescent : baseEnd_5218400 < baseStart_5218400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218404 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_5218404 : Nat := 118140960795 + 5218404 * 2 ^ 59
def prefixEnd_5218404 : Nat := 4983230072969 + 3 ^ 40 * 5218404 * 2
def baseEnd_5218404 : Nat := 2679549501345106204051003

theorem tailTrace_5218404 : CollatzResearch.WordTrace tailWord_5218404 prefixEnd_5218404 2679549501345106204051003 := by
  unfold tailWord_5218404
  simp only [CollatzResearch.WordTrace]
  refine ⟨95165415093310507646835133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126887220124414010195780177 95165415093310507646835133)
  ·
    refine ⟨35687030659991440367563175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95165415093310507646835133 35687030659991440367563175)
    ·
      refine ⟨53530545989987160551344763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35687030659991440367563175 53530545989987160551344763)
      ·
        refine ⟨80295818984980740827017145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53530545989987160551344763 80295818984980740827017145)
        ·
          refine ⟨60221864238735555620262859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80295818984980740827017145 60221864238735555620262859)
          ·
            refine ⟨90332796358103333430394289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60221864238735555620262859 90332796358103333430394289)
            ·
              refine ⟨67749597268577500072795717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90332796358103333430394289 67749597268577500072795717)
              ·
                refine ⟨12703049487858281263649197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67749597268577500072795717 12703049487858281263649197)
                ·
                  refine ⟨4763643557946855473868449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12703049487858281263649197 4763643557946855473868449)
                  ·
                    refine ⟨3572732668460141605401337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763643557946855473868449 3572732668460141605401337)
                    ·
                      refine ⟨2679549501345106204051003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572732668460141605401337 2679549501345106204051003)
                      ·
                        rfl

theorem cell23_5218404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_5218404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218404 prefixEnd_5218404 := by exact prefixLift 5218404
  have htrace : WordTrace (prefixWord ++ tailWord_5218404) baseStart_5218404 baseEnd_5218404 := by
    simpa [prefixWord, tailWord_5218404, baseEnd_5218404] using wordTrace_append hprefix tailTrace_5218404
  have hstable : (prefixWord ++ tailWord_5218404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218404).length < 2 ^ (prefixWord ++ tailWord_5218404).sum := by decide
  have hdescent : baseEnd_5218404 < baseStart_5218404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218407 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_5218407 : Nat := 118140960795 + 5218407 * 2 ^ 59
def prefixEnd_5218407 : Nat := 4983230072969 + 3 ^ 40 * 5218407 * 2
def baseEnd_5218407 : Nat := 2679551041787069692313489

theorem tailTrace_5218407 : CollatzResearch.WordTrace tailWord_5218407 prefixEnd_5218407 2679551041787069692313489 := by
  unfold tailWord_5218407
  simp only [CollatzResearch.WordTrace]
  refine ⟨190330939605610146806029475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126887293070406764537352983 190330939605610146806029475)
  ·
    refine ⟨285496409408415220209044213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190330939605610146806029475 285496409408415220209044213)
    ·
      refine ⟨26765288382038926894597895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285496409408415220209044213 26765288382038926894597895)
      ·
        refine ⟨40147932573058390341896843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26765288382038926894597895 40147932573058390341896843)
        ·
          refine ⟨60221898859587585512845265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40147932573058390341896843 60221898859587585512845265)
          ·
            refine ⟨45166424144690689134633949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60221898859587585512845265 45166424144690689134633949)
            ·
              refine ⟨16937409054259008425487731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45166424144690689134633949 16937409054259008425487731)
              ·
                refine ⟨25406113581388512638231597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16937409054259008425487731 25406113581388512638231597)
                ·
                  refine ⟨9527292593020692239336849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25406113581388512638231597 9527292593020692239336849)
                  ·
                    refine ⟨7145469444765519179502637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9527292593020692239336849 7145469444765519179502637)
                    ·
                      refine ⟨2679551041787069692313489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145469444765519179502637 2679551041787069692313489)
                      ·
                        rfl

theorem cell23_5218407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_5218407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218407 prefixEnd_5218407 := by exact prefixLift 5218407
  have htrace : WordTrace (prefixWord ++ tailWord_5218407) baseStart_5218407 baseEnd_5218407 := by
    simpa [prefixWord, tailWord_5218407, baseEnd_5218407] using wordTrace_append hprefix tailTrace_5218407
  have hstable : (prefixWord ++ tailWord_5218407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218407).length < 2 ^ (prefixWord ++ tailWord_5218407).sum := by decide
  have hdescent : baseEnd_5218407 < baseStart_5218407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218464 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 3, 3, 2]
def baseStart_5218464 : Nat := 118140960795 + 5218464 * 2 ^ 59
def prefixEnd_5218464 : Nat := 4983230072969 + 3 ^ 40 * 5218464 * 2
def baseEnd_5218464 : Nat := 2679580310184375969300727

theorem tailTrace_5218464 : CollatzResearch.WordTrace tailWord_5218464 prefixEnd_5218464 2679580310184375969300727 := by
  unfold tailWord_5218464
  simp only [CollatzResearch.WordTrace]
  refine ⟨95166509283201822770427223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126888679044269097027236297 95166509283201822770427223)
  ·
    refine ⟨142749763924802734155640835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95166509283201822770427223 142749763924802734155640835)
    ·
      refine ⟨214124645887204101233461253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142749763924802734155640835 214124645887204101233461253)
      ·
        refine ⟨40148371103850768981273985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214124645887204101233461253 40148371103850768981273985)
        ·
          refine ⟨30111278327888076735955489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40148371103850768981273985 30111278327888076735955489)
          ·
            refine ⟨22583458745916057551966617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30111278327888076735955489 22583458745916057551966617)
            ·
              refine ⟨16937594059437043163974963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22583458745916057551966617 16937594059437043163974963)
              ·
                refine ⟨25406391089155564745962445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16937594059437043163974963 25406391089155564745962445)
                ·
                  refine ⟨9527396658433336779735917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25406391089155564745962445 9527396658433336779735917)
                  ·
                    refine ⟨3572773746912501292400969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9527396658433336779735917 3572773746912501292400969)
                    ·
                      refine ⟨2679580310184375969300727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572773746912501292400969 2679580310184375969300727)
                      ·
                        rfl

theorem cell23_5218464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_5218464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218464 prefixEnd_5218464 := by exact prefixLift 5218464
  have htrace : WordTrace (prefixWord ++ tailWord_5218464) baseStart_5218464 baseEnd_5218464 := by
    simpa [prefixWord, tailWord_5218464, baseEnd_5218464] using wordTrace_append hprefix tailTrace_5218464
  have hstable : (prefixWord ++ tailWord_5218464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218464).length < 2 ^ (prefixWord ++ tailWord_5218464).sum := by decide
  have hdescent : baseEnd_5218464 < baseStart_5218464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218547 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 2, 5]
def baseStart_5218547 : Nat := 118140960795 + 5218547 * 2 ^ 59
def prefixEnd_5218547 : Nat := 4983230072969 + 3 ^ 40 * 5218547 * 2
def baseEnd_5218547 : Nat := 893207643026233048187615

theorem tailTrace_5218547 : CollatzResearch.WordTrace tailWord_5218547 prefixEnd_5218547 893207643026233048187615 := by
  unfold tailWord_5218547
  simp only [CollatzResearch.WordTrace]
  refine ⟨190336045825102950716125895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126890697216735300477417263 190336045825102950716125895)
  ·
    refine ⟨285504068737654426074188843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190336045825102950716125895 285504068737654426074188843)
    ·
      refine ⟨428256103106481639111283265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285504068737654426074188843 428256103106481639111283265)
      ·
        refine ⟨321192077329861229333462449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428256103106481639111283265 321192077329861229333462449)
        ·
          refine ⟨240894057997395922000096837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321192077329861229333462449 240894057997395922000096837)
          ·
            refine ⟨45167635874511735375018157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240894057997395922000096837 45167635874511735375018157)
            ·
              refine ⟨16937863452941900765631809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45167635874511735375018157 16937863452941900765631809)
              ·
                refine ⟨12703397589706425574223857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16937863452941900765631809 12703397589706425574223857)
                ·
                  refine ⟨9527548192279819180667893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12703397589706425574223857 9527548192279819180667893)
                  ·
                    refine ⟨893207643026233048187615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9527548192279819180667893 893207643026233048187615)
                    ·
                      rfl

theorem cell23_5218547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 5].length) (baseStart_5218547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218547 prefixEnd_5218547 := by exact prefixLift 5218547
  have htrace : WordTrace (prefixWord ++ tailWord_5218547) baseStart_5218547 baseEnd_5218547 := by
    simpa [prefixWord, tailWord_5218547, baseEnd_5218547] using wordTrace_append hprefix tailTrace_5218547
  have hstable : (prefixWord ++ tailWord_5218547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218547).length < 2 ^ (prefixWord ++ tailWord_5218547).sum := by decide
  have hdescent : baseEnd_5218547 < baseStart_5218547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218562 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_5218562 : Nat := 118140960795 + 5218562 * 2 ^ 59
def prefixEnd_5218562 : Nat := 4983230072969 + 3 ^ 40 * 5218562 * 2
def baseEnd_5218562 : Nat := 2679630631288516585875277

theorem tailTrace_5218562 : CollatzResearch.WordTrace tailWord_5218562 prefixEnd_5218562 2679630631288516585875277 := by
  unfold tailWord_5218562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47584148230012152069480485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126891061946699072185281293 47584148230012152069480485)
  ·
    refine ⟨8922027793127278513027591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47584148230012152069480485 8922027793127278513027591)
    ·
      refine ⟨13383041689690917769541387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8922027793127278513027591 13383041689690917769541387)
      ·
        refine ⟨20074562534536376654312081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13383041689690917769541387 20074562534536376654312081)
        ·
          refine ⟨15055921900902282490734061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20074562534536376654312081 15055921900902282490734061)
          ·
            refine ⟨5645970712838355934025273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15055921900902282490734061 5645970712838355934025273)
            ·
              refine ⟨4234478034628766950518955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5645970712838355934025273 4234478034628766950518955)
              ·
                refine ⟨6351717051943150425778433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234478034628766950518955 6351717051943150425778433)
                ·
                  refine ⟨4763787788957362819333825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6351717051943150425778433 4763787788957362819333825)
                  ·
                    refine ⟨3572840841718022114500369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763787788957362819333825 3572840841718022114500369)
                    ·
                      refine ⟨2679630631288516585875277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3572840841718022114500369 2679630631288516585875277)
                      ·
                        rfl

theorem cell23_5218562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_5218562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218562 prefixEnd_5218562 := by exact prefixLift 5218562
  have htrace : WordTrace (prefixWord ++ tailWord_5218562) baseStart_5218562 baseEnd_5218562 := by
    simpa [prefixWord, tailWord_5218562, baseEnd_5218562] using wordTrace_append hprefix tailTrace_5218562
  have hstable : (prefixWord ++ tailWord_5218562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218562).length < 2 ^ (prefixWord ++ tailWord_5218562).sum := by decide
  have hdescent : baseEnd_5218562 < baseStart_5218562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218584 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_5218584 : Nat := 118140960795 + 5218584 * 2 ^ 59
def prefixEnd_5218584 : Nat := 4983230072969 + 3 ^ 40 * 5218584 * 2
def baseEnd_5218584 : Nat := 2679641927862915499800175

theorem tailTrace_5218584 : CollatzResearch.WordTrace tailWord_5218584 prefixEnd_5218584 2679641927862915499800175 := by
  unfold tailWord_5218584
  simp only [CollatzResearch.WordTrace]
  refine ⟨95168697662984453017611403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126891596883979270690148537 95168697662984453017611403)
  ·
    refine ⟨142753046494476679526417105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95168697662984453017611403 142753046494476679526417105)
    ·
      refine ⟨107064784870857509644812829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142753046494476679526417105 107064784870857509644812829)
      ·
        refine ⟨40149294326571566116804811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107064784870857509644812829 40149294326571566116804811)
        ·
          refine ⟨60223941489857349175207217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40149294326571566116804811 60223941489857349175207217)
          ·
            refine ⟨45167956117393011881405413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60223941489857349175207217 45167956117393011881405413)
            ·
              refine ⟨8468991772011189727763515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45167956117393011881405413 8468991772011189727763515)
              ·
                refine ⟨12703487658016784591645273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468991772011189727763515 12703487658016784591645273)
                ·
                  refine ⟨9527615743512588443733955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12703487658016784591645273 9527615743512588443733955)
                  ·
                    refine ⟨14291423615268882665600933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9527615743512588443733955 14291423615268882665600933)
                    ·
                      refine ⟨2679641927862915499800175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14291423615268882665600933 2679641927862915499800175)
                      ·
                        rfl

theorem cell23_5218584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_5218584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218584 prefixEnd_5218584 := by exact prefixLift 5218584
  have htrace : WordTrace (prefixWord ++ tailWord_5218584) baseStart_5218584 baseEnd_5218584 := by
    simpa [prefixWord, tailWord_5218584, baseEnd_5218584] using wordTrace_append hprefix tailTrace_5218584
  have hstable : (prefixWord ++ tailWord_5218584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218584).length < 2 ^ (prefixWord ++ tailWord_5218584).sum := by decide
  have hdescent : baseEnd_5218584 < baseStart_5218584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218587 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 3]
def baseStart_5218587 : Nat := 118140960795 + 5218587 * 2 ^ 59
def prefixEnd_5218587 : Nat := 4983230072969 + 3 ^ 40 * 5218587 * 2
def baseEnd_5218587 : Nat := 2679643468304878988062661

theorem tailTrace_5218587 : CollatzResearch.WordTrace tailWord_5218587 prefixEnd_5218587 2679643468304878988062661 := by
  unfold tailWord_5218587
  simp only [CollatzResearch.WordTrace]
  refine ⟨190337504744958037547582015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126891669829972025031721343 190337504744958037547582015)
  ·
    refine ⟨285506257117437056321373023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190337504744958037547582015 285506257117437056321373023)
    ·
      refine ⟨428259385676155584482059535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285506257117437056321373023 428259385676155584482059535)
      ·
        refine ⟨642389078514233376723089303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428259385676155584482059535 642389078514233376723089303)
        ·
          refine ⟨963583617771350065084633955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642389078514233376723089303 963583617771350065084633955)
          ·
            refine ⟨1445375426657025097626950933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963583617771350065084633955 1445375426657025097626950933)
            ·
              refine ⟨67751973124548051451263325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1445375426657025097626950933 67751973124548051451263325)
              ·
                refine ⟨25406989921705519294223747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67751973124548051451263325 25406989921705519294223747)
                ·
                  refine ⟨38110484882558278941335621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25406989921705519294223747 38110484882558278941335621)
                  ·
                    refine ⟨7145715915479677301500429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38110484882558278941335621 7145715915479677301500429)
                    ·
                      refine ⟨2679643468304878988062661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145715915479677301500429 2679643468304878988062661)
                      ·
                        rfl

theorem cell23_5218587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 3].length) (baseStart_5218587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218587 prefixEnd_5218587 := by exact prefixLift 5218587
  have htrace : WordTrace (prefixWord ++ tailWord_5218587) baseStart_5218587 baseEnd_5218587 := by
    simpa [prefixWord, tailWord_5218587, baseEnd_5218587] using wordTrace_append hprefix tailTrace_5218587
  have hstable : (prefixWord ++ tailWord_5218587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218587).length < 2 ^ (prefixWord ++ tailWord_5218587).sum := by decide
  have hdescent : baseEnd_5218587 < baseStart_5218587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218604 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_5218604 : Nat := 118140960795 + 5218604 * 2 ^ 59
def prefixEnd_5218604 : Nat := 4983230072969 + 3 ^ 40 * 5218604 * 2
def baseEnd_5218604 : Nat := 2679652197476005421550083

theorem tailTrace_5218604 : CollatzResearch.WordTrace tailWord_5218604 prefixEnd_5218604 2679652197476005421550083 := by
  unfold tailWord_5218604
  simp only [CollatzResearch.WordTrace]
  refine ⟨95169062392948224725475433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126892083190597632967300577 95169062392948224725475433)
  ·
    refine ⟨71376796794711168544106575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95169062392948224725475433 71376796794711168544106575)
    ·
      refine ⟨107065195192066752816159863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71376796794711168544106575 107065195192066752816159863)
      ·
        refine ⟨160597792788100129224239795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107065195192066752816159863 160597792788100129224239795)
        ·
          refine ⟨240896689182150193836359693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160597792788100129224239795 240896689182150193836359693)
          ·
            refine ⟨90336258443306322688634885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240896689182150193836359693 90336258443306322688634885)
            ·
              refine ⟨16938048458119935504119041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90336258443306322688634885 16938048458119935504119041)
              ·
                refine ⟨12703536343589951628089281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16938048458119935504119041 12703536343589951628089281)
                ·
                  refine ⟨9527652257692463721066961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12703536343589951628089281 9527652257692463721066961)
                  ·
                    refine ⟨7145739193269347790800221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9527652257692463721066961 7145739193269347790800221)
                    ·
                      refine ⟨2679652197476005421550083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145739193269347790800221 2679652197476005421550083)
                      ·
                        rfl

theorem cell23_5218604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_5218604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218604 prefixEnd_5218604 := by exact prefixLift 5218604
  have htrace : WordTrace (prefixWord ++ tailWord_5218604) baseStart_5218604 baseEnd_5218604 := by
    simpa [prefixWord, tailWord_5218604, baseEnd_5218604] using wordTrace_append hprefix tailTrace_5218604
  have hstable : (prefixWord ++ tailWord_5218604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218604).length < 2 ^ (prefixWord ++ tailWord_5218604).sum := by decide
  have hdescent : baseEnd_5218604 < baseStart_5218604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218607 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 6]
def baseStart_5218607 : Nat := 118140960795 + 5218607 * 2 ^ 59
def prefixEnd_5218607 : Nat := 4983230072969 + 3 ^ 40 * 5218607 * 2
def baseEnd_5218607 : Nat := 297739304213107656645841

theorem tailTrace_5218607 : CollatzResearch.WordTrace tailWord_5218607 prefixEnd_5218607 297739304213107656645841 := by
  unfold tailWord_5218607
  simp only [CollatzResearch.WordTrace]
  refine ⟨190338234204885580963310075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126892156136590387308873383 190338234204885580963310075)
  ·
    refine ⟨285507351307328371444965113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190338234204885580963310075 285507351307328371444965113)
    ·
      refine ⟨214130513480496278583723835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285507351307328371444965113 214130513480496278583723835)
      ·
        refine ⟨321195770220744417875585753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214130513480496278583723835 321195770220744417875585753)
        ·
          refine ⟨240896827665558313406689315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321195770220744417875585753 240896827665558313406689315)
          ·
            refine ⟨361345241498337470110033973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240896827665558313406689315 361345241498337470110033973)
            ·
              refine ⟨33876116390469137822815685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 361345241498337470110033973 33876116390469137822815685)
              ·
                refine ⟨6351771823212963341777941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33876116390469137822815685 6351771823212963341777941)
                ·
                  refine ⟨297739304213107656645841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6351771823212963341777941 297739304213107656645841)
                  ·
                    rfl

theorem cell23_5218607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 6].length) (baseStart_5218607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218607 prefixEnd_5218607 := by exact prefixLift 5218607
  have htrace : WordTrace (prefixWord ++ tailWord_5218607) baseStart_5218607 baseEnd_5218607 := by
    simpa [prefixWord, tailWord_5218607, baseEnd_5218607] using wordTrace_append hprefix tailTrace_5218607
  have hstable : (prefixWord ++ tailWord_5218607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218607).length < 2 ^ (prefixWord ++ tailWord_5218607).sum := by decide
  have hdescent : baseEnd_5218607 < baseStart_5218607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218611 : List Nat := [1, 1, 1, 2, 5, 1, 3, 4, 1, 4]
def baseStart_5218611 : Nat := 118140960795 + 5218611 * 2 ^ 59
def prefixEnd_5218611 : Nat := 4983230072969 + 3 ^ 40 * 5218611 * 2
def baseEnd_5218611 : Nat := 893218597280195631387517

theorem tailTrace_5218611 : CollatzResearch.WordTrace tailWord_5218611 prefixEnd_5218611 893218597280195631387517 := by
  unfold tailWord_5218611
  simp only [CollatzResearch.WordTrace]
  refine ⟨190338380096871089646455687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126892253397914059764303791 190338380096871089646455687)
  ·
    refine ⟨285507570145306634469683531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190338380096871089646455687 285507570145306634469683531)
    ·
      refine ⟨428261355217959951704525297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285507570145306634469683531 428261355217959951704525297)
      ·
        refine ⟨321196016413469963778393973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428261355217959951704525297 321196016413469963778393973)
        ·
          refine ⟨30112126538762809104224435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 321196016413469963778393973 30112126538762809104224435)
          ·
            refine ⟨45168189808144213656336653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30112126538762809104224435 45168189808144213656336653)
            ·
              refine ⟨16938071178054080121126245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45168189808144213656336653 16938071178054080121126245)
              ·
                refine ⟨3175888345885140022711171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16938071178054080121126245 3175888345885140022711171)
                ·
                  refine ⟨4763832518827710034066757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175888345885140022711171 4763832518827710034066757)
                  ·
                    refine ⟨893218597280195631387517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763832518827710034066757 893218597280195631387517)
                    ·
                      rfl

theorem cell23_5218611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 4].length) (baseStart_5218611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218611 prefixEnd_5218611 := by exact prefixLift 5218611
  have htrace : WordTrace (prefixWord ++ tailWord_5218611) baseStart_5218611 baseEnd_5218611 := by
    simpa [prefixWord, tailWord_5218611, baseEnd_5218611] using wordTrace_append hprefix tailTrace_5218611
  have hstable : (prefixWord ++ tailWord_5218611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218611).length < 2 ^ (prefixWord ++ tailWord_5218611).sum := by decide
  have hdescent : baseEnd_5218611 < baseStart_5218611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218628 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5218628 : Nat := 118140960795 + 5218628 * 2 ^ 59
def prefixEnd_5218628 : Nat := 4983230072969 + 3 ^ 40 * 5218628 * 2
def baseEnd_5218628 : Nat := 893221507003904442549991

theorem tailTrace_5218628 : CollatzResearch.WordTrace tailWord_5218628 prefixEnd_5218628 893221507003904442549991 := by
  unfold tailWord_5218628
  simp only [CollatzResearch.WordTrace]
  refine ⟨95169500068904750774912269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126892666758539667699883025 95169500068904750774912269)
  ·
    refine ⟨35688562525839281540592101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95169500068904750774912269 35688562525839281540592101)
    ·
      refine ⟨6691605473594865288861019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35688562525839281540592101 6691605473594865288861019)
      ·
        refine ⟨10037408210392297933291529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691605473594865288861019 10037408210392297933291529)
        ·
          refine ⟨7528056157794223449968647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10037408210392297933291529 7528056157794223449968647)
          ·
            refine ⟨11292084236691335174952971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528056157794223449968647 11292084236691335174952971)
            ·
              refine ⟨16938126355037002762429457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11292084236691335174952971 16938126355037002762429457)
              ·
                refine ⟨12703594766277752071822093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16938126355037002762429457 12703594766277752071822093)
                ·
                  refine ⟨4763848037354157026933285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12703594766277752071822093 4763848037354157026933285)
                  ·
                    refine ⟨893221507003904442549991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763848037354157026933285 893221507003904442549991)
                    ·
                      rfl

theorem cell23_5218628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5218628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218628 prefixEnd_5218628 := by exact prefixLift 5218628
  have htrace : WordTrace (prefixWord ++ tailWord_5218628) baseStart_5218628 baseEnd_5218628 := by
    simpa [prefixWord, tailWord_5218628, baseEnd_5218628] using wordTrace_append hprefix tailTrace_5218628
  have hstable : (prefixWord ++ tailWord_5218628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218628).length < 2 ^ (prefixWord ++ tailWord_5218628).sum := by decide
  have hdescent : baseEnd_5218628 < baseStart_5218628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218668 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_5218668 : Nat := 118140960795 + 5218668 * 2 ^ 59
def prefixEnd_5218668 : Nat := 4983230072969 + 3 ^ 40 * 5218668 * 2
def baseEnd_5218668 : Nat := 2679685060237893171149789

theorem tailTrace_5218668 : CollatzResearch.WordTrace tailWord_5218668 prefixEnd_5218668 2679685060237893171149789 := by
  unfold tailWord_5218668
  simp only [CollatzResearch.WordTrace]
  refine ⟨95170229528832294190640329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126893639371776392254187105 95170229528832294190640329)
  ·
    refine ⟨71377672146624220642980247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95170229528832294190640329 71377672146624220642980247)
    ·
      refine ⟨107066508219936330964470371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71377672146624220642980247 107066508219936330964470371)
      ·
        refine ⟨160599762329904496446705557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107066508219936330964470371 160599762329904496446705557)
        ·
          refine ⟨7528113859214273270939323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160599762329904496446705557 7528113859214273270939323)
          ·
            refine ⟨11292170788821409906408985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528113859214273270939323 11292170788821409906408985)
            ·
              refine ⟨8469128091616057429806739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11292170788821409906408985 8469128091616057429806739)
              ·
                refine ⟨12703692137424086144710109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8469128091616057429806739 12703692137424086144710109)
                ·
                  refine ⟨4763884551534032304266291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12703692137424086144710109 4763884551534032304266291)
                  ·
                    refine ⟨7145826827301048456399437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4763884551534032304266291 7145826827301048456399437)
                    ·
                      refine ⟨2679685060237893171149789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145826827301048456399437 2679685060237893171149789)
                      ·
                        rfl

theorem cell23_5218668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_5218668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218668 prefixEnd_5218668 := by exact prefixLift 5218668
  have htrace : WordTrace (prefixWord ++ tailWord_5218668) baseStart_5218668 baseEnd_5218668 := by
    simpa [prefixWord, tailWord_5218668, baseEnd_5218668] using wordTrace_append hprefix tailTrace_5218668
  have hstable : (prefixWord ++ tailWord_5218668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218668).length < 2 ^ (prefixWord ++ tailWord_5218668).sum := by decide
  have hdescent : baseEnd_5218668 < baseStart_5218668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218687 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_5218687 : Nat := 118140960795 + 5218687 * 2 ^ 59
def prefixEnd_5218687 : Nat := 4983230072969 + 3 ^ 40 * 5218687 * 2
def baseEnd_5218687 : Nat := 2679694816370328596812201

theorem tailTrace_5218687 : CollatzResearch.WordTrace tailWord_5218687 prefixEnd_5218687 2679694816370328596812201 := by
  unfold tailWord_5218687
  simp only [CollatzResearch.WordTrace]
  refine ⟨190341152044595754626222315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126894101363063836417481543 190341152044595754626222315)
  ·
    refine ⟨285511728066893631939333473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190341152044595754626222315 285511728066893631939333473)
    ·
      refine ⟨214133796050170223954500105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285511728066893631939333473 214133796050170223954500105)
      ·
        refine ⟨160600347037627667965875079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214133796050170223954500105 160600347037627667965875079)
        ·
          refine ⟨240900520556441501948812619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160600347037627667965875079 240900520556441501948812619)
          ·
            refine ⟨361350780834662252923218929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240900520556441501948812619 361350780834662252923218929)
            ·
              refine ⟨271013085625996689692414197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361350780834662252923218929 271013085625996689692414197)
              ·
                refine ⟨25407476777437189658663831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 271013085625996689692414197 25407476777437189658663831)
                ·
                  refine ⟨38111215166155784487995747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25407476777437189658663831 38111215166155784487995747)
                  ·
                    refine ⟨57166822749233676731993621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38111215166155784487995747 57166822749233676731993621)
                    ·
                      refine ⟨2679694816370328596812201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57166822749233676731993621 2679694816370328596812201)
                      ·
                        rfl

theorem cell23_5218687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_5218687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218687 prefixEnd_5218687 := by exact prefixLift 5218687
  have htrace : WordTrace (prefixWord ++ tailWord_5218687) baseStart_5218687 baseEnd_5218687 := by
    simpa [prefixWord, tailWord_5218687, baseEnd_5218687] using wordTrace_append hprefix tailTrace_5218687
  have hstable : (prefixWord ++ tailWord_5218687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218687).length < 2 ^ (prefixWord ++ tailWord_5218687).sum := by decide
  have hdescent : baseEnd_5218687 < baseStart_5218687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218702 : List Nat := [4, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5218702 : Nat := 118140960795 + 5218702 * 2 ^ 59
def prefixEnd_5218702 : Nat := 4983230072969 + 3 ^ 40 * 5218702 * 2
def baseEnd_5218702 : Nat := 2679702518580146038124633

theorem tailTrace_5218702 : CollatzResearch.WordTrace tailWord_5218702 prefixEnd_5218702 2679702518580146038124633 := by
  unfold tailWord_5218702
  simp only [CollatzResearch.WordTrace]
  refine ⟨23792712392442676523502295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126894466093027608125345573 23792712392442676523502295)
  ·
    refine ⟨35689068588664014785253443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23792712392442676523502295 35689068588664014785253443)
    ·
      refine ⟨53533602882996022177880165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35689068588664014785253443 53533602882996022177880165)
      ·
        refine ⟨10037550540561754158352531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53533602882996022177880165 10037550540561754158352531)
        ·
          refine ⟨15056325810842631237528797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10037550540561754158352531 15056325810842631237528797)
          ·
            refine ⟨5646122179065986714073299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15056325810842631237528797 5646122179065986714073299)
            ·
              refine ⟨8469183268598980071109949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646122179065986714073299 8469183268598980071109949)
              ·
                refine ⟨3175943725724617526666231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8469183268598980071109949 3175943725724617526666231)
                ·
                  refine ⟨4763915588586926289999347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175943725724617526666231 4763915588586926289999347)
                  ·
                    refine ⟨7145873382880389434999021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4763915588586926289999347 7145873382880389434999021)
                    ·
                      refine ⟨2679702518580146038124633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145873382880389434999021 2679702518580146038124633)
                      ·
                        rfl

theorem cell23_5218702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5218702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218702 prefixEnd_5218702 := by exact prefixLift 5218702
  have htrace : WordTrace (prefixWord ++ tailWord_5218702) baseStart_5218702 baseEnd_5218702 := by
    simpa [prefixWord, tailWord_5218702, baseEnd_5218702] using wordTrace_append hprefix tailTrace_5218702
  have hstable : (prefixWord ++ tailWord_5218702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218702).length < 2 ^ (prefixWord ++ tailWord_5218702).sum := by decide
  have hdescent : baseEnd_5218702 < baseStart_5218702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218711 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_5218711 : Nat := 118140960795 + 5218711 * 2 ^ 59
def prefixEnd_5218711 : Nat := 4983230072969 + 3 ^ 40 * 5218711 * 2
def baseEnd_5218711 : Nat := 2679707139906036502912091

theorem tailTrace_5218711 : CollatzResearch.WordTrace tailWord_5218711 prefixEnd_5218711 2679707139906036502912091 := by
  unfold tailWord_5218711
  simp only [CollatzResearch.WordTrace]
  refine ⟨190342027396508806725095987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126894684931005871150063991 190342027396508806725095987)
  ·
    refine ⟨285513041094763210087643981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190342027396508806725095987 285513041094763210087643981)
    ·
      refine ⟨107067390410536203782866493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285513041094763210087643981 107067390410536203782866493)
      ·
        refine ⟨40150271403951076418574935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107067390410536203782866493 40150271403951076418574935)
        ·
          refine ⟨60225407105926614627862403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40150271403951076418574935 60225407105926614627862403)
          ·
            refine ⟨90338110658889921941793605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60225407105926614627862403 90338110658889921941793605)
            ·
              refine ⟨16938395748541860364086301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90338110658889921941793605 16938395748541860364086301)
              ·
                refine ⟨6351898405703197636532363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16938395748541860364086301 6351898405703197636532363)
                ·
                  refine ⟨9527847608554796454798545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6351898405703197636532363 9527847608554796454798545)
                  ·
                    refine ⟨7145885706416097341098909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9527847608554796454798545 7145885706416097341098909)
                    ·
                      refine ⟨2679707139906036502912091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145885706416097341098909 2679707139906036502912091)
                      ·
                        rfl

theorem cell23_5218711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_5218711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218711 prefixEnd_5218711 := by exact prefixLift 5218711
  have htrace : WordTrace (prefixWord ++ tailWord_5218711) baseStart_5218711 baseEnd_5218711 := by
    simpa [prefixWord, tailWord_5218711, baseEnd_5218711] using wordTrace_append hprefix tailTrace_5218711
  have hstable : (prefixWord ++ tailWord_5218711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218711).length < 2 ^ (prefixWord ++ tailWord_5218711).sum := by decide
  have hdescent : baseEnd_5218711 < baseStart_5218711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218714 : List Nat := [3, 1, 1, 4, 1, 4, 9]
def baseStart_5218714 : Nat := 118140960795 + 5218714 * 2 ^ 59
def prefixEnd_5218714 : Nat := 4983230072969 + 3 ^ 40 * 5218714 * 2
def baseEnd_5218714 : Nat := 33082823214172839397217

theorem tailTrace_5218714 : CollatzResearch.WordTrace tailWord_5218714 prefixEnd_5218714 33082823214172839397217 := by
  unfold tailWord_5218714
  simp only [CollatzResearch.WordTrace]
  refine ⟨47585534203874484559363799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126894757876998625491636797 47585534203874484559363799)
  ·
    refine ⟨71378301305811726839045699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47585534203874484559363799 71378301305811726839045699)
    ·
      refine ⟨107067451958717590258568549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71378301305811726839045699 107067451958717590258568549)
      ·
        refine ⟨20075147242259548173481603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107067451958717590258568549 20075147242259548173481603)
        ·
          refine ⟨30112720863389322260222405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20075147242259548173481603 30112720863389322260222405)
          ·
            refine ⟨5646135161885497923791701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30112720863389322260222405 5646135161885497923791701)
            ·
              refine ⟨33082823214172839397217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5646135161885497923791701 33082823214172839397217)
              ·
                rfl

theorem cell23_5218714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 9].length) (baseStart_5218714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218714 prefixEnd_5218714 := by exact prefixLift 5218714
  have htrace : WordTrace (prefixWord ++ tailWord_5218714) baseStart_5218714 baseEnd_5218714 := by
    simpa [prefixWord, tailWord_5218714, baseEnd_5218714] using wordTrace_append hprefix tailTrace_5218714
  have hstable : (prefixWord ++ tailWord_5218714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218714).length < 2 ^ (prefixWord ++ tailWord_5218714).sum := by decide
  have hdescent : baseEnd_5218714 < baseStart_5218714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218718 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_5218718 : Nat := 118140960795 + 5218718 * 2 ^ 59
def prefixEnd_5218718 : Nat := 4983230072969 + 3 ^ 40 * 5218718 * 2
def baseEnd_5218718 : Nat := 893236911423539325174853

theorem tailTrace_5218718 : CollatzResearch.WordTrace tailWord_5218718 prefixEnd_5218718 893236911423539325174853 := by
  unfold tailWord_5218718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23792785338435430865075101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126894855138322297947067205 23792785338435430865075101)
  ·
    refine ⟨8922294501913286574403163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23792785338435430865075101 8922294501913286574403163)
    ·
      refine ⟨13383441752869929861604745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8922294501913286574403163 13383441752869929861604745)
      ·
        refine ⟨10037581314652447396203559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13383441752869929861604745 10037581314652447396203559)
        ·
          refine ⟨15056371971978671094305339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10037581314652447396203559 15056371971978671094305339)
          ·
            refine ⟨22584557957968006641458009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15056371971978671094305339 22584557957968006641458009)
            ·
              refine ⟨16938418468476004981093507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22584557957968006641458009 16938418468476004981093507)
              ·
                refine ⟨25407627702714007471640261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16938418468476004981093507 25407627702714007471640261)
                ·
                  refine ⟨4763930194258876400932549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25407627702714007471640261 4763930194258876400932549)
                  ·
                    refine ⟨893236911423539325174853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763930194258876400932549 893236911423539325174853)
                    ·
                      rfl

theorem cell23_5218718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_5218718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218718 prefixEnd_5218718 := by exact prefixLift 5218718
  have htrace : WordTrace (prefixWord ++ tailWord_5218718) baseStart_5218718 baseEnd_5218718 := by
    simpa [prefixWord, tailWord_5218718, baseEnd_5218718] using wordTrace_append hprefix tailTrace_5218718
  have hstable : (prefixWord ++ tailWord_5218718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218718).length < 2 ^ (prefixWord ++ tailWord_5218718).sum := by decide
  have hdescent : baseEnd_5218718 < baseStart_5218718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218784 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3]
def baseStart_5218784 : Nat := 118140960795 + 5218784 * 2 ^ 59
def prefixEnd_5218784 : Nat := 4983230072969 + 3 ^ 40 * 5218784 * 2
def baseEnd_5218784 : Nat := 2679744623993814717299255

theorem tailTrace_5218784 : CollatzResearch.WordTrace tailWord_5218784 prefixEnd_5218784 2679744623993814717299255 := by
  unfold tailWord_5218784
  simp only [CollatzResearch.WordTrace]
  refine ⟨95172344962622170096251703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126896459950162893461668937 95172344962622170096251703)
  ·
    refine ⟨142758517443933255144377555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95172344962622170096251703 142758517443933255144377555)
    ·
      refine ⟨214137776165899882716566333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142758517443933255144377555 214137776165899882716566333)
      ·
        refine ⟨80301666062212456018712375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214137776165899882716566333 80301666062212456018712375)
        ·
          refine ⟨120452499093318684028068563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80301666062212456018712375 120452499093318684028068563)
          ·
            refine ⟨180678748639978026042102845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120452499093318684028068563 180678748639978026042102845)
            ·
              refine ⟨67754530739991759765788567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180678748639978026042102845 67754530739991759765788567)
              ·
                refine ⟨101631796109987639648682851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67754530739991759765788567 101631796109987639648682851)
                ·
                  refine ⟨152447694164981459473024277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101631796109987639648682851 152447694164981459473024277)
                  ·
                    refine ⟨7145985663983505912798013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 152447694164981459473024277 7145985663983505912798013)
                    ·
                      refine ⟨2679744623993814717299255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7145985663983505912798013 2679744623993814717299255)
                      ·
                        rfl

theorem cell23_5218784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_5218784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218784 prefixEnd_5218784 := by exact prefixLift 5218784
  have htrace : WordTrace (prefixWord ++ tailWord_5218784) baseStart_5218784 baseEnd_5218784 := by
    simpa [prefixWord, tailWord_5218784, baseEnd_5218784] using wordTrace_append hprefix tailTrace_5218784
  have hstable : (prefixWord ++ tailWord_5218784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218784).length < 2 ^ (prefixWord ++ tailWord_5218784).sum := by decide
  have hdescent : baseEnd_5218784 < baseStart_5218784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218798 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_5218798 : Nat := 118140960795 + 5218798 * 2 ^ 59
def prefixEnd_5218798 : Nat := 4983230072969 + 3 ^ 40 * 5218798 * 2
def baseEnd_5218798 : Nat := 2679751812722977662524191

theorem tailTrace_5218798 : CollatzResearch.WordTrace tailWord_5218798 prefixEnd_5218798 2679751812722977662524191 := by
  unfold tailWord_5218798
  simp only [CollatzResearch.WordTrace]
  refine ⟨23793150068399202572939131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126896800364795747055675365 23793150068399202572939131)
  ·
    refine ⟨35689725102598803859408697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23793150068399202572939131 35689725102598803859408697)
    ·
      refine ⟨26767293826949102894556523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35689725102598803859408697 26767293826949102894556523)
      ·
        refine ⟨40150940740423654341834785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26767293826949102894556523 40150940740423654341834785)
        ·
          refine ⟨30113205555317740756376089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40150940740423654341834785 30113205555317740756376089)
          ·
            refine ⟨22584904166488305567282067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30113205555317740756376089 22584904166488305567282067)
            ·
              refine ⟨33877356249732458350923101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22584904166488305567282067 33877356249732458350923101)
              ·
                refine ⟨12704008593649671881596163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33877356249732458350923101 12704008593649671881596163)
                ·
                  refine ⟨19056012890474507822394245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12704008593649671881596163 19056012890474507822394245)
                  ·
                    refine ⟨3573002416963970216698921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19056012890474507822394245 3573002416963970216698921)
                    ·
                      refine ⟨2679751812722977662524191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573002416963970216698921 2679751812722977662524191)
                      ·
                        rfl

theorem cell23_5218798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_5218798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218798 prefixEnd_5218798 := by exact prefixLift 5218798
  have htrace : WordTrace (prefixWord ++ tailWord_5218798) baseStart_5218798 baseEnd_5218798 := by
    simpa [prefixWord, tailWord_5218798, baseEnd_5218798] using wordTrace_append hprefix tailTrace_5218798
  have hstable : (prefixWord ++ tailWord_5218798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218798).length < 2 ^ (prefixWord ++ tailWord_5218798).sum := by decide
  have hdescent : baseEnd_5218798 < baseStart_5218798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218821 : List Nat := [1, 3, 1, 1, 2, 2, 3, 5, 5]
def baseStart_5218821 : Nat := 118140960795 + 5218821 * 2 ^ 59
def prefixEnd_5218821 : Nat := 4983230072969 + 3 ^ 40 * 5218821 * 2
def baseEnd_5218821 : Nat := 297751513642003452504065

theorem tailTrace_5218821 : CollatzResearch.WordTrace tailWord_5218821 prefixEnd_5218821 297751513642003452504065 := by
  unfold tailWord_5218821
  simp only [CollatzResearch.WordTrace]
  refine ⟨190346039426110295511600317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126897359617406863674400211 190346039426110295511600317)
  ·
    refine ⟨71379764784791360816850119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190346039426110295511600317 71379764784791360816850119)
    ·
      refine ⟨107069647177187041225275179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71379764784791360816850119 107069647177187041225275179)
      ·
        refine ⟨160604470765780561837912769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107069647177187041225275179 160604470765780561837912769)
        ·
          refine ⟨120453353074335421378434577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160604470765780561837912769 120453353074335421378434577)
          ·
            refine ⟨90340014805751566033825933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120453353074335421378434577 90340014805751566033825933)
            ·
              refine ⟨33877505552156837262684725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90340014805751566033825933 33877505552156837262684725)
              ·
                refine ⟨3176016145514703493376693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33877505552156837262684725 3176016145514703493376693)
                ·
                  refine ⟨297751513642003452504065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3176016145514703493376693 297751513642003452504065)
                  ·
                    rfl

theorem cell23_5218821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_5218821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218821 prefixEnd_5218821 := by exact prefixLift 5218821
  have htrace : WordTrace (prefixWord ++ tailWord_5218821) baseStart_5218821 baseEnd_5218821 := by
    simpa [prefixWord, tailWord_5218821, baseEnd_5218821] using wordTrace_append hprefix tailTrace_5218821
  have hstable : (prefixWord ++ tailWord_5218821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218821).length < 2 ^ (prefixWord ++ tailWord_5218821).sum := by decide
  have hdescent : baseEnd_5218821 < baseStart_5218821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218871 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_5218871 : Nat := 118140960795 + 5218871 * 2 ^ 59
def prefixEnd_5218871 : Nat := 4983230072969 + 3 ^ 40 * 5218871 * 2
def baseEnd_5218871 : Nat := 2679789296810755876911355

theorem tailTrace_5218871 : CollatzResearch.WordTrace tailWord_5218871 prefixEnd_5218871 2679789296810755876911355 := by
  unfold tailWord_5218871
  simp only [CollatzResearch.WordTrace]
  refine ⟨190347863075929154050920467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126898575383952769367280311 190347863075929154050920467)
  ·
    refine ⟨285521794613893731076380701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190347863075929154050920467 285521794613893731076380701)
    ·
      refine ⟨107070672980210149153642763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285521794613893731076380701 107070672980210149153642763)
      ·
        refine ⟨160606009470315223730464145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107070672980210149153642763 160606009470315223730464145)
        ·
          refine ⟨120454507102736417797848109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160606009470315223730464145 120454507102736417797848109)
          ·
            refine ⟨45170440163526156674193041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120454507102736417797848109 45170440163526156674193041)
            ·
              refine ⟨33877830122644617505644781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45170440163526156674193041 33877830122644617505644781)
              ·
                refine ⟨12704186295991731564616793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33877830122644617505644781 12704186295991731564616793)
                ·
                  refine ⟨9528139721993798673462595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12704186295991731564616793 9528139721993798673462595)
                  ·
                    refine ⟨14292209582990698010193893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9528139721993798673462595 14292209582990698010193893)
                    ·
                      refine ⟨2679789296810755876911355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14292209582990698010193893 2679789296810755876911355)
                      ·
                        rfl

theorem cell23_5218871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_5218871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218871 prefixEnd_5218871 := by exact prefixLift 5218871
  have htrace : WordTrace (prefixWord ++ tailWord_5218871) baseStart_5218871 baseEnd_5218871 := by
    simpa [prefixWord, tailWord_5218871, baseEnd_5218871] using wordTrace_append hprefix tailTrace_5218871
  have hstable : (prefixWord ++ tailWord_5218871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218871).length < 2 ^ (prefixWord ++ tailWord_5218871).sum := by decide
  have hdescent : baseEnd_5218871 < baseStart_5218871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218891 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 3]
def baseStart_5218891 : Nat := 118140960795 + 5218891 * 2 ^ 59
def prefixEnd_5218891 : Nat := 4983230072969 + 3 ^ 40 * 5218891 * 2
def baseEnd_5218891 : Nat := 2679799566423845798661263

theorem tailTrace_5218891 : CollatzResearch.WordTrace tailWord_5218891 prefixEnd_5218891 2679799566423845798661263 := by
  unfold tailWord_5218891
  simp only [CollatzResearch.WordTrace]
  refine ⟨190348592535856697466648527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126899061690571131644432351 190348592535856697466648527)
  ·
    refine ⟨285522888803785046199972791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190348592535856697466648527 285522888803785046199972791)
    ·
      refine ⟨428284333205677569299959187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285522888803785046199972791 428284333205677569299959187)
      ·
        refine ⟨642426499808516353949938781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428284333205677569299959187 642426499808516353949938781)
        ·
          refine ⟨240909937428193632731227043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642426499808516353949938781 240909937428193632731227043)
          ·
            refine ⟨361364906142290449096840565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240909937428193632731227043 361364906142290449096840565)
            ·
              refine ⟨33877959950839729602828803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 361364906142290449096840565 33877959950839729602828803)
              ·
                refine ⟨50816939926259594404243205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33877959950839729602828803 50816939926259594404243205)
                ·
                  refine ⟨9528176236173673950795601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50816939926259594404243205 9528176236173673950795601)
                  ·
                    refine ⟨7146132177130255463096701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9528176236173673950795601 7146132177130255463096701)
                    ·
                      refine ⟨2679799566423845798661263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146132177130255463096701 2679799566423845798661263)
                      ·
                        rfl

theorem cell23_5218891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 3].length) (baseStart_5218891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218891 prefixEnd_5218891 := by exact prefixLift 5218891
  have htrace : WordTrace (prefixWord ++ tailWord_5218891) baseStart_5218891 baseEnd_5218891 := by
    simpa [prefixWord, tailWord_5218891, baseEnd_5218891] using wordTrace_append hprefix tailTrace_5218891
  have hstable : (prefixWord ++ tailWord_5218891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218891).length < 2 ^ (prefixWord ++ tailWord_5218891).sum := by decide
  have hdescent : baseEnd_5218891 < baseStart_5218891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218925 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_5218925 : Nat := 118140960795 + 5218925 * 2 ^ 59
def prefixEnd_5218925 : Nat := 4983230072969 + 3 ^ 40 * 5218925 * 2
def baseEnd_5218925 : Nat := 2679817024766098665636107

theorem tailTrace_5218925 : CollatzResearch.WordTrace tailWord_5218925 prefixEnd_5218925 2679817024766098665636107 := by
  unfold tailWord_5218925
  simp only [CollatzResearch.WordTrace]
  refine ⟨190349832617733521273386229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126899888411822347515590819 190349832617733521273386229)
  ·
    refine ⟨17845296807912517619379959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190349832617733521273386229 17845296807912517619379959)
    ·
      refine ⟨26767945211868776429069939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17845296807912517619379959 26767945211868776429069939)
      ·
        refine ⟨40151917817803164643604909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26767945211868776429069939 40151917817803164643604909)
        ·
          refine ⟨15056969181676186741351841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40151917817803164643604909 15056969181676186741351841)
          ·
            refine ⟨11292726886257140056013881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15056969181676186741351841 11292726886257140056013881)
            ·
              refine ⟨8469545164692855042010411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11292726886257140056013881 8469545164692855042010411)
              ·
                refine ⟨12704317747039282563015617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8469545164692855042010411 12704317747039282563015617)
                ·
                  refine ⟨9528238310279461922261713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12704317747039282563015617 9528238310279461922261713)
                  ·
                    refine ⟨7146178732709596441696285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9528238310279461922261713 7146178732709596441696285)
                    ·
                      refine ⟨2679817024766098665636107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146178732709596441696285 2679817024766098665636107)
                      ·
                        rfl

theorem cell23_5218925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_5218925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218925 prefixEnd_5218925 := by exact prefixLift 5218925
  have htrace : WordTrace (prefixWord ++ tailWord_5218925) baseStart_5218925 baseEnd_5218925 := by
    simpa [prefixWord, tailWord_5218925, baseEnd_5218925] using wordTrace_append hprefix tailTrace_5218925
  have hstable : (prefixWord ++ tailWord_5218925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218925).length < 2 ^ (prefixWord ++ tailWord_5218925).sum := by decide
  have hdescent : baseEnd_5218925 < baseStart_5218925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218989 : List Nat := [1, 5, 2, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_5218989 : Nat := 118140960795 + 5218989 * 2 ^ 59
def prefixEnd_5218989 : Nat := 4983230072969 + 3 ^ 40 * 5218989 * 2
def baseEnd_5218989 : Nat := 2679849887527986415235813

theorem tailTrace_5218989 : CollatzResearch.WordTrace tailWord_5218989 prefixEnd_5218989 2679849887527986415235813 := by
  unfold tailWord_5218989
  simp only [CollatzResearch.WordTrace]
  refine ⟨190352166889501660203716021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126901444593001106802477347 190352166889501660203716021)
  ·
    refine ⟨17845515645890780644098377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190352166889501660203716021 17845515645890780644098377)
    ·
      refine ⟨13384136734418085483073783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17845515645890780644098377 13384136734418085483073783)
      ·
        refine ⟨20076205101627128224610675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13384136734418085483073783 20076205101627128224610675)
        ·
          refine ⟨30114307652440692336916013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20076205101627128224610675 30114307652440692336916013)
          ·
            refine ⟨11292865369665259626343505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30114307652440692336916013 11292865369665259626343505)
            ·
              refine ⟨8469649027248944719757629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11292865369665259626343505 8469649027248944719757629)
              ·
                refine ⟨3176118385218354269909111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8469649027248944719757629 3176118385218354269909111)
                ·
                  refine ⟨4764177577827531404863667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176118385218354269909111 4764177577827531404863667)
                  ·
                    refine ⟨7146266366741297107295501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764177577827531404863667 7146266366741297107295501)
                    ·
                      refine ⟨2679849887527986415235813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146266366741297107295501 2679849887527986415235813)
                      ·
                        rfl

theorem cell23_5218989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_5218989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218989 prefixEnd_5218989 := by exact prefixLift 5218989
  have htrace : WordTrace (prefixWord ++ tailWord_5218989) baseStart_5218989 baseEnd_5218989 := by
    simpa [prefixWord, tailWord_5218989, baseEnd_5218989] using wordTrace_append hprefix tailTrace_5218989
  have hstable : (prefixWord ++ tailWord_5218989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218989).length < 2 ^ (prefixWord ++ tailWord_5218989).sum := by decide
  have hdescent : baseEnd_5218989 < baseStart_5218989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5218995 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 1, 1, 4]
def baseStart_5218995 : Nat := 118140960795 + 5218995 * 2 ^ 59
def prefixEnd_5218995 : Nat := 4983230072969 + 3 ^ 40 * 5218995 * 2
def baseEnd_5218995 : Nat := 2679852968411913391760785

theorem tailTrace_5218995 : CollatzResearch.WordTrace tailWord_5218995 prefixEnd_5218995 2679852968411913391760785 := by
  unfold tailWord_5218995
  simp only [CollatzResearch.WordTrace]
  refine ⟨190352385727479923228434439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126901590484986615485622959 190352385727479923228434439)
  ·
    refine ⟨285528578591219884842651659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190352385727479923228434439 285528578591219884842651659)
    ·
      refine ⟨428292867886829827263977489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285528578591219884842651659 428292867886829827263977489)
      ·
        refine ⟨321219650915122370447983117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428292867886829827263977489 321219650915122370447983117)
        ·
          refine ⟨120457369093170888917993669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321219650915122370447983117 120457369093170888917993669)
          ·
            refine ⟨22585756704969541672123813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120457369093170888917993669 22585756704969541672123813)
            ·
              refine ⟨4234829382181789063523215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22585756704969541672123813 4234829382181789063523215)
              ·
                refine ⟨6352244073272683595284823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234829382181789063523215 6352244073272683595284823)
                ·
                  refine ⟨9528366109909025392927235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6352244073272683595284823 9528366109909025392927235)
                  ·
                    refine ⟨14292549164863538089390853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9528366109909025392927235 14292549164863538089390853)
                    ·
                      refine ⟨2679852968411913391760785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14292549164863538089390853 2679852968411913391760785)
                      ·
                        rfl

theorem cell23_5218995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 1, 4].length) (baseStart_5218995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5218995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5218995 prefixEnd_5218995 := by exact prefixLift 5218995
  have htrace : WordTrace (prefixWord ++ tailWord_5218995) baseStart_5218995 baseEnd_5218995 := by
    simpa [prefixWord, tailWord_5218995, baseEnd_5218995] using wordTrace_append hprefix tailTrace_5218995
  have hstable : (prefixWord ++ tailWord_5218995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5218995).length < 2 ^ (prefixWord ++ tailWord_5218995).sum := by decide
  have hdescent : baseEnd_5218995 < baseStart_5218995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5218995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219005 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_5219005 : Nat := 118140960795 + 5219005 * 2 ^ 59
def prefixEnd_5219005 : Nat := 4983230072969 + 3 ^ 40 * 5219005 * 2
def baseEnd_5219005 : Nat := 893286034406152784211913

theorem tailTrace_5219005 : CollatzResearch.WordTrace tailWord_5219005 prefixEnd_5219005 893286034406152784211913 := by
  unfold tailWord_5219005
  simp only [CollatzResearch.WordTrace]
  refine ⟨190352750457443694936298469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126901833638295796624198979 190352750457443694936298469)
  ·
    refine ⟨35691140710770692800555963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190352750457443694936298469 35691140710770692800555963)
    ·
      refine ⟨53536711066156039200833945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35691140710770692800555963 53536711066156039200833945)
      ·
        refine ⟨40152533299617029400625459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53536711066156039200833945 40152533299617029400625459)
        ·
          refine ⟨60228799949425544100938189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40152533299617029400625459 60228799949425544100938189)
          ·
            refine ⟨22585799981034579037851821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60228799949425544100938189 22585799981034579037851821)
            ·
              refine ⟨8469674992887967139194433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22585799981034579037851821 8469674992887967139194433)
              ·
                refine ⟨6352256244665975354395825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8469674992887967139194433 6352256244665975354395825)
                ·
                  refine ⟨4764192183499481515796869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352256244665975354395825 4764192183499481515796869)
                  ·
                    refine ⟨893286034406152784211913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764192183499481515796869 893286034406152784211913)
                    ·
                      rfl

theorem cell23_5219005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_5219005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219005 prefixEnd_5219005 := by exact prefixLift 5219005
  have htrace : WordTrace (prefixWord ++ tailWord_5219005) baseStart_5219005 baseEnd_5219005 := by
    simpa [prefixWord, tailWord_5219005, baseEnd_5219005] using wordTrace_append hprefix tailTrace_5219005
  have hstable : (prefixWord ++ tailWord_5219005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219005).length < 2 ^ (prefixWord ++ tailWord_5219005).sum := by decide
  have hdescent : baseEnd_5219005 < baseStart_5219005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219011 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 3]
def baseStart_5219011 : Nat := 118140960795 + 5219011 * 2 ^ 59
def prefixEnd_5219011 : Nat := 4983230072969 + 3 ^ 40 * 5219011 * 2
def baseEnd_5219011 : Nat := 2679861184102385329160711

theorem tailTrace_5219011 : CollatzResearch.WordTrace tailWord_5219011 prefixEnd_5219011 2679861184102385329160711 := by
  unfold tailWord_5219011
  simp only [CollatzResearch.WordTrace]
  refine ⟨190352969295421957961016887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126901979530281305307344591 190352969295421957961016887)
  ·
    refine ⟨285529453943132936941525331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190352969295421957961016887 285529453943132936941525331)
    ·
      refine ⟨428294180914699405412287997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285529453943132936941525331 428294180914699405412287997)
      ·
        refine ⟨160610317843012277029607999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428294180914699405412287997 160610317843012277029607999)
        ·
          refine ⟨240915476764518415544411999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160610317843012277029607999 240915476764518415544411999)
          ·
            refine ⟨361373215146777623316617999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240915476764518415544411999 361373215146777623316617999)
            ·
              refine ⟨542059822720166434974926999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361373215146777623316617999 542059822720166434974926999)
              ·
                refine ⟨813089734080249652462390499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542059822720166434974926999 813089734080249652462390499)
                ·
                  refine ⟨1219634601120374478693585749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813089734080249652462390499 1219634601120374478693585749)
                  ·
                    refine ⟨7146296490939694211095229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1219634601120374478693585749 7146296490939694211095229)
                    ·
                      refine ⟨2679861184102385329160711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146296490939694211095229 2679861184102385329160711)
                      ·
                        rfl

theorem cell23_5219011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_5219011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219011 prefixEnd_5219011 := by exact prefixLift 5219011
  have htrace : WordTrace (prefixWord ++ tailWord_5219011) baseStart_5219011 baseEnd_5219011 := by
    simpa [prefixWord, tailWord_5219011, baseEnd_5219011] using wordTrace_append hprefix tailTrace_5219011
  have hstable : (prefixWord ++ tailWord_5219011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219011).length < 2 ^ (prefixWord ++ tailWord_5219011).sum := by decide
  have hdescent : baseEnd_5219011 < baseStart_5219011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219012 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_5219012 : Nat := 118140960795 + 5219012 * 2 ^ 59
def prefixEnd_5219012 : Nat := 4983230072969 + 3 ^ 40 * 5219012 * 2
def baseEnd_5219012 : Nat := 2679861697583039825248207

theorem tailTrace_5219012 : CollatzResearch.WordTrace tailWord_5219012 prefixEnd_5219012 2679861697583039825248207 := by
  unfold tailWord_5219012
  simp only [CollatzResearch.WordTrace]
  refine ⟨95176502884209167565901645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126902003845612223421202193 95176502884209167565901645)
  ·
    refine ⟨35691188581578437837213117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95176502884209167565901645 35691188581578437837213117)
    ·
      refine ⟨13384195718091914188954919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35691188581578437837213117 13384195718091914188954919)
      ·
        refine ⟨20076293577137871283432379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13384195718091914188954919 20076293577137871283432379)
        ·
          refine ⟨30114440365706806925148569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20076293577137871283432379 30114440365706806925148569)
          ·
            refine ⟨22585830274280105193861427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30114440365706806925148569 22585830274280105193861427)
            ·
              refine ⟨33878745411420157790792141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22585830274280105193861427 33878745411420157790792141)
              ·
                refine ⟨12704529529282559171547053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33878745411420157790792141 12704529529282559171547053)
                ·
                  refine ⟨4764198573480959689330145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12704529529282559171547053 4764198573480959689330145)
                  ·
                    refine ⟨3573148930110719766997609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4764198573480959689330145 3573148930110719766997609)
                    ·
                      refine ⟨2679861697583039825248207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573148930110719766997609 2679861697583039825248207)
                      ·
                        rfl

theorem cell23_5219012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_5219012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219012 prefixEnd_5219012 := by exact prefixLift 5219012
  have htrace : WordTrace (prefixWord ++ tailWord_5219012) baseStart_5219012 baseEnd_5219012 := by
    simpa [prefixWord, tailWord_5219012, baseEnd_5219012] using wordTrace_append hprefix tailTrace_5219012
  have hstable : (prefixWord ++ tailWord_5219012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219012).length < 2 ^ (prefixWord ++ tailWord_5219012).sum := by decide
  have hdescent : baseEnd_5219012 < baseStart_5219012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219022 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_5219022 : Nat := 118140960795 + 5219022 * 2 ^ 59
def prefixEnd_5219022 : Nat := 4983230072969 + 3 ^ 40 * 5219022 * 2
def baseEnd_5219022 : Nat := 893288944129861595374387

theorem tailTrace_5219022 : CollatzResearch.WordTrace tailWord_5219022 prefixEnd_5219022 893288944129861595374387 := by
  unfold tailWord_5219022
  simp only [CollatzResearch.WordTrace]
  refine ⟨23794171312297763354958415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126902246998921404559778213 23794171312297763354958415)
  ·
    refine ⟨35691256968446645032437623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23794171312297763354958415 35691256968446645032437623)
    ·
      refine ⟨53536885452669967548656435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35691256968446645032437623 53536885452669967548656435)
      ·
        refine ⟨80305328179004951322984653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53536885452669967548656435 80305328179004951322984653)
        ·
          refine ⟨30114498067126856746119245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80305328179004951322984653 30114498067126856746119245)
          ·
            refine ⟨11292936775172571279794717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30114498067126856746119245 11292936775172571279794717)
            ·
              refine ⟨4234851290689714229923019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11292936775172571279794717 4234851290689714229923019)
              ·
                refine ⟨6352276936034571344884529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234851290689714229923019 6352276936034571344884529)
                ·
                  refine ⟨4764207702025928508663397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352276936034571344884529 4764207702025928508663397)
                  ·
                    refine ⟨893288944129861595374387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764207702025928508663397 893288944129861595374387)
                    ·
                      rfl

theorem cell23_5219022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_5219022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219022 prefixEnd_5219022 := by exact prefixLift 5219022
  have htrace : WordTrace (prefixWord ++ tailWord_5219022) baseStart_5219022 baseEnd_5219022 := by
    simpa [prefixWord, tailWord_5219022, baseEnd_5219022] using wordTrace_append hprefix tailTrace_5219022
  have hstable : (prefixWord ++ tailWord_5219022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219022).length < 2 ^ (prefixWord ++ tailWord_5219022).sum := by decide
  have hdescent : baseEnd_5219022 < baseStart_5219022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219045 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_5219045 : Nat := 118140960795 + 5219045 * 2 ^ 59
def prefixEnd_5219045 : Nat := 4983230072969 + 3 ^ 40 * 5219045 * 2
def baseEnd_5219045 : Nat := 2679878642444638196135555

theorem tailTrace_5219045 : CollatzResearch.WordTrace tailWord_5219045 prefixEnd_5219045 2679878642444638196135555 := by
  unfold tailWord_5219045
  simp only [CollatzResearch.WordTrace]
  refine ⟨190354209377298781767754589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126902806251532521178503059 190354209377298781767754589)
  ·
    refine ⟨71382828516487043162907971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190354209377298781767754589 71382828516487043162907971)
    ·
      refine ⟨107074242774730564744361957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71382828516487043162907971 107074242774730564744361957)
      ·
        refine ⟨20076420520261980889567867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107074242774730564744361957 20076420520261980889567867)
        ·
          refine ⟨30114630780392971334351801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20076420520261980889567867 30114630780392971334351801)
          ·
            refine ⟨22585973085294728500763851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30114630780392971334351801 22585973085294728500763851)
            ·
              refine ⟨33878959627942092751145777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22585973085294728500763851 33878959627942092751145777)
              ·
                refine ⟨25409219720956569563359333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33878959627942092751145777 25409219720956569563359333)
                ·
                  refine ⟨4764228697679356793129875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25409219720956569563359333 4764228697679356793129875)
                  ·
                    refine ⟨7146343046519035189694813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764228697679356793129875 7146343046519035189694813)
                    ·
                      refine ⟨2679878642444638196135555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146343046519035189694813 2679878642444638196135555)
                      ·
                        rfl

theorem cell23_5219045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_5219045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219045 prefixEnd_5219045 := by exact prefixLift 5219045
  have htrace : WordTrace (prefixWord ++ tailWord_5219045) baseStart_5219045 baseEnd_5219045 := by
    simpa [prefixWord, tailWord_5219045, baseEnd_5219045] using wordTrace_append hprefix tailTrace_5219045
  have hstable : (prefixWord ++ tailWord_5219045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219045).length < 2 ^ (prefixWord ++ tailWord_5219045).sum := by decide
  have hdescent : baseEnd_5219045 < baseStart_5219045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219051 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4]
def baseStart_5219051 : Nat := 118140960795 + 5219051 * 2 ^ 59
def prefixEnd_5219051 : Nat := 4983230072969 + 3 ^ 40 * 5219051 * 2
def baseEnd_5219051 : Nat := 2679881723328565172660527

theorem tailTrace_5219051 : CollatzResearch.WordTrace tailWord_5219051 prefixEnd_5219051 2679881723328565172660527 := by
  unfold tailWord_5219051
  simp only [CollatzResearch.WordTrace]
  refine ⟨190354428215277044792473007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126902952143518029861648671 190354428215277044792473007)
  ·
    refine ⟨285531642322915567188709511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190354428215277044792473007 285531642322915567188709511)
    ·
      refine ⟨428297463484373350783064267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285531642322915567188709511 428297463484373350783064267)
      ·
        refine ⟨642446195226560026174596401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428297463484373350783064267 642446195226560026174596401)
        ·
          refine ⟨481834646419920019630947301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642446195226560026174596401 481834646419920019630947301)
          ·
            refine ⟨90343996203735003680802619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 481834646419920019630947301 90343996203735003680802619)
            ·
              refine ⟨135515994305602505521203929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90343996203735003680802619 135515994305602505521203929)
              ·
                refine ⟨101636995729201879140902947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135515994305602505521203929 101636995729201879140902947)
                ·
                  refine ⟨152455493593802818711354421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101636995729201879140902947 152455493593802818711354421)
                  ·
                    refine ⟨14292702524419014254189477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 152455493593802818711354421 14292702524419014254189477)
                    ·
                      refine ⟨2679881723328565172660527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14292702524419014254189477 2679881723328565172660527)
                      ·
                        rfl

theorem cell23_5219051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_5219051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219051 prefixEnd_5219051 := by exact prefixLift 5219051
  have htrace : WordTrace (prefixWord ++ tailWord_5219051) baseStart_5219051 baseEnd_5219051 := by
    simpa [prefixWord, tailWord_5219051, baseEnd_5219051] using wordTrace_append hprefix tailTrace_5219051
  have hstable : (prefixWord ++ tailWord_5219051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219051).length < 2 ^ (prefixWord ++ tailWord_5219051).sum := by decide
  have hdescent : baseEnd_5219051 < baseStart_5219051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219062 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_5219062 : Nat := 118140960795 + 5219062 * 2 ^ 59
def prefixEnd_5219062 : Nat := 4983230072969 + 3 ^ 40 * 5219062 * 2
def baseEnd_5219062 : Nat := 2679887371615764629622977

theorem tailTrace_5219062 : CollatzResearch.WordTrace tailWord_5219062 prefixEnd_5219062 2679887371615764629622977 := by
  unfold tailWord_5219062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11897176838639824604445215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126903219612158129114082293 11897176838639824604445215)
  ·
    refine ⟨17845765257959736906667823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11897176838639824604445215 17845765257959736906667823)
    ·
      refine ⟨26768647886939605360001735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17845765257959736906667823 26768647886939605360001735)
      ·
        refine ⟨40152971830409408040002603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26768647886939605360001735 40152971830409408040002603)
        ·
          refine ⟨60229457745614112060003905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40152971830409408040002603 60229457745614112060003905)
          ·
            refine ⟨45172093309210584045002929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60229457745614112060003905 45172093309210584045002929)
            ·
              refine ⟨33879069981907938033752197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45172093309210584045002929 33879069981907938033752197)
              ·
                refine ⟨6352325621607738381328537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33879069981907938033752197 6352325621607738381328537)
                ·
                  refine ⟨4764244216205803785996403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352325621607738381328537 4764244216205803785996403)
                  ·
                    refine ⟨7146366324308705678994605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764244216205803785996403 7146366324308705678994605)
                    ·
                      refine ⟨2679887371615764629622977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146366324308705678994605 2679887371615764629622977)
                      ·
                        rfl

theorem cell23_5219062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_5219062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219062 prefixEnd_5219062 := by exact prefixLift 5219062
  have htrace : WordTrace (prefixWord ++ tailWord_5219062) baseStart_5219062 baseEnd_5219062 := by
    simpa [prefixWord, tailWord_5219062, baseEnd_5219062] using wordTrace_append hprefix tailTrace_5219062
  have hstable : (prefixWord ++ tailWord_5219062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219062).length < 2 ^ (prefixWord ++ tailWord_5219062).sum := by decide
  have hdescent : baseEnd_5219062 < baseStart_5219062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219071 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_5219071 : Nat := 118140960795 + 5219071 * 2 ^ 59
def prefixEnd_5219071 : Nat := 4983230072969 + 3 ^ 40 * 5219071 * 2
def baseEnd_5219071 : Nat := 2679891992941655094410435

theorem tailTrace_5219071 : CollatzResearch.WordTrace tailWord_5219071 prefixEnd_5219071 2679891992941655094410435 := by
  unfold tailWord_5219071
  simp only [CollatzResearch.WordTrace]
  refine ⟨190355157675204588208201067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126903438450136392138800711 190355157675204588208201067)
  ·
    refine ⟨285532736512806882312301601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190355157675204588208201067 285532736512806882312301601)
    ·
      refine ⟨214149552384605161734226201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285532736512806882312301601 214149552384605161734226201)
      ·
        refine ⟨160612164288453871300669651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214149552384605161734226201 160612164288453871300669651)
        ·
          refine ⟨240918246432680806951004477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160612164288453871300669651 240918246432680806951004477)
          ·
            refine ⟨90344342412255302606626679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240918246432680806951004477 90344342412255302606626679)
            ·
              refine ⟨135516513618382953909940019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90344342412255302606626679 135516513618382953909940019)
              ·
                refine ⟨203274770427574430864910029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135516513618382953909940019 203274770427574430864910029)
                ·
                  refine ⟨76228038910340411574341261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203274770427574430864910029 76228038910340411574341261)
                  ·
                    refine ⟨28585514591377654340377973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76228038910340411574341261 28585514591377654340377973)
                    ·
                      refine ⟨2679891992941655094410435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28585514591377654340377973 2679891992941655094410435)
                      ·
                        rfl

theorem cell23_5219071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_5219071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219071 prefixEnd_5219071 := by exact prefixLift 5219071
  have htrace : WordTrace (prefixWord ++ tailWord_5219071) baseStart_5219071 baseEnd_5219071 := by
    simpa [prefixWord, tailWord_5219071, baseEnd_5219071] using wordTrace_append hprefix tailTrace_5219071
  have hstable : (prefixWord ++ tailWord_5219071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219071).length < 2 ^ (prefixWord ++ tailWord_5219071).sum := by decide
  have hdescent : baseEnd_5219071 < baseStart_5219071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219079 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5219079 : Nat := 118140960795 + 5219079 * 2 ^ 59
def prefixEnd_5219079 : Nat := 4983230072969 + 3 ^ 40 * 5219079 * 2
def baseEnd_5219079 : Nat := 2679896100786891063110399

theorem tailTrace_5219079 : CollatzResearch.WordTrace tailWord_5219079 prefixEnd_5219079 2679896100786891063110399 := by
  unfold tailWord_5219079
  simp only [CollatzResearch.WordTrace]
  refine ⟨190355449459175605574492291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126903632972783737049661527 190355449459175605574492291)
  ·
    refine ⟨285533174188763408361738437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190355449459175605574492291 285533174188763408361738437)
    ·
      refine ⟨53537470160393139067825957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285533174188763408361738437 53537470160393139067825957)
      ·
        refine ⟨10038275655073713575217367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53537470160393139067825957 10038275655073713575217367)
        ·
          refine ⟨15057413482610570362826051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10038275655073713575217367 15057413482610570362826051)
          ·
            refine ⟨22586120223915855544239077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15057413482610570362826051 22586120223915855544239077)
            ·
              refine ⟨4234897541984222914544827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22586120223915855544239077 4234897541984222914544827)
              ·
                refine ⟨6352346312976334371817241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234897541984222914544827 6352346312976334371817241)
                ·
                  refine ⟨4764259734732250778862931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352346312976334371817241 4764259734732250778862931)
                  ·
                    refine ⟨7146389602098376168294397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764259734732250778862931 7146389602098376168294397)
                    ·
                      refine ⟨2679896100786891063110399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146389602098376168294397 2679896100786891063110399)
                      ·
                        rfl

theorem cell23_5219079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5219079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219079 prefixEnd_5219079 := by exact prefixLift 5219079
  have htrace : WordTrace (prefixWord ++ tailWord_5219079) baseStart_5219079 baseEnd_5219079 := by
    simpa [prefixWord, tailWord_5219079, baseEnd_5219079] using wordTrace_append hprefix tailTrace_5219079
  have hstable : (prefixWord ++ tailWord_5219079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219079).length < 2 ^ (prefixWord ++ tailWord_5219079).sum := by decide
  have hdescent : baseEnd_5219079 < baseStart_5219079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219091 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 9]
def baseStart_5219091 : Nat := 118140960795 + 5219091 * 2 ^ 59
def prefixEnd_5219091 : Nat := 4983230072969 + 3 ^ 40 * 5219091 * 2
def baseEnd_5219091 : Nat := 297766918061638335128927

theorem tailTrace_5219091 : CollatzResearch.WordTrace tailWord_5219091 prefixEnd_5219091 297766918061638335128927 := by
  unfold tailWord_5219091
  simp only [CollatzResearch.WordTrace]
  refine ⟨190355887135132131623929127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126903924756754754415952751 190355887135132131623929127)
  ·
    refine ⟨285533830702698197435893691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190355887135132131623929127 285533830702698197435893691)
    ·
      refine ⟨428300746054047296153840537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285533830702698197435893691 428300746054047296153840537)
      ·
        refine ⟨321225559540535472115380403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428300746054047296153840537 321225559540535472115380403)
        ·
          refine ⟨481838339310803208173070605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321225559540535472115380403 481838339310803208173070605)
          ·
            refine ⟨180689377241551203064901477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 481838339310803208173070605 180689377241551203064901477)
            ·
              refine ⟨33879258232790850574669027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180689377241551203064901477 33879258232790850574669027)
              ·
                refine ⟨50818887349186275862003541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33879258232790850574669027 50818887349186275862003541)
                ·
                  refine ⟨297766918061638335128927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50818887349186275862003541 297766918061638335128927)
                  ·
                    rfl

theorem cell23_5219091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 9].length) (baseStart_5219091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219091 prefixEnd_5219091 := by exact prefixLift 5219091
  have htrace : WordTrace (prefixWord ++ tailWord_5219091) baseStart_5219091 baseEnd_5219091 := by
    simpa [prefixWord, tailWord_5219091, baseEnd_5219091] using wordTrace_append hprefix tailTrace_5219091
  have hstable : (prefixWord ++ tailWord_5219091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219091).length < 2 ^ (prefixWord ++ tailWord_5219091).sum := by decide
  have hdescent : baseEnd_5219091 < baseStart_5219091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219135 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 3]
def baseStart_5219135 : Nat := 118140960795 + 5219135 * 2 ^ 59
def prefixEnd_5219135 : Nat := 4983230072969 + 3 ^ 40 * 5219135 * 2
def baseEnd_5219135 : Nat := 2679924855703542844010141

theorem tailTrace_5219135 : CollatzResearch.WordTrace tailWord_5219135 prefixEnd_5219135 2679924855703542844010141 := by
  unfold tailWord_5219135
  simp only [CollatzResearch.WordTrace]
  refine ⟨190357491946972727138530859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126904994631315151425687239 190357491946972727138530859)
  ·
    refine ⟨285536237920459090707796289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190357491946972727138530859 285536237920459090707796289)
    ·
      refine ⟨214152178440344318030847217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285536237920459090707796289 214152178440344318030847217)
      ·
        refine ⟨160614133830258238523135413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214152178440344318030847217 160614133830258238523135413)
        ·
          refine ⟨15057575046586709861543945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160614133830258238523135413 15057575046586709861543945)
          ·
            refine ⟨11293181284940032396157959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15057575046586709861543945 11293181284940032396157959)
            ·
              refine ⟨16939771927410048594236939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11293181284940032396157959 16939771927410048594236939)
              ·
                refine ⟨25409657891115072891355409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16939771927410048594236939 25409657891115072891355409)
                ·
                  refine ⟨19057243418336304668516557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25409657891115072891355409 19057243418336304668516557)
                  ·
                    refine ⟨7146466281876114250693709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19057243418336304668516557 7146466281876114250693709)
                    ·
                      refine ⟨2679924855703542844010141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146466281876114250693709 2679924855703542844010141)
                      ·
                        rfl

theorem cell23_5219135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_5219135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219135 prefixEnd_5219135 := by exact prefixLift 5219135
  have htrace : WordTrace (prefixWord ++ tailWord_5219135) baseStart_5219135 baseEnd_5219135 := by
    simpa [prefixWord, tailWord_5219135, baseEnd_5219135] using wordTrace_append hprefix tailTrace_5219135
  have hstable : (prefixWord ++ tailWord_5219135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219135).length < 2 ^ (prefixWord ++ tailWord_5219135).sum := by decide
  have hdescent : baseEnd_5219135 < baseStart_5219135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219185 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 3, 4]
def baseStart_5219185 : Nat := 118140960795 + 5219185 * 2 ^ 59
def prefixEnd_5219185 : Nat := 4983230072969 + 3 ^ 40 * 5219185 * 2
def baseEnd_5219185 : Nat := 893316843245422549461637

theorem tailTrace_5219185 : CollatzResearch.WordTrace tailWord_5219185 prefixEnd_5219185 893316843245422549461637 := by
  unfold tailWord_5219185
  simp only [CollatzResearch.WordTrace]
  refine ⟨190359315596791585677851009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126906210397861057118567339 190359315596791585677851009)
  ·
    refine ⟨142769486697593689258388257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190359315596791585677851009 142769486697593689258388257)
    ·
      refine ⟨107077115023195266943791193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142769486697593689258388257 107077115023195266943791193)
      ·
        refine ⟨80307836267396450207843395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107077115023195266943791193 80307836267396450207843395)
        ·
          refine ⟨120461754401094675311765093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80307836267396450207843395 120461754401094675311765093)
          ·
            refine ⟨22586578950205251620955955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120461754401094675311765093 22586578950205251620955955)
            ·
              refine ⟨33879868425307877431433933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22586578950205251620955955 33879868425307877431433933)
              ·
                refine ⟨12704950659490454036787725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33879868425307877431433933 12704950659490454036787725)
                ·
                  refine ⟨4764356497308920263795397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12704950659490454036787725 4764356497308920263795397)
                  ·
                    refine ⟨893316843245422549461637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764356497308920263795397 893316843245422549461637)
                    ·
                      rfl

theorem cell23_5219185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_5219185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219185 prefixEnd_5219185 := by exact prefixLift 5219185
  have htrace : WordTrace (prefixWord ++ tailWord_5219185) baseStart_5219185 baseEnd_5219185 := by
    simpa [prefixWord, tailWord_5219185, baseEnd_5219185] using wordTrace_append hprefix tailTrace_5219185
  have hstable : (prefixWord ++ tailWord_5219185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219185).length < 2 ^ (prefixWord ++ tailWord_5219185).sum := by decide
  have hdescent : baseEnd_5219185 < baseStart_5219185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219249 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 6]
def baseStart_5219249 : Nat := 118140960795 + 5219249 * 2 ^ 59
def prefixEnd_5219249 : Nat := 4983230072969 + 3 ^ 40 * 5219249 * 2
def baseEnd_5219249 : Nat := 297775932499795044220513

theorem tailTrace_5219249 : CollatzResearch.WordTrace tailWord_5219249 prefixEnd_5219249 297775932499795044220513 := by
  unfold tailWord_5219249
  simp only [CollatzResearch.WordTrace]
  refine ⟨190361649868559724608180801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126907766579039816405453867 190361649868559724608180801)
  ·
    refine ⟨142771237401419793456135601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190361649868559724608180801 142771237401419793456135601)
    ·
      refine ⟨107078428051064845092101701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142771237401419793456135601 107078428051064845092101701)
      ·
        refine ⟨20077205259574658454769069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107078428051064845092101701 20077205259574658454769069)
        ·
          refine ⟨7528951972340496920538401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20077205259574658454769069 7528951972340496920538401)
          ·
            refine ⟨5646713979255372690403801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7528951972340496920538401 5646713979255372690403801)
            ·
              refine ⟨4235035484441529517802851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5646713979255372690403801 4235035484441529517802851)
              ·
                refine ⟨6352553226662294276704277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235035484441529517802851 6352553226662294276704277)
                ·
                  refine ⟨297775932499795044220513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6352553226662294276704277 297775932499795044220513)
                  ·
                    rfl

theorem cell23_5219249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 6].length) (baseStart_5219249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219249 prefixEnd_5219249 := by exact prefixLift 5219249
  have htrace : WordTrace (prefixWord ++ tailWord_5219249) baseStart_5219249 baseEnd_5219249 := by
    simpa [prefixWord, tailWord_5219249, baseEnd_5219249] using wordTrace_append hprefix tailTrace_5219249
  have hstable : (prefixWord ++ tailWord_5219249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219249).length < 2 ^ (prefixWord ++ tailWord_5219249).sum := by decide
  have hdescent : baseEnd_5219249 < baseStart_5219249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219275 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 1, 6]
def baseStart_5219275 : Nat := 118140960795 + 5219275 * 2 ^ 59
def prefixEnd_5219275 : Nat := 4983230072969 + 3 ^ 40 * 5219275 * 2
def baseEnd_5219275 : Nat := 893332247665057432086499

theorem tailTrace_5219275 : CollatzResearch.WordTrace tailWord_5219275 prefixEnd_5219275 893332247665057432086499 := by
  unfold tailWord_5219275
  simp only [CollatzResearch.WordTrace]
  refine ⟨190362598166465531048627279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126908398777643687365751519 190362598166465531048627279)
  ·
    refine ⟨285543897249698296572940919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190362598166465531048627279 285543897249698296572940919)
    ·
      refine ⟨428315845874547444859411379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285543897249698296572940919 428315845874547444859411379)
      ·
        refine ⟨642473768811821167289117069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428315845874547444859411379 642473768811821167289117069)
        ·
          refine ⟨240927663304432937733418901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642473768811821167289117069 240927663304432937733418901)
          ·
            refine ⟨11293484217395293956254011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 240927663304432937733418901 11293484217395293956254011)
            ·
              refine ⟨16940226326092940934381017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11293484217395293956254011 16940226326092940934381017)
              ·
                refine ⟨12705169744569705700785763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16940226326092940934381017 12705169744569705700785763)
                ·
                  refine ⟨19057754616854558551178645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12705169744569705700785763 19057754616854558551178645)
                  ·
                    refine ⟨893332247665057432086499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19057754616854558551178645 893332247665057432086499)
                    ·
                      rfl

theorem cell23_5219275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 6].length) (baseStart_5219275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219275 prefixEnd_5219275 := by exact prefixLift 5219275
  have htrace : WordTrace (prefixWord ++ tailWord_5219275) baseStart_5219275 baseEnd_5219275 := by
    simpa [prefixWord, tailWord_5219275, baseEnd_5219275] using wordTrace_append hprefix tailTrace_5219275
  have hstable : (prefixWord ++ tailWord_5219275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219275).length < 2 ^ (prefixWord ++ tailWord_5219275).sum := by decide
  have hdescent : baseEnd_5219275 < baseStart_5219275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219286 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_5219286 : Nat := 118140960795 + 5219286 * 2 ^ 59
def prefixEnd_5219286 : Nat := 4983230072969 + 3 ^ 40 * 5219286 * 2
def baseEnd_5219286 : Nat := 2680002391282371753221947

theorem tailTrace_5219286 : CollatzResearch.WordTrace tailWord_5219286 prefixEnd_5219286 2680002391282371753221947 := by
  unfold tailWord_5219286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11897687460589104995454857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126908666246283786618185141 11897687460589104995454857)
  ·
    refine ⟨8923265595441828746591143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11897687460589104995454857 8923265595441828746591143)
    ·
      refine ⟨13384898393162743119886715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8923265595441828746591143 13384898393162743119886715)
      ·
        refine ⟨20077347589744114679830073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13384898393162743119886715 20077347589744114679830073)
        ·
          refine ⟨15058010692308086009872555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20077347589744114679830073 15058010692308086009872555)
          ·
            refine ⟨22587016038462129014808833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15058010692308086009872555 22587016038462129014808833)
            ·
              refine ⟨16940262028846596761106625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22587016038462129014808833 16940262028846596761106625)
              ·
                refine ⟨12705196521634947570829969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16940262028846596761106625 12705196521634947570829969)
                ·
                  refine ⟨9528897391226210678122477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12705196521634947570829969 9528897391226210678122477)
                  ·
                    refine ⟨3573336521709829004295929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9528897391226210678122477 3573336521709829004295929)
                    ·
                      refine ⟨2680002391282371753221947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573336521709829004295929 2680002391282371753221947)
                      ·
                        rfl

theorem cell23_5219286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_5219286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219286 prefixEnd_5219286 := by exact prefixLift 5219286
  have htrace : WordTrace (prefixWord ++ tailWord_5219286) baseStart_5219286 baseEnd_5219286 := by
    simpa [prefixWord, tailWord_5219286, baseEnd_5219286] using wordTrace_append hprefix tailTrace_5219286
  have hstable : (prefixWord ++ tailWord_5219286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219286).length < 2 ^ (prefixWord ++ tailWord_5219286).sum := by decide
  have hdescent : baseEnd_5219286 < baseStart_5219286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219288 : List Nat := [2, 1, 2, 2, 2, 14]
def baseStart_5219288 : Nat := 118140960795 + 5219288 * 2 ^ 59
def prefixEnd_5219288 : Nat := 4983230072969 + 3 ^ 40 * 5219288 * 2
def baseEnd_5219288 : Nat := 11028820651208562738259

theorem tailTrace_5219288 : CollatzResearch.WordTrace tailWord_5219288 prefixEnd_5219288 11028820651208562738259 := by
  unfold tailWord_5219288
  simp only [CollatzResearch.WordTrace]
  refine ⟨95181536157709217134425259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126908714876945622845900345 95181536157709217134425259)
  ·
    refine ⟨142772304236563825701637889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95181536157709217134425259 142772304236563825701637889)
    ·
      refine ⟨107079228177422869276228417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142772304236563825701637889 107079228177422869276228417)
      ·
        refine ⟨80309421133067151957171313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107079228177422869276228417 80309421133067151957171313)
        ·
          refine ⟨60232065849800363967878485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80309421133067151957171313 60232065849800363967878485)
          ·
            refine ⟨11028820651208562738259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 60232065849800363967878485 11028820651208562738259)
            ·
              rfl

theorem cell23_5219288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 14].length) (baseStart_5219288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219288 prefixEnd_5219288 := by exact prefixLift 5219288
  have htrace : WordTrace (prefixWord ++ tailWord_5219288) baseStart_5219288 baseEnd_5219288 := by
    simpa [prefixWord, tailWord_5219288, baseEnd_5219288] using wordTrace_append hprefix tailTrace_5219288
  have hstable : (prefixWord ++ tailWord_5219288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219288).length < 2 ^ (prefixWord ++ tailWord_5219288).sum := by decide
  have hdescent : baseEnd_5219288 < baseStart_5219288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219293 : List Nat := [1, 4, 3, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_5219293 : Nat := 118140960795 + 5219293 * 2 ^ 59
def prefixEnd_5219293 : Nat := 4983230072969 + 3 ^ 40 * 5219293 * 2
def baseEnd_5219293 : Nat := 2680005985646953225834415

theorem tailTrace_5219293 : CollatzResearch.WordTrace tailWord_5219293 prefixEnd_5219293 2680005985646953225834415 := by
  unfold tailWord_5219293
  simp only [CollatzResearch.WordTrace]
  refine ⟨190363254680400320122782533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126908836453600213415188355 190363254680400320122782533)
  ·
    refine ⟨35693110252575060023021725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190363254680400320122782533 35693110252575060023021725)
    ·
      refine ⟨13384916344715647508633147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35693110252575060023021725 13384916344715647508633147)
      ·
        refine ⟨20077374517073471262949721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13384916344715647508633147 20077374517073471262949721)
        ·
          refine ⟨15058030887805103447212291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20077374517073471262949721 15058030887805103447212291)
          ·
            refine ⟨22587046331707655170818437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15058030887805103447212291 22587046331707655170818437)
            ·
              refine ⟨4235071187195185344528457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22587046331707655170818437 4235071187195185344528457)
              ·
                refine ⟨3176303390396389008396343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4235071187195185344528457 3176303390396389008396343)
                ·
                  refine ⟨4764455085594583512594515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176303390396389008396343 4764455085594583512594515)
                  ·
                    refine ⟨7146682628391875268891773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764455085594583512594515 7146682628391875268891773)
                    ·
                      refine ⟨2680005985646953225834415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146682628391875268891773 2680005985646953225834415)
                      ·
                        rfl

theorem cell23_5219293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_5219293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219293 prefixEnd_5219293 := by exact prefixLift 5219293
  have htrace : WordTrace (prefixWord ++ tailWord_5219293) baseStart_5219293 baseEnd_5219293 := by
    simpa [prefixWord, tailWord_5219293, baseEnd_5219293] using wordTrace_append hprefix tailTrace_5219293
  have hstable : (prefixWord ++ tailWord_5219293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219293).length < 2 ^ (prefixWord ++ tailWord_5219293).sum := by decide
  have hdescent : baseEnd_5219293 < baseStart_5219293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219299 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 3, 2, 2]
def baseStart_5219299 : Nat := 118140960795 + 5219299 * 2 ^ 59
def prefixEnd_5219299 : Nat := 4983230072969 + 3 ^ 40 * 5219299 * 2
def baseEnd_5219299 : Nat := 2680009066530880202359387

theorem tailTrace_5219299 : CollatzResearch.WordTrace tailWord_5219299 prefixEnd_5219299 2680009066530880202359387 := by
  unfold tailWord_5219299
  simp only [CollatzResearch.WordTrace]
  refine ⟨190363473518378583147500951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126908982345585722098333967 190363473518378583147500951)
  ·
    refine ⟨285545210277567874721251427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190363473518378583147500951 285545210277567874721251427)
    ·
      refine ⟨428317815416351812081877141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285545210277567874721251427 428317815416351812081877141)
      ·
        refine ⟨20077397597641491191337991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 428317815416351812081877141 20077397597641491191337991)
        ·
          refine ⟨30116096396462236787006987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20077397597641491191337991 30116096396462236787006987)
          ·
            refine ⟨45174144594693355180510481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30116096396462236787006987 45174144594693355180510481)
            ·
              refine ⟨33880608446020016385382861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45174144594693355180510481 33880608446020016385382861)
              ·
                refine ⟨12705228167257506144518573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33880608446020016385382861 12705228167257506144518573)
                ·
                  refine ⟨4764460562721564804194465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12705228167257506144518573 4764460562721564804194465)
                  ·
                    refine ⟨3573345422041173603145849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4764460562721564804194465 3573345422041173603145849)
                    ·
                      refine ⟨2680009066530880202359387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573345422041173603145849 2680009066530880202359387)
                      ·
                        rfl

theorem cell23_5219299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_5219299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219299 prefixEnd_5219299 := by exact prefixLift 5219299
  have htrace : WordTrace (prefixWord ++ tailWord_5219299) baseStart_5219299 baseEnd_5219299 := by
    simpa [prefixWord, tailWord_5219299, baseEnd_5219299] using wordTrace_append hprefix tailTrace_5219299
  have hstable : (prefixWord ++ tailWord_5219299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219299).length < 2 ^ (prefixWord ++ tailWord_5219299).sum := by decide
  have hdescent : baseEnd_5219299 < baseStart_5219299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219330 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_5219330 : Nat := 118140960795 + 5219330 * 2 ^ 59
def prefixEnd_5219330 : Nat := 4983230072969 + 3 ^ 40 * 5219330 * 2
def baseEnd_5219330 : Nat := 893341661477056527023915

theorem tailTrace_5219330 : CollatzResearch.WordTrace tailWord_5219330 prefixEnd_5219330 893341661477056527023915 := by
  unfold tailWord_5219330
  simp only [CollatzResearch.WordTrace]
  refine ⟨47591151045316568860469861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126909736120844183627919629 47591151045316568860469861)
  ·
    refine ⟨8923340820996856661338099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47591151045316568860469861 8923340820996856661338099)
    ·
      refine ⟨13385011231495284992007149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8923340820996856661338099 13385011231495284992007149)
      ·
        refine ⟨5019379211810731872002681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13385011231495284992007149 5019379211810731872002681)
        ·
          refine ⟨3764534408858048904002011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5019379211810731872002681 3764534408858048904002011)
          ·
            refine ⟨5646801613287073356003017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764534408858048904002011 5646801613287073356003017)
            ·
              refine ⟨4235101209965305017002263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5646801613287073356003017 4235101209965305017002263)
              ·
                refine ⟨6352651814947957525503395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235101209965305017002263 6352651814947957525503395)
                ·
                  refine ⟨9528977722421936288255093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6352651814947957525503395 9528977722421936288255093)
                  ·
                    refine ⟨893341661477056527023915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9528977722421936288255093 893341661477056527023915)
                    ·
                      rfl

theorem cell23_5219330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_5219330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219330 prefixEnd_5219330 := by exact prefixLift 5219330
  have htrace : WordTrace (prefixWord ++ tailWord_5219330) baseStart_5219330 baseEnd_5219330 := by
    simpa [prefixWord, tailWord_5219330, baseEnd_5219330] using wordTrace_append hprefix tailTrace_5219330
  have hstable : (prefixWord ++ tailWord_5219330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219330).length < 2 ^ (prefixWord ++ tailWord_5219330).sum := by decide
  have hdescent : baseEnd_5219330 < baseStart_5219330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219336 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_5219336 : Nat := 118140960795 + 5219336 * 2 ^ 59
def prefixEnd_5219336 : Nat := 4983230072969 + 3 ^ 40 * 5219336 * 2
def baseEnd_5219336 : Nat := 2680028065315096557596717

theorem tailTrace_5219336 : CollatzResearch.WordTrace tailWord_5219336 prefixEnd_5219336 2680028065315096557596717 := by
  unfold tailWord_5219336
  simp only [CollatzResearch.WordTrace]
  refine ⟨95182411509622269233298931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126909882012829692311065241 95182411509622269233298931)
  ·
    refine ⟨142773617264433403849948397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95182411509622269233298931 142773617264433403849948397)
    ·
      refine ⟨53540106474162526443730649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142773617264433403849948397 53540106474162526443730649)
      ·
        refine ⟨40155079855621894832797987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53540106474162526443730649 40155079855621894832797987)
        ·
          refine ⟨60232619783432842249196981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40155079855621894832797987 60232619783432842249196981)
          ·
            refine ⟨5646808104696828960862217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60232619783432842249196981 5646808104696828960862217)
            ·
              refine ⟨4235106078522621720646663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5646808104696828960862217 4235106078522621720646663)
              ·
                refine ⟨6352659117783932580969995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235106078522621720646663 6352659117783932580969995)
                ·
                  refine ⟨9528988676675898871454993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6352659117783932580969995 9528988676675898871454993)
                  ·
                    refine ⟨7146741507506924153591245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9528988676675898871454993 7146741507506924153591245)
                    ·
                      refine ⟨2680028065315096557596717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146741507506924153591245 2680028065315096557596717)
                      ·
                        rfl

theorem cell23_5219336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_5219336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219336 prefixEnd_5219336 := by exact prefixLift 5219336
  have htrace : WordTrace (prefixWord ++ tailWord_5219336) baseStart_5219336 baseEnd_5219336 := by
    simpa [prefixWord, tailWord_5219336, baseEnd_5219336] using wordTrace_append hprefix tailTrace_5219336
  have hstable : (prefixWord ++ tailWord_5219336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219336).length < 2 ^ (prefixWord ++ tailWord_5219336).sum := by decide
  have hdescent : baseEnd_5219336 < baseStart_5219336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219349 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_5219349 : Nat := 118140960795 + 5219349 * 2 ^ 59
def prefixEnd_5219349 : Nat := 4983230072969 + 3 ^ 40 * 5219349 * 2
def baseEnd_5219349 : Nat := 2680034740563605006734157

theorem tailTrace_5219349 : CollatzResearch.WordTrace tailWord_5219349 prefixEnd_5219349 2680034740563605006734157 := by
  unfold tailWord_5219349
  simp only [CollatzResearch.WordTrace]
  refine ⟨190365297168197441686821101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126910198112131627791214067 190365297168197441686821101)
  ·
    refine ⟨71386986438074040632557913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190365297168197441686821101 71386986438074040632557913)
    ·
      refine ⟨53540239828555530474418435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71386986438074040632557913 53540239828555530474418435)
      ·
        refine ⟨80310359742833295711627653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53540239828555530474418435 80310359742833295711627653)
        ·
          refine ⟨15058192451781242945930185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80310359742833295711627653 15058192451781242945930185)
          ·
            refine ⟨11293644338835932209447639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15058192451781242945930185 11293644338835932209447639)
            ·
              refine ⟨16940466508253898314171459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11293644338835932209447639 16940466508253898314171459)
              ·
                refine ⟨25410699762380847471257189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16940466508253898314171459 25410699762380847471257189)
                ·
                  refine ⟨4764506205446408900860723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25410699762380847471257189 4764506205446408900860723)
                  ·
                    refine ⟨7146759308169613351291085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764506205446408900860723 7146759308169613351291085)
                    ·
                      refine ⟨2680034740563605006734157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146759308169613351291085 2680034740563605006734157)
                      ·
                        rfl

theorem cell23_5219349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_5219349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219349 prefixEnd_5219349 := by exact prefixLift 5219349
  have htrace : WordTrace (prefixWord ++ tailWord_5219349) baseStart_5219349 baseEnd_5219349 := by
    simpa [prefixWord, tailWord_5219349, baseEnd_5219349] using wordTrace_append hprefix tailTrace_5219349
  have hstable : (prefixWord ++ tailWord_5219349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219349).length < 2 ^ (prefixWord ++ tailWord_5219349).sum := by decide
  have hdescent : baseEnd_5219349 < baseStart_5219349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219365 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_5219365 : Nat := 118140960795 + 5219365 * 2 ^ 59
def prefixEnd_5219365 : Nat := 4983230072969 + 3 ^ 40 * 5219365 * 2
def baseEnd_5219365 : Nat := 893347652084692314711361

theorem tailTrace_5219365 : CollatzResearch.WordTrace tailWord_5219365 prefixEnd_5219365 893347652084692314711361 := by
  unfold tailWord_5219365
  simp only [CollatzResearch.WordTrace]
  refine ⟨190365880736139476419403549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126910587157426317612935699 190365880736139476419403549)
  ·
    refine ⟨71387205276052303657276331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190365880736139476419403549 71387205276052303657276331)
    ·
      refine ⟨107080807914078455485914497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71387205276052303657276331 107080807914078455485914497)
      ·
        refine ⟨80310605935558841614435873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107080807914078455485914497 80310605935558841614435873)
        ·
          refine ⟨60232954451669131210826905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80310605935558841614435873 60232954451669131210826905)
          ·
            refine ⟨45174715838751848408120179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60232954451669131210826905 45174715838751848408120179)
            ·
              refine ⟨67762073758127772612180269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45174715838751848408120179 67762073758127772612180269)
              ·
                refine ⟨25410777659297914729567601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67762073758127772612180269 25410777659297914729567601)
                ·
                  refine ⟨19058083244473436047175701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25410777659297914729567601 19058083244473436047175701)
                  ·
                    refine ⟨893347652084692314711361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19058083244473436047175701 893347652084692314711361)
                    ·
                      rfl

theorem cell23_5219365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_5219365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219365 prefixEnd_5219365 := by exact prefixLift 5219365
  have htrace : WordTrace (prefixWord ++ tailWord_5219365) baseStart_5219365 baseEnd_5219365 := by
    simpa [prefixWord, tailWord_5219365, baseEnd_5219365] using wordTrace_append hprefix tailTrace_5219365
  have hstable : (prefixWord ++ tailWord_5219365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219365).length < 2 ^ (prefixWord ++ tailWord_5219365).sum := by decide
  have hdescent : baseEnd_5219365 < baseStart_5219365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219375 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 3]
def baseStart_5219375 : Nat := 118140960795 + 5219375 * 2 ^ 59
def prefixEnd_5219375 : Nat := 4983230072969 + 3 ^ 40 * 5219375 * 2
def baseEnd_5219375 : Nat := 2680048091060621905009037

theorem tailTrace_5219375 : CollatzResearch.WordTrace tailWord_5219375 prefixEnd_5219375 2680048091060621905009037 := by
  unfold tailWord_5219375
  simp only [CollatzResearch.WordTrace]
  refine ⟨190366245466103248127267579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126910830310735498751511719 190366245466103248127267579)
  ·
    refine ⟨285549368199154872190901369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190366245466103248127267579 285549368199154872190901369)
    ·
      refine ⟨214162026149366154143176027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285549368199154872190901369 214162026149366154143176027)
      ·
        refine ⟨321243039224049231214764041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214162026149366154143176027 321243039224049231214764041)
        ·
          refine ⟨240932279418036923411073031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321243039224049231214764041 240932279418036923411073031)
          ·
            refine ⟨361398419127055385116609547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240932279418036923411073031 361398419127055385116609547)
            ·
              refine ⟨542097628690583077674914321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361398419127055385116609547 542097628690583077674914321)
              ·
                refine ⟨406573221517937308256185741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542097628690583077674914321 406573221517937308256185741)
                ·
                  refine ⟨152464958069226490596069653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406573221517937308256185741 152464958069226490596069653)
                  ·
                    refine ⟨7146794909494991746690765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 152464958069226490596069653 7146794909494991746690765)
                    ·
                      refine ⟨2680048091060621905009037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7146794909494991746690765 2680048091060621905009037)
                      ·
                        rfl

theorem cell23_5219375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_5219375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219375 prefixEnd_5219375 := by exact prefixLift 5219375
  have htrace : WordTrace (prefixWord ++ tailWord_5219375) baseStart_5219375 baseEnd_5219375 := by
    simpa [prefixWord, tailWord_5219375, baseEnd_5219375] using wordTrace_append hprefix tailTrace_5219375
  have hstable : (prefixWord ++ tailWord_5219375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219375).length < 2 ^ (prefixWord ++ tailWord_5219375).sum := by decide
  have hdescent : baseEnd_5219375 < baseStart_5219375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219406 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_5219406 : Nat := 118140960795 + 5219406 * 2 ^ 59
def prefixEnd_5219406 : Nat := 4983230072969 + 3 ^ 40 * 5219406 * 2
def baseEnd_5219406 : Nat := 2680064008960911283721395

theorem tailTrace_5219406 : CollatzResearch.WordTrace tailWord_5219406 prefixEnd_5219406 2680064008960911283721395 := by
  unfold tailWord_5219406
  simp only [CollatzResearch.WordTrace]
  refine ⟨23795922016123867552705759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126911584085993960281097381 23795922016123867552705759)
  ·
    refine ⟨35693883024185801329058639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23795922016123867552705759 35693883024185801329058639)
    ·
      refine ⟨53540824536278701993587959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35693883024185801329058639 53540824536278701993587959)
      ·
        refine ⟨80311236804418052990381939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53540824536278701993587959 80311236804418052990381939)
        ·
          refine ⟨120466855206627079485572909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80311236804418052990381939 120466855206627079485572909)
          ·
            refine ⟨45175070702485154807089841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120466855206627079485572909 45175070702485154807089841)
            ·
              refine ⟨33881303026863866105317381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45175070702485154807089841 33881303026863866105317381)
              ·
                refine ⟨6352744317536974894747009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33881303026863866105317381 6352744317536974894747009)
                ·
                  refine ⟨4764558238152731171060257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352744317536974894747009 4764558238152731171060257)
                  ·
                    refine ⟨3573418678614548378295193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4764558238152731171060257 3573418678614548378295193)
                    ·
                      refine ⟨2680064008960911283721395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573418678614548378295193 2680064008960911283721395)
                      ·
                        rfl

theorem cell23_5219406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_5219406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219406 prefixEnd_5219406 := by exact prefixLift 5219406
  have htrace : WordTrace (prefixWord ++ tailWord_5219406) baseStart_5219406 baseEnd_5219406 := by
    simpa [prefixWord, tailWord_5219406, baseEnd_5219406] using wordTrace_append hprefix tailTrace_5219406
  have hstable : (prefixWord ++ tailWord_5219406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219406).length < 2 ^ (prefixWord ++ tailWord_5219406).sum := by decide
  have hdescent : baseEnd_5219406 < baseStart_5219406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219412 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 7]
def baseStart_5219412 : Nat := 118140960795 + 5219412 * 2 ^ 59
def prefixEnd_5219412 : Nat := 4983230072969 + 3 ^ 40 * 5219412 * 2
def baseEnd_5219412 : Nat := 297785232204982028916263

theorem tailTrace_5219412 : CollatzResearch.WordTrace tailWord_5219412 prefixEnd_5219412 297785232204982028916263 := by
  unfold tailWord_5219412
  simp only [CollatzResearch.WordTrace]
  refine ⟨95183797483484601723182245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126911729977979468964242993 95183797483484601723182245)
  ·
    refine ⟨17846962028153362823096671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95183797483484601723182245 17846962028153362823096671)
    ·
      refine ⟨26770443042230044234645007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17846962028153362823096671 26770443042230044234645007)
      ·
        refine ⟨40155664563345066351967511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26770443042230044234645007 40155664563345066351967511)
        ·
          refine ⟨60233496845017599527951267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40155664563345066351967511 60233496845017599527951267)
          ·
            refine ⟨90350245267526399291926901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60233496845017599527951267 90350245267526399291926901)
            ·
              refine ⟨8470335493830599933618147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90350245267526399291926901 8470335493830599933618147)
              ·
                refine ⟨12705503240745899900427221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8470335493830599933618147 12705503240745899900427221)
                ·
                  refine ⟨297785232204982028916263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12705503240745899900427221 297785232204982028916263)
                  ·
                    rfl

theorem cell23_5219412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_5219412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219412 prefixEnd_5219412 := by exact prefixLift 5219412
  have htrace : WordTrace (prefixWord ++ tailWord_5219412) baseStart_5219412 baseEnd_5219412 := by
    simpa [prefixWord, tailWord_5219412, baseEnd_5219412] using wordTrace_append hprefix tailTrace_5219412
  have hstable : (prefixWord ++ tailWord_5219412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219412).length < 2 ^ (prefixWord ++ tailWord_5219412).sum := by decide
  have hdescent : baseEnd_5219412 < baseStart_5219412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219425 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 3, 7]
def baseStart_5219425 : Nat := 118140960795 + 5219425 * 2 ^ 59
def prefixEnd_5219425 : Nat := 4983230072969 + 3 ^ 40 * 5219425 * 2
def baseEnd_5219425 : Nat := 893357921697782236461269

theorem tailTrace_5219425 : CollatzResearch.WordTrace tailWord_5219425 prefixEnd_5219425 893357921697782236461269 := by
  unfold tailWord_5219425
  simp only [CollatzResearch.WordTrace]
  refine ⟨190368069115922106666587729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126912046077281404444391819 190368069115922106666587729)
  ·
    refine ⟨142776051836941579999940797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190368069115922106666587729 142776051836941579999940797)
    ·
      refine ⟨53541019438853092499977799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142776051836941579999940797 53541019438853092499977799)
      ·
        refine ⟨80311529158279638749966699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53541019438853092499977799 80311529158279638749966699)
        ·
          refine ⟨120467293737419458124950049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80311529158279638749966699 120467293737419458124950049)
          ·
            refine ⟨90350470303064593593712537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120467293737419458124950049 90350470303064593593712537)
            ·
              refine ⟨67762852727298445195284403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90350470303064593593712537 67762852727298445195284403)
              ·
                refine ⟨101644279090947667792926605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67762852727298445195284403 101644279090947667792926605)
                ·
                  refine ⟨38116604659105375422347477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101644279090947667792926605 38116604659105375422347477)
                  ·
                    refine ⟨893357921697782236461269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38116604659105375422347477 893357921697782236461269)
                    ·
                      rfl

theorem cell23_5219425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_5219425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219425 prefixEnd_5219425 := by exact prefixLift 5219425
  have htrace : WordTrace (prefixWord ++ tailWord_5219425) baseStart_5219425 baseEnd_5219425 := by
    simpa [prefixWord, tailWord_5219425, baseEnd_5219425] using wordTrace_append hprefix tailTrace_5219425
  have hstable : (prefixWord ++ tailWord_5219425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219425).length < 2 ^ (prefixWord ++ tailWord_5219425).sum := by decide
  have hdescent : baseEnd_5219425 < baseStart_5219425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219479 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 1, 6, 2]
def baseStart_5219479 : Nat := 118140960795 + 5219479 * 2 ^ 59
def prefixEnd_5219479 : Nat := 4983230072969 + 3 ^ 40 * 5219479 * 2
def baseEnd_5219479 : Nat := 2680101493048689498108559

theorem tailTrace_5219479 : CollatzResearch.WordTrace tailWord_5219479 prefixEnd_5219479 2680101493048689498108559 := by
  unfold tailWord_5219479
  simp only [CollatzResearch.WordTrace]
  refine ⟨190370038657726473889053491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126913359105150982592702327 190370038657726473889053491)
  ·
    refine ⟨285555057986589710833580237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190370038657726473889053491 285555057986589710833580237)
    ·
      refine ⟨107083146744971141562592589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285555057986589710833580237 107083146744971141562592589)
      ·
        refine ⟨40156180029364178085972221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107083146744971141562592589 40156180029364178085972221)
        ·
          refine ⟨15058567511011566782239583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40156180029364178085972221 15058567511011566782239583)
          ·
            refine ⟨22587851266517350173359375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15058567511011566782239583 22587851266517350173359375)
            ·
              refine ⟨33881776899776025260039063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22587851266517350173359375 33881776899776025260039063)
              ·
                refine ⟨50822665349664037890058595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33881776899776025260039063 50822665349664037890058595)
                ·
                  refine ⟨76233998024496056835087893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50822665349664037890058595 76233998024496056835087893)
                  ·
                    refine ⟨3573468657398252664144745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76233998024496056835087893 3573468657398252664144745)
                    ·
                      refine ⟨2680101493048689498108559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573468657398252664144745 2680101493048689498108559)
                      ·
                        rfl

theorem cell23_5219479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_5219479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219479 prefixEnd_5219479 := by exact prefixLift 5219479
  have htrace : WordTrace (prefixWord ++ tailWord_5219479) baseStart_5219479 baseEnd_5219479 := by
    simpa [prefixWord, tailWord_5219479, baseEnd_5219479] using wordTrace_append hprefix tailTrace_5219479
  have hstable : (prefixWord ++ tailWord_5219479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219479).length < 2 ^ (prefixWord ++ tailWord_5219479).sum := by decide
  have hdescent : baseEnd_5219479 < baseStart_5219479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219489 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 3, 4]
def baseStart_5219489 : Nat := 118140960795 + 5219489 * 2 ^ 59
def prefixEnd_5219489 : Nat := 4983230072969 + 3 ^ 40 * 5219489 * 2
def baseEnd_5219489 : Nat := 893368875951744819661171

theorem tailTrace_5219489 : CollatzResearch.WordTrace tailWord_5219489 prefixEnd_5219489 893368875951744819661171 := by
  unfold tailWord_5219489
  simp only [CollatzResearch.WordTrace]
  refine ⟨190370403387690245596917521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126913602258460163731278347 190370403387690245596917521)
  ·
    refine ⟨142777802540767684197688141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190370403387690245596917521 142777802540767684197688141)
    ·
      refine ⟨53541675952787881574133053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142777802540767684197688141 53541675952787881574133053)
      ·
        refine ⟨20078128482295455590299895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53541675952787881574133053 20078128482295455590299895)
        ·
          refine ⟨30117192723443183385449843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20078128482295455590299895 30117192723443183385449843)
          ·
            refine ⟨45175789085164775078174765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30117192723443183385449843 45175789085164775078174765)
            ·
              refine ⟨16940920906936790654315537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45175789085164775078174765 16940920906936790654315537)
              ·
                refine ⟨12705690680202592990736653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16940920906936790654315537 12705690680202592990736653)
                ·
                  refine ⟨4764634005075972371526245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12705690680202592990736653 4764634005075972371526245)
                  ·
                    refine ⟨893368875951744819661171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764634005075972371526245 893368875951744819661171)
                    ·
                      rfl

theorem cell23_5219489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_5219489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219489 prefixEnd_5219489 := by exact prefixLift 5219489
  have htrace : WordTrace (prefixWord ++ tailWord_5219489) baseStart_5219489 baseEnd_5219489 := by
    simpa [prefixWord, tailWord_5219489, baseEnd_5219489] using wordTrace_append hprefix tailTrace_5219489
  have hstable : (prefixWord ++ tailWord_5219489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219489).length < 2 ^ (prefixWord ++ tailWord_5219489).sum := by decide
  have hdescent : baseEnd_5219489 < baseStart_5219489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219506 : List Nat := [3, 2, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_5219506 : Nat := 118140960795 + 5219506 * 2 ^ 59
def prefixEnd_5219506 : Nat := 4983230072969 + 3 ^ 40 * 5219506 * 2
def baseEnd_5219506 : Nat := 893371785675453630823645

theorem tailTrace_5219506 : CollatzResearch.WordTrace tailWord_5219506 prefixEnd_5219506 893371785675453630823645 := by
  unfold tailWord_5219506
  simp only [CollatzResearch.WordTrace]
  refine ⟨47592755857157164375071593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126914015619085771666857581 47592755857157164375071593)
  ·
    refine ⟨35694566892867873281303695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47592755857157164375071593 35694566892867873281303695)
    ·
      refine ⟨53541850339301809921955543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35694566892867873281303695 53541850339301809921955543)
      ·
        refine ⟨80312775508952714882933315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53541850339301809921955543 80312775508952714882933315)
        ·
          refine ⟨120469163263429072324399973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80312775508952714882933315 120469163263429072324399973)
          ·
            refine ⟨22587968111892951060824995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120469163263429072324399973 22587968111892951060824995)
            ·
              refine ⟨33881952167839426591237493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22587968111892951060824995 33881952167839426591237493)
              ·
                refine ⟨3176433015734946242928515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33881952167839426591237493 3176433015734946242928515)
                ·
                  refine ⟨4764649523602419364392773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176433015734946242928515 4764649523602419364392773)
                  ·
                    refine ⟨893371785675453630823645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764649523602419364392773 893371785675453630823645)
                    ·
                      rfl

theorem cell23_5219506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_5219506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219506 prefixEnd_5219506 := by exact prefixLift 5219506
  have htrace : WordTrace (prefixWord ++ tailWord_5219506) baseStart_5219506 baseEnd_5219506 := by
    simpa [prefixWord, tailWord_5219506, baseEnd_5219506] using wordTrace_append hprefix tailTrace_5219506
  have hstable : (prefixWord ++ tailWord_5219506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219506).length < 2 ^ (prefixWord ++ tailWord_5219506).sum := by decide
  have hdescent : baseEnd_5219506 < baseStart_5219506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 4, 3, 2]
def baseStart_5219539 : Nat := 118140960795 + 5219539 * 2 ^ 59
def prefixEnd_5219539 : Nat := 4983230072969 + 3 ^ 40 * 5219539 * 2
def baseEnd_5219539 : Nat := 2680132301887959263358283

theorem tailTrace_5219539 : CollatzResearch.WordTrace tailWord_5219539 prefixEnd_5219539 2680132301887959263358283 := by
  unfold tailWord_5219539
  simp only [CollatzResearch.WordTrace]
  refine ⟨190372227037509104136237671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126914818025006069424158447 190372227037509104136237671)
  ·
    refine ⟨285558340556263656204356507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190372227037509104136237671 285558340556263656204356507)
    ·
      refine ⟨428337510834395484306534761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285558340556263656204356507 428337510834395484306534761)
      ·
        refine ⟨321253133125796613229901071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428337510834395484306534761 321253133125796613229901071)
        ·
          refine ⟨481879699688694919844851607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321253133125796613229901071 481879699688694919844851607)
          ·
            refine ⟨722819549533042379767277411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481879699688694919844851607 722819549533042379767277411)
            ·
              refine ⟨1084229324299563569650916117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722819549533042379767277411 1084229324299563569650916117)
              ·
                refine ⟨50823249576542042327386693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1084229324299563569650916117 50823249576542042327386693)
                ·
                  refine ⟨9529359295601632936385005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50823249576542042327386693 9529359295601632936385005)
                  ·
                    refine ⟨3573509735850612351144377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9529359295601632936385005 3573509735850612351144377)
                    ·
                      refine ⟨2680132301887959263358283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573509735850612351144377 2680132301887959263358283)
                      ·
                        rfl

theorem cell23_5219539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3, 2].length) (baseStart_5219539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219539 prefixEnd_5219539 := by exact prefixLift 5219539
  have htrace : WordTrace (prefixWord ++ tailWord_5219539) baseStart_5219539 baseEnd_5219539 := by
    simpa [prefixWord, tailWord_5219539, baseEnd_5219539] using wordTrace_append hprefix tailTrace_5219539
  have hstable : (prefixWord ++ tailWord_5219539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219539).length < 2 ^ (prefixWord ++ tailWord_5219539).sum := by decide
  have hdescent : baseEnd_5219539 < baseStart_5219539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219563 : List Nat := [1, 1, 1, 1, 2, 6, 3, 3, 1, 1, 3]
def baseStart_5219563 : Nat := 118140960795 + 5219563 * 2 ^ 59
def prefixEnd_5219563 : Nat := 4983230072969 + 3 ^ 40 * 5219563 * 2
def baseEnd_5219563 : Nat := 2680144625423667169458173

theorem tailTrace_5219563 : CollatzResearch.WordTrace tailWord_5219563 prefixEnd_5219563 2680144625423667169458173 := by
  unfold tailWord_5219563
  simp only [CollatzResearch.WordTrace]
  refine ⟨190373102389422156235111343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126915401592948104156740895 190373102389422156235111343)
  ·
    refine ⟨285559653584133234352667015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190373102389422156235111343 285559653584133234352667015)
    ·
      refine ⟨428339480376199851529000523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285559653584133234352667015 428339480376199851529000523)
      ·
        refine ⟨642509220564299777293500785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428339480376199851529000523 642509220564299777293500785)
        ·
          refine ⟨481881915423224832970125589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642509220564299777293500785 481881915423224832970125589)
          ·
            refine ⟨22588214785463664045474637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 481881915423224832970125589 22588214785463664045474637)
            ·
              refine ⟨8470580544548874017052989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22588214785463664045474637 8470580544548874017052989)
              ·
                refine ⟨3176467704205827756394871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8470580544548874017052989 3176467704205827756394871)
                ·
                  refine ⟨4764701556308741634592307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176467704205827756394871 4764701556308741634592307)
                  ·
                    refine ⟨7147052334463112451888461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764701556308741634592307 7147052334463112451888461)
                    ·
                      refine ⟨2680144625423667169458173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147052334463112451888461 2680144625423667169458173)
                      ·
                        rfl

theorem cell23_5219563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 1, 3].length) (baseStart_5219563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219563 prefixEnd_5219563 := by exact prefixLift 5219563
  have htrace : WordTrace (prefixWord ++ tailWord_5219563) baseStart_5219563 baseEnd_5219563 := by
    simpa [prefixWord, tailWord_5219563, baseEnd_5219563] using wordTrace_append hprefix tailTrace_5219563
  have hstable : (prefixWord ++ tailWord_5219563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219563).length < 2 ^ (prefixWord ++ tailWord_5219563).sum := by decide
  have hdescent : baseEnd_5219563 < baseStart_5219563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219580 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_5219580 : Nat := 118140960795 + 5219580 * 2 ^ 59
def prefixEnd_5219580 : Nat := 4983230072969 + 3 ^ 40 * 5219580 * 2
def baseEnd_5219580 : Nat := 2680153354594793602945595

theorem tailTrace_5219580 : CollatzResearch.WordTrace tailWord_5219580 prefixEnd_5219580 2680153354594793602945595 := by
  unfold tailWord_5219580
  simp only [CollatzResearch.WordTrace]
  refine ⟨95186861215180284069240097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126915814953573712092320129 95186861215180284069240097)
  ·
    refine ⟨71390145911385213051930073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95186861215180284069240097 71390145911385213051930073)
    ·
      refine ⟨53542609433538909788947555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71390145911385213051930073 53542609433538909788947555)
      ·
        refine ⟨80313914150308364683421333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53542609433538909788947555 80313914150308364683421333)
        ·
          refine ⟨3764714725795704594535375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80313914150308364683421333 3764714725795704594535375)
          ·
            refine ⟨5647072088693556891803063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764714725795704594535375 5647072088693556891803063)
            ·
              refine ⟨8470608133040335337704595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5647072088693556891803063 8470608133040335337704595)
              ·
                refine ⟨12705912199560503006556893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8470608133040335337704595 12705912199560503006556893)
                ·
                  refine ⟨4764717074835188627458835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12705912199560503006556893 4764717074835188627458835)
                  ·
                    refine ⟨7147075612252782941188253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764717074835188627458835 7147075612252782941188253)
                    ·
                      refine ⟨2680153354594793602945595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147075612252782941188253 2680153354594793602945595)
                      ·
                        rfl

theorem cell23_5219580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_5219580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219580 prefixEnd_5219580 := by exact prefixLift 5219580
  have htrace : WordTrace (prefixWord ++ tailWord_5219580) baseStart_5219580 baseEnd_5219580 := by
    simpa [prefixWord, tailWord_5219580, baseEnd_5219580] using wordTrace_append hprefix tailTrace_5219580
  have hstable : (prefixWord ++ tailWord_5219580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219580).length < 2 ^ (prefixWord ++ tailWord_5219580).sum := by decide
  have hdescent : baseEnd_5219580 < baseStart_5219580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219589 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_5219589 : Nat := 118140960795 + 5219589 * 2 ^ 59
def prefixEnd_5219589 : Nat := 4983230072969 + 3 ^ 40 * 5219589 * 2
def baseEnd_5219589 : Nat := 2680157975920684067733053

theorem tailTrace_5219589 : CollatzResearch.WordTrace tailWord_5219589 prefixEnd_5219589 2680157975920684067733053 := by
  unfold tailWord_5219589
  simp only [CollatzResearch.WordTrace]
  refine ⟨190374050687327962675557821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126916033791551975117038547 190374050687327962675557821)
  ·
    refine ⟨71390269007747986003334183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190374050687327962675557821 71390269007747986003334183)
    ·
      refine ⟨107085403511621979005001275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71390269007747986003334183 107085403511621979005001275)
      ·
        refine ⟨160628105267432968507501913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107085403511621979005001275 160628105267432968507501913)
        ·
          refine ⟨120471078950574726380626435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160628105267432968507501913 120471078950574726380626435)
          ·
            refine ⟨180706618425862089570939653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120471078950574726380626435 180706618425862089570939653)
            ·
              refine ⟨33882490954849141794551185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180706618425862089570939653 33882490954849141794551185)
              ·
                refine ⟨25411868216136856345913389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33882490954849141794551185 25411868216136856345913389)
                ·
                  refine ⟨9529450581051321129717521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25411868216136856345913389 9529450581051321129717521)
                  ·
                    refine ⟨7147087935788490847288141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9529450581051321129717521 7147087935788490847288141)
                    ·
                      refine ⟨2680157975920684067733053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147087935788490847288141 2680157975920684067733053)
                      ·
                        rfl

theorem cell23_5219589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_5219589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219589 prefixEnd_5219589 := by exact prefixLift 5219589
  have htrace : WordTrace (prefixWord ++ tailWord_5219589) baseStart_5219589 baseEnd_5219589 := by
    simpa [prefixWord, tailWord_5219589, baseEnd_5219589] using wordTrace_append hprefix tailTrace_5219589
  have hstable : (prefixWord ++ tailWord_5219589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219589).length < 2 ^ (prefixWord ++ tailWord_5219589).sum := by decide
  have hdescent : baseEnd_5219589 < baseStart_5219589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219596 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_5219596 : Nat := 118140960795 + 5219596 * 2 ^ 59
def prefixEnd_5219596 : Nat := 4983230072969 + 3 ^ 40 * 5219596 * 2
def baseEnd_5219596 : Nat := 893387190095088513448507

theorem tailTrace_5219596 : CollatzResearch.WordTrace tailWord_5219596 prefixEnd_5219596 893387190095088513448507 := by
  unfold tailWord_5219596
  simp only [CollatzResearch.WordTrace]
  refine ⟨95187152999151301435531321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126916203998868401914041761 95187152999151301435531321)
  ·
    refine ⟨71390364749363476076648491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95187152999151301435531321 71390364749363476076648491)
    ·
      refine ⟨107085547124045214114972737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71390364749363476076648491 107085547124045214114972737)
      ·
        refine ⟨80314160343033910586229553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107085547124045214114972737 80314160343033910586229553)
        ·
          refine ⟨60235620257275432939672165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80314160343033910586229553 60235620257275432939672165)
          ·
            refine ⟨11294178798239143676188531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60235620257275432939672165 11294178798239143676188531)
            ·
              refine ⟨16941268197358715514282797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11294178798239143676188531 16941268197358715514282797)
              ·
                refine ⟨6352975574009518317856049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16941268197358715514282797 6352975574009518317856049)
                ·
                  refine ⟨4764731680507138738392037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352975574009518317856049 4764731680507138738392037)
                  ·
                    refine ⟨893387190095088513448507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764731680507138738392037 893387190095088513448507)
                    ·
                      rfl

theorem cell23_5219596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_5219596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219596 prefixEnd_5219596 := by exact prefixLift 5219596
  have htrace : WordTrace (prefixWord ++ tailWord_5219596) baseStart_5219596 baseEnd_5219596 := by
    simpa [prefixWord, tailWord_5219596, baseEnd_5219596] using wordTrace_append hprefix tailTrace_5219596
  have hstable : (prefixWord ++ tailWord_5219596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219596).length < 2 ^ (prefixWord ++ tailWord_5219596).sum := by decide
  have hdescent : baseEnd_5219596 < baseStart_5219596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219616 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5219616 : Nat := 118140960795 + 5219616 * 2 ^ 59
def prefixEnd_5219616 : Nat := 4983230072969 + 3 ^ 40 * 5219616 * 2
def baseEnd_5219616 : Nat := 2680171839898355462095429

theorem tailTrace_5219616 : CollatzResearch.WordTrace tailWord_5219616 prefixEnd_5219616 2680171839898355462095429 := by
  unfold tailWord_5219616
  simp only [CollatzResearch.WordTrace]
  refine ⟨95187517729115073143395351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126916690305486764191193801 95187517729115073143395351)
  ·
    refine ⟨142781276593672609715093027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95187517729115073143395351 142781276593672609715093027)
    ·
      refine ⟨214171914890508914572639541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142781276593672609715093027 214171914890508914572639541)
      ·
        refine ⟨20078617020985210741184957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214171914890508914572639541 20078617020985210741184957)
        ·
          refine ⟨7529481382869454027944359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20078617020985210741184957 7529481382869454027944359)
          ·
            refine ⟨11294222074304181041916539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529481382869454027944359 11294222074304181041916539)
            ·
              refine ⟨16941333111456271562874809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11294222074304181041916539 16941333111456271562874809)
              ·
                refine ⟨12705999833592203672156107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16941333111456271562874809 12705999833592203672156107)
                ·
                  refine ⟨19058999750388305508234161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12705999833592203672156107 19058999750388305508234161)
                  ·
                    refine ⟨14294249812791229131175621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19058999750388305508234161 14294249812791229131175621)
                    ·
                      refine ⟨2680171839898355462095429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14294249812791229131175621 2680171839898355462095429)
                      ·
                        rfl

theorem cell23_5219616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5219616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219616 prefixEnd_5219616 := by exact prefixLift 5219616
  have htrace : WordTrace (prefixWord ++ tailWord_5219616) baseStart_5219616 baseEnd_5219616 := by
    simpa [prefixWord, tailWord_5219616, baseEnd_5219616] using wordTrace_append hprefix tailTrace_5219616
  have hstable : (prefixWord ++ tailWord_5219616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219616).length < 2 ^ (prefixWord ++ tailWord_5219616).sum := by decide
  have hdescent : baseEnd_5219616 < baseStart_5219616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219619 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 3]
def baseStart_5219619 : Nat := 118140960795 + 5219619 * 2 ^ 59
def prefixEnd_5219619 : Nat := 4983230072969 + 3 ^ 40 * 5219619 * 2
def baseEnd_5219619 : Nat := 2680173380340318950357915

theorem tailTrace_5219619 : CollatzResearch.WordTrace tailWord_5219619 prefixEnd_5219619 2680173380340318950357915 := by
  unfold tailWord_5219619
  simp only [CollatzResearch.WordTrace]
  refine ⟨190375144877219277799149911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126916763251479518532766607 190375144877219277799149911)
  ·
    refine ⟨285562717315828916698724867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190375144877219277799149911 285562717315828916698724867)
    ·
      refine ⟨428344075973743375048087301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285562717315828916698724867 428344075973743375048087301)
      ·
        refine ⟨80314514245076882821516369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428344075973743375048087301 80314514245076882821516369)
        ·
          refine ⟨60235885683807662116137277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80314514245076882821516369 60235885683807662116137277)
          ·
            refine ⟨22588457131427873293551479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60235885683807662116137277 22588457131427873293551479)
            ·
              refine ⟨33882685697141809940327219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22588457131427873293551479 33882685697141809940327219)
              ·
                refine ⟨50824028545712714910490829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33882685697141809940327219 50824028545712714910490829)
                ·
                  refine ⟨19059010704642268091434061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50824028545712714910490829 19059010704642268091434061)
                  ·
                    refine ⟨7147129014240850534287773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19059010704642268091434061 7147129014240850534287773)
                    ·
                      refine ⟨2680173380340318950357915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147129014240850534287773 2680173380340318950357915)
                      ·
                        rfl

theorem cell23_5219619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_5219619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219619 prefixEnd_5219619 := by exact prefixLift 5219619
  have htrace : WordTrace (prefixWord ++ tailWord_5219619) baseStart_5219619 baseEnd_5219619 := by
    simpa [prefixWord, tailWord_5219619, baseEnd_5219619] using wordTrace_append hprefix tailTrace_5219619
  have hstable : (prefixWord ++ tailWord_5219619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219619).length < 2 ^ (prefixWord ++ tailWord_5219619).sum := by decide
  have hdescent : baseEnd_5219619 < baseStart_5219619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219620 : List Nat := [2, 3, 1, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_5219620 : Nat := 118140960795 + 5219620 * 2 ^ 59
def prefixEnd_5219620 : Nat := 4983230072969 + 3 ^ 40 * 5219620 * 2
def baseEnd_5219620 : Nat := 2680173893820973446445411

theorem tailTrace_5219620 : CollatzResearch.WordTrace tailWord_5219620 prefixEnd_5219620 2680173893820973446445411 := by
  unfold tailWord_5219620
  simp only [CollatzResearch.WordTrace]
  refine ⟨95187590675107827484968157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126916787566810436646624209 95187590675107827484968157)
  ·
    refine ⟨35695346503165435306863059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95187590675107827484968157 35695346503165435306863059)
    ·
      refine ⟨53543019754748152960294589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35695346503165435306863059 53543019754748152960294589)
      ·
        refine ⟨20078632408030557360110471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53543019754748152960294589 20078632408030557360110471)
        ·
          refine ⟨30117948612045836040165707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20078632408030557360110471 30117948612045836040165707)
          ·
            refine ⟨45176922918068754060248561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30117948612045836040165707 45176922918068754060248561)
            ·
              refine ⟨33882692188551565545186421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45176922918068754060248561 33882692188551565545186421)
              ·
                refine ⟨3176502392676709269861227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33882692188551565545186421 3176502392676709269861227)
                ·
                  refine ⟨4764753589015063904791841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176502392676709269861227 4764753589015063904791841)
                  ·
                    refine ⟨3573565191761297928593881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4764753589015063904791841 3573565191761297928593881)
                    ·
                      refine ⟨2680173893820973446445411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573565191761297928593881 2680173893820973446445411)
                      ·
                        rfl

theorem cell23_5219620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_5219620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219620 prefixEnd_5219620 := by exact prefixLift 5219620
  have htrace : WordTrace (prefixWord ++ tailWord_5219620) baseStart_5219620 baseEnd_5219620 := by
    simpa [prefixWord, tailWord_5219620, baseEnd_5219620] using wordTrace_append hprefix tailTrace_5219620
  have hstable : (prefixWord ++ tailWord_5219620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219620).length < 2 ^ (prefixWord ++ tailWord_5219620).sum := by decide
  have hdescent : baseEnd_5219620 < baseStart_5219620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219636 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_5219636 : Nat := 118140960795 + 5219636 * 2 ^ 59
def prefixEnd_5219636 : Nat := 4983230072969 + 3 ^ 40 * 5219636 * 2
def baseEnd_5219636 : Nat := 2680182109511445383845337

theorem tailTrace_5219636 : CollatzResearch.WordTrace tailWord_5219636 prefixEnd_5219636 2680182109511445383845337 := by
  unfold tailWord_5219636
  simp only [CollatzResearch.WordTrace]
  refine ⟨95187882459078844851259381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126917176612105126468345841 95187882459078844851259381)
  ·
    refine ⟨8923863980538641704805567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95187882459078844851259381 8923863980538641704805567)
    ·
      refine ⟨13385795970807962557208351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8923863980538641704805567 13385795970807962557208351)
      ·
        refine ⟨20078693956211943835812527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13385795970807962557208351 20078693956211943835812527)
        ·
          refine ⟨30118040934317915753718791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20078693956211943835812527 30118040934317915753718791)
          ·
            refine ⟨45177061401476873630578187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30118040934317915753718791 45177061401476873630578187)
            ·
              refine ⟨67765592102215310445867281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45177061401476873630578187 67765592102215310445867281)
              ·
                refine ⟨50824194076661482834400461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67765592102215310445867281 50824194076661482834400461)
                ·
                  refine ⟨19059072778748056062900173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50824194076661482834400461 19059072778748056062900173)
                  ·
                    refine ⟨7147152292030521023587565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19059072778748056062900173 7147152292030521023587565)
                    ·
                      refine ⟨2680182109511445383845337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147152292030521023587565 2680182109511445383845337)
                      ·
                        rfl

theorem cell23_5219636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_5219636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219636 prefixEnd_5219636 := by exact prefixLift 5219636
  have htrace : WordTrace (prefixWord ++ tailWord_5219636) baseStart_5219636 baseEnd_5219636 := by
    simpa [prefixWord, tailWord_5219636, baseEnd_5219636] using wordTrace_append hprefix tailTrace_5219636
  have hstable : (prefixWord ++ tailWord_5219636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219636).length < 2 ^ (prefixWord ++ tailWord_5219636).sum := by decide
  have hdescent : baseEnd_5219636 < baseStart_5219636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219637 : List Nat := [1, 3, 3, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_5219637 : Nat := 118140960795 + 5219637 * 2 ^ 59
def prefixEnd_5219637 : Nat := 4983230072969 + 3 ^ 40 * 5219637 * 2
def baseEnd_5219637 : Nat := 2680182622992099879932833

theorem tailTrace_5219637 : CollatzResearch.WordTrace tailWord_5219637 prefixEnd_5219637 2680182622992099879932833 := by
  unfold tailWord_5219637
  simp only [CollatzResearch.WordTrace]
  refine ⟨190375801391154066873305165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126917200927436044582203443 190375801391154066873305165)
  ·
    refine ⟨71390925521682775077489437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190375801391154066873305165 71390925521682775077489437)
    ·
      refine ⟨26771597070631040654058539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71390925521682775077489437 26771597070631040654058539)
      ·
        refine ⟨40157395605946560981087809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26771597070631040654058539 40157395605946560981087809)
        ·
          refine ⟨30118046704459920735815857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40157395605946560981087809 30118046704459920735815857)
          ·
            refine ⟨22588535028344940551861893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30118046704459920735815857 22588535028344940551861893)
            ·
              refine ⟨4235350317814676353474105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22588535028344940551861893 4235350317814676353474105)
              ·
                refine ⟨3176512738361007265105579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4235350317814676353474105 3176512738361007265105579)
                ·
                  refine ⟨4764769107541510897658369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176512738361007265105579 4764769107541510897658369)
                  ·
                    refine ⟨3573576830656133173243777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4764769107541510897658369 3573576830656133173243777)
                    ·
                      refine ⟨2680182622992099879932833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573576830656133173243777 2680182622992099879932833)
                      ·
                        rfl

theorem cell23_5219637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_5219637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219637 prefixEnd_5219637 := by exact prefixLift 5219637
  have htrace : WordTrace (prefixWord ++ tailWord_5219637) baseStart_5219637 baseEnd_5219637 := by
    simpa [prefixWord, tailWord_5219637, baseEnd_5219637] using wordTrace_append hprefix tailTrace_5219637
  have hstable : (prefixWord ++ tailWord_5219637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219637).length < 2 ^ (prefixWord ++ tailWord_5219637).sum := by decide
  have hdescent : baseEnd_5219637 < baseStart_5219637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219654 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5219654 : Nat := 118140960795 + 5219654 * 2 ^ 59
def prefixEnd_5219654 : Nat := 4983230072969 + 3 ^ 40 * 5219654 * 2
def baseEnd_5219654 : Nat := 2680191352163226313420255

theorem tailTrace_5219654 : CollatzResearch.WordTrace tailWord_5219654 prefixEnd_5219654 2680191352163226313420255 := by
  unfold tailWord_5219654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949263169752889961771063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126917614288061652517782677 5949263169752889961771063)
  ·
    refine ⟨8923894754629334942656595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5949263169752889961771063 8923894754629334942656595)
    ·
      refine ⟨13385842131944002413984893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8923894754629334942656595 13385842131944002413984893)
      ·
        refine ⟨5019690799479000905244335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13385842131944002413984893 5019690799479000905244335)
        ·
          refine ⟨7529536199218501357866503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5019690799479000905244335 7529536199218501357866503)
          ·
            refine ⟨11294304298827752036799755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529536199218501357866503 11294304298827752036799755)
            ·
              refine ⟨16941456448241628055199633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11294304298827752036799755 16941456448241628055199633)
              ·
                refine ⟨12706092336181221041399725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16941456448241628055199633 12706092336181221041399725)
                ·
                  refine ⟨4764784626067957890524897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12706092336181221041399725 4764784626067957890524897)
                  ·
                    refine ⟨3573588469550968417893673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4764784626067957890524897 3573588469550968417893673)
                    ·
                      refine ⟨2680191352163226313420255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573588469550968417893673 2680191352163226313420255)
                      ·
                        rfl

theorem cell23_5219654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5219654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219654 prefixEnd_5219654 := by exact prefixLift 5219654
  have htrace : WordTrace (prefixWord ++ tailWord_5219654) baseStart_5219654 baseEnd_5219654 := by
    simpa [prefixWord, tailWord_5219654, baseEnd_5219654] using wordTrace_append hprefix tailTrace_5219654
  have hstable : (prefixWord ++ tailWord_5219654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219654).length < 2 ^ (prefixWord ++ tailWord_5219654).sum := by decide
  have hdescent : baseEnd_5219654 < baseStart_5219654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219680 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 1, 3, 2]
def baseStart_5219680 : Nat := 118140960795 + 5219680 * 2 ^ 59
def prefixEnd_5219680 : Nat := 4983230072969 + 3 ^ 40 * 5219680 * 2
def baseEnd_5219680 : Nat := 2680204702660243211695135

theorem tailTrace_5219680 : CollatzResearch.WordTrace tailWord_5219680 prefixEnd_5219680 2680204702660243211695135 := by
  unfold tailWord_5219680
  simp only [CollatzResearch.WordTrace]
  refine ⟨95188684864999142608560247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126918246486665523478080329 95188684864999142608560247)
  ·
    refine ⟨142783027297498713912840371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95188684864999142608560247 142783027297498713912840371)
    ·
      refine ⟨214174540946248070869260557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142783027297498713912840371 214174540946248070869260557)
      ·
        refine ⟨80315452854843026575972709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214174540946248070869260557 80315452854843026575972709)
        ·
          refine ⟨15059147410283067482994883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80315452854843026575972709 15059147410283067482994883)
          ·
            refine ⟨22588721115424601224492325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15059147410283067482994883 22588721115424601224492325)
            ·
              refine ⟨4235385209142112729592311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22588721115424601224492325 4235385209142112729592311)
              ·
                refine ⟨6353077813713169094388467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235385209142112729592311 6353077813713169094388467)
                ·
                  refine ⟨9529616720569753641582701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6353077813713169094388467 9529616720569753641582701)
                  ·
                    refine ⟨3573606270213657615593513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9529616720569753641582701 3573606270213657615593513)
                    ·
                      refine ⟨2680204702660243211695135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573606270213657615593513 2680204702660243211695135)
                      ·
                        rfl

theorem cell23_5219680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_5219680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219680 prefixEnd_5219680 := by exact prefixLift 5219680
  have htrace : WordTrace (prefixWord ++ tailWord_5219680) baseStart_5219680 baseEnd_5219680 := by
    simpa [prefixWord, tailWord_5219680, baseEnd_5219680] using wordTrace_append hprefix tailTrace_5219680
  have hstable : (prefixWord ++ tailWord_5219680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219680).length < 2 ^ (prefixWord ++ tailWord_5219680).sum := by decide
  have hdescent : baseEnd_5219680 < baseStart_5219680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219687 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_5219687 : Nat := 118140960795 + 5219687 * 2 ^ 59
def prefixEnd_5219687 : Nat := 4983230072969 + 3 ^ 40 * 5219687 * 2
def baseEnd_5219687 : Nat := 2680208297024824684307603

theorem tailTrace_5219687 : CollatzResearch.WordTrace tailWord_5219687 prefixEnd_5219687 2680208297024824684307603 := by
  unfold tailWord_5219687
  simp only [CollatzResearch.WordTrace]
  refine ⟨190377625040972925412625315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126918416693981950275083543 190377625040972925412625315)
  ·
    refine ⟨285566437561459388118937973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190377625040972925412625315 285566437561459388118937973)
    ·
      refine ⟨26771853521386817636150435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285566437561459388118937973 26771853521386817636150435)
      ·
        refine ⟨40157780282080226454225653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26771853521386817636150435 40157780282080226454225653)
        ·
          refine ⟨3764791901445021230083655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40157780282080226454225653 3764791901445021230083655)
          ·
            refine ⟨5647187852167531845125483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764791901445021230083655 5647187852167531845125483)
            ·
              refine ⟨8470781778251297767688225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5647187852167531845125483 8470781778251297767688225)
              ·
                refine ⟨6353086333688473325766169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8470781778251297767688225 6353086333688473325766169)
                ·
                  refine ⟨4764814750266354994324627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6353086333688473325766169 4764814750266354994324627)
                  ·
                    refine ⟨7147222125399532491486941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764814750266354994324627 7147222125399532491486941)
                    ·
                      refine ⟨2680208297024824684307603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147222125399532491486941 2680208297024824684307603)
                      ·
                        rfl

theorem cell23_5219687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_5219687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219687 prefixEnd_5219687 := by exact prefixLift 5219687
  have htrace : WordTrace (prefixWord ++ tailWord_5219687) baseStart_5219687 baseEnd_5219687 := by
    simpa [prefixWord, tailWord_5219687, baseEnd_5219687] using wordTrace_append hprefix tailTrace_5219687
  have hstable : (prefixWord ++ tailWord_5219687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219687).length < 2 ^ (prefixWord ++ tailWord_5219687).sum := by decide
  have hdescent : baseEnd_5219687 < baseStart_5219687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219746 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_5219746 : Nat := 118140960795 + 5219746 * 2 ^ 59
def prefixEnd_5219746 : Nat := 4983230072969 + 3 ^ 40 * 5219746 * 2
def baseEnd_5219746 : Nat := 893412864127813317823277

theorem tailTrace_5219746 : CollatzResearch.WordTrace tailWord_5219746 prefixEnd_5219746 893412864127813317823277 := by
  unfold tailWord_5219746
  simp only [CollatzResearch.WordTrace]
  refine ⟨47594944236939794622255773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126919851298506118992682061 47594944236939794622255773)
  ·
    refine ⟨17848104088852422983345915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47594944236939794622255773 17848104088852422983345915)
    ·
      refine ⟨26772156133278634475018873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17848104088852422983345915 26772156133278634475018873)
      ·
        refine ⟨20079117099958975856264155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26772156133278634475018873 20079117099958975856264155)
        ·
          refine ⟨30118675649938463784396233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20079117099958975856264155 30118675649938463784396233)
          ·
            refine ⟨22589006737453847838297175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30118675649938463784396233 22589006737453847838297175)
            ·
              refine ⟨33883510106180771757445763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22589006737453847838297175 33883510106180771757445763)
              ·
                refine ⟨50825265159271157636168645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33883510106180771757445763 50825265159271157636168645)
                ·
                  refine ⟨9529737217363342056781621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50825265159271157636168645 9529737217363342056781621)
                  ·
                    refine ⟨893412864127813317823277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9529737217363342056781621 893412864127813317823277)
                    ·
                      rfl

theorem cell23_5219746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_5219746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219746 prefixEnd_5219746 := by exact prefixLift 5219746
  have htrace : WordTrace (prefixWord ++ tailWord_5219746) baseStart_5219746 baseEnd_5219746 := by
    simpa [prefixWord, tailWord_5219746, baseEnd_5219746] using wordTrace_append hprefix tailTrace_5219746
  have hstable : (prefixWord ++ tailWord_5219746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219746).length < 2 ^ (prefixWord ++ tailWord_5219746).sum := by decide
  have hdescent : baseEnd_5219746 < baseStart_5219746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219749 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_5219749 : Nat := 118140960795 + 5219749 * 2 ^ 59
def prefixEnd_5219749 : Nat := 4983230072969 + 3 ^ 40 * 5219749 * 2
def baseEnd_5219749 : Nat := 2680240132825403441732317

theorem tailTrace_5219749 : CollatzResearch.WordTrace tailWord_5219749 prefixEnd_5219749 2680240132825403441732317 := by
  unfold tailWord_5219749
  simp only [CollatzResearch.WordTrace]
  refine ⟨190379886366748310001382301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126919924244498873334254867 190379886366748310001382301)
  ·
    refine ⟨71392457387530616250518363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190379886366748310001382301 71392457387530616250518363)
    ·
      refine ⟨107088686081295924375777545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71392457387530616250518363 107088686081295924375777545)
      ·
        refine ⟨80316514560971943281833159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107088686081295924375777545 80316514560971943281833159)
        ·
          refine ⟨120474771841457914922749739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80316514560971943281833159 120474771841457914922749739)
          ·
            refine ⟨180712157762186872384124609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120474771841457914922749739 180712157762186872384124609)
            ·
              refine ⟨135534118321640154288093457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180712157762186872384124609 135534118321640154288093457)
              ·
                refine ⟨101650588741230115716070093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135534118321640154288093457 101650588741230115716070093)
                ·
                  refine ⟨38118970777961293393526285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101650588741230115716070093 38118970777961293393526285)
                  ·
                    refine ⟨14294614041735485022572357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38118970777961293393526285 14294614041735485022572357)
                    ·
                      refine ⟨2680240132825403441732317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14294614041735485022572357 2680240132825403441732317)
                      ·
                        rfl

theorem cell23_5219749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_5219749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219749 prefixEnd_5219749 := by exact prefixLift 5219749
  have htrace : WordTrace (prefixWord ++ tailWord_5219749) baseStart_5219749 baseEnd_5219749 := by
    simpa [prefixWord, tailWord_5219749, baseEnd_5219749] using wordTrace_append hprefix tailTrace_5219749
  have hstable : (prefixWord ++ tailWord_5219749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219749).length < 2 ^ (prefixWord ++ tailWord_5219749).sum := by decide
  have hdescent : baseEnd_5219749 < baseStart_5219749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219776 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 3, 4]
def baseStart_5219776 : Nat := 118140960795 + 5219776 * 2 ^ 59
def prefixEnd_5219776 : Nat := 4983230072969 + 3 ^ 40 * 5219776 * 2
def baseEnd_5219776 : Nat := 893417998934358278698231

theorem tailTrace_5219776 : CollatzResearch.WordTrace tailWord_5219776 prefixEnd_5219776 893417998934358278698231 := by
  unfold tailWord_5219776
  simp only [CollatzResearch.WordTrace]
  refine ⟨95190435568825246806307591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126920580758433662408410121 95190435568825246806307591)
  ·
    refine ⟨142785653353237870209461387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95190435568825246806307591 142785653353237870209461387)
    ·
      refine ⟨214178480029856805314192081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142785653353237870209461387 214178480029856805314192081)
      ·
        refine ⟨160633860022392603985644061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214178480029856805314192081 160633860022392603985644061)
        ·
          refine ⟨60237697508397226494616523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160633860022392603985644061 60237697508397226494616523)
          ·
            refine ⟨90356546262595839741924785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60237697508397226494616523 90356546262595839741924785)
            ·
              refine ⟨67767409696946879806443589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90356546262595839741924785 67767409696946879806443589)
              ·
                refine ⟨12706389318177539963708173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67767409696946879806443589 12706389318177539963708173)
                ·
                  refine ⟨4764895994316577486390565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12706389318177539963708173 4764895994316577486390565)
                  ·
                    refine ⟨893417998934358278698231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764895994316577486390565 893417998934358278698231)
                    ·
                      rfl

theorem cell23_5219776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_5219776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219776 prefixEnd_5219776 := by exact prefixLift 5219776
  have htrace : WordTrace (prefixWord ++ tailWord_5219776) baseStart_5219776 baseEnd_5219776 := by
    simpa [prefixWord, tailWord_5219776, baseEnd_5219776] using wordTrace_append hprefix tailTrace_5219776
  have hstable : (prefixWord ++ tailWord_5219776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219776).length < 2 ^ (prefixWord ++ tailWord_5219776).sum := by decide
  have hdescent : baseEnd_5219776 < baseStart_5219776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219779 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4]
def baseStart_5219779 : Nat := 118140960795 + 5219779 * 2 ^ 59
def prefixEnd_5219779 : Nat := 4983230072969 + 3 ^ 40 * 5219779 * 2
def baseEnd_5219779 : Nat := 2680255537245038324357179

theorem tailTrace_5219779 : CollatzResearch.WordTrace tailWord_5219779 prefixEnd_5219779 2680255537245038324357179 := by
  unfold tailWord_5219779
  simp only [CollatzResearch.WordTrace]
  refine ⟨190380980556639625124974391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126920653704426416749982927 190380980556639625124974391)
  ·
    refine ⟨285571470834959437687461587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190380980556639625124974391 285571470834959437687461587)
    ·
      refine ⟨428357206252439156531192381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285571470834959437687461587 428357206252439156531192381)
      ·
        refine ⟨160633952344664683699197143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428357206252439156531192381 160633952344664683699197143)
        ·
          refine ⟨240950928516997025548795715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160633952344664683699197143 240950928516997025548795715)
          ·
            refine ⟨361426392775495538323193573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240950928516997025548795715 361426392775495538323193573)
            ·
              refine ⟨67767448645405413435598795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 361426392775495538323193573 67767448645405413435598795)
              ·
                refine ⟨101651172968108120153398193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67767448645405413435598795 101651172968108120153398193)
                ·
                  refine ⟨76238379726081090115048645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101651172968108120153398193 76238379726081090115048645)
                  ·
                    refine ⟨14294696198640204396571621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76238379726081090115048645 14294696198640204396571621)
                    ·
                      refine ⟨2680255537245038324357179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14294696198640204396571621 2680255537245038324357179)
                      ·
                        rfl

theorem cell23_5219779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_5219779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219779 prefixEnd_5219779 := by exact prefixLift 5219779
  have htrace : WordTrace (prefixWord ++ tailWord_5219779) baseStart_5219779 baseEnd_5219779 := by
    simpa [prefixWord, tailWord_5219779, baseEnd_5219779] using wordTrace_append hprefix tailTrace_5219779
  have hstable : (prefixWord ++ tailWord_5219779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219779).length < 2 ^ (prefixWord ++ tailWord_5219779).sum := by decide
  have hdescent : baseEnd_5219779 < baseStart_5219779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219836 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_5219836 : Nat := 118140960795 + 5219836 * 2 ^ 59
def prefixEnd_5219836 : Nat := 4983230072969 + 3 ^ 40 * 5219836 * 2
def baseEnd_5219836 : Nat := 893428268547448200448139

theorem tailTrace_5219836 : CollatzResearch.WordTrace tailWord_5219836 prefixEnd_5219836 893428268547448200448139 := by
  unfold tailWord_5219836
  simp only [CollatzResearch.WordTrace]
  refine ⟨95191529758716561929899681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126922039678288749239866241 95191529758716561929899681)
  ·
    refine ⟨71393647319037421447424761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95191529758716561929899681 71393647319037421447424761)
    ·
      refine ⟨53545235489278066085568571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71393647319037421447424761 53545235489278066085568571)
      ·
        refine ⟨80317853233917099128352857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53545235489278066085568571 80317853233917099128352857)
        ·
          refine ⟨60238389925437824346264643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80317853233917099128352857 60238389925437824346264643)
          ·
            refine ⟨90357584888156736519396965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60238389925437824346264643 90357584888156736519396965)
            ·
              refine ⟨16942047166529388097386931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90357584888156736519396965 16942047166529388097386931)
              ·
                refine ⟨25413070749794082146080397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16942047166529388097386931 25413070749794082146080397)
                ·
                  refine ⟨9529901531172780804780149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25413070749794082146080397 9529901531172780804780149)
                  ·
                    refine ⟨893428268547448200448139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9529901531172780804780149 893428268547448200448139)
                    ·
                      rfl

theorem cell23_5219836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_5219836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219836 prefixEnd_5219836 := by exact prefixLift 5219836
  have htrace : WordTrace (prefixWord ++ tailWord_5219836) baseStart_5219836 baseEnd_5219836 := by
    simpa [prefixWord, tailWord_5219836, baseEnd_5219836] using wordTrace_append hprefix tailTrace_5219836
  have hstable : (prefixWord ++ tailWord_5219836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219836).length < 2 ^ (prefixWord ++ tailWord_5219836).sum := by decide
  have hdescent : baseEnd_5219836 < baseStart_5219836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219843 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 2, 3, 2]
def baseStart_5219843 : Nat := 118140960795 + 5219843 * 2 ^ 59
def prefixEnd_5219843 : Nat := 4983230072969 + 3 ^ 40 * 5219843 * 2
def baseEnd_5219843 : Nat := 2680288400006926073956885

theorem tailTrace_5219843 : CollatzResearch.WordTrace tailWord_5219843 prefixEnd_5219843 2680288400006926073956885 := by
  unfold tailWord_5219843
  simp only [CollatzResearch.WordTrace]
  refine ⟨190383314828407764055304183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126922209885605176036869455 190383314828407764055304183)
  ·
    refine ⟨285574972242611646082956275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190383314828407764055304183 285574972242611646082956275)
    ·
      refine ⟨428362458363917469124434413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285574972242611646082956275 428362458363917469124434413)
      ·
        refine ⟨160635921886469050921662905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428362458363917469124434413 160635921886469050921662905)
        ·
          refine ⟨120476941414851788191247179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160635921886469050921662905 120476941414851788191247179)
          ·
            refine ⟨180715412122277682286870769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120476941414851788191247179 180715412122277682286870769)
            ·
              refine ⟨135536559091708261715153077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180715412122277682286870769 135536559091708261715153077)
              ·
                refine ⟨12706552414847649535795601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135536559091708261715153077 12706552414847649535795601)
                ·
                  refine ⟨9529914311135737151846701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12706552414847649535795601 9529914311135737151846701)
                  ·
                    refine ⟨3573717866675901431942513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9529914311135737151846701 3573717866675901431942513)
                    ·
                      refine ⟨2680288400006926073956885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573717866675901431942513 2680288400006926073956885)
                      ·
                        rfl

theorem cell23_5219843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_5219843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219843 prefixEnd_5219843 := by exact prefixLift 5219843
  have htrace : WordTrace (prefixWord ++ tailWord_5219843) baseStart_5219843 baseEnd_5219843 := by
    simpa [prefixWord, tailWord_5219843, baseEnd_5219843] using wordTrace_append hprefix tailTrace_5219843
  have hstable : (prefixWord ++ tailWord_5219843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219843).length < 2 ^ (prefixWord ++ tailWord_5219843).sum := by decide
  have hdescent : baseEnd_5219843 < baseStart_5219843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219896 : List Nat := [2, 1, 2, 1, 4, 3, 1, 9]
def baseStart_5219896 : Nat := 118140960795 + 5219896 * 2 ^ 59
def prefixEnd_5219896 : Nat := 4983230072969 + 3 ^ 40 * 5219896 * 2
def baseEnd_5219896 : Nat := 99270948684504235799783

theorem tailTrace_5219896 : CollatzResearch.WordTrace tailWord_5219896 prefixEnd_5219896 99270948684504235799783 := by
  unfold tailWord_5219896
  simp only [CollatzResearch.WordTrace]
  refine ⟨95192623948607877053491771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126923498598143836071322361 95192623948607877053491771)
  ·
    refine ⟨142788935922911815580237657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95192623948607877053491771 142788935922911815580237657)
    ·
      refine ⟨107091701942183861685178243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142788935922911815580237657 107091701942183861685178243)
      ·
        refine ⟨160637552913275792527767365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107091701942183861685178243 160637552913275792527767365)
        ·
          refine ⟨30119541171239211098956381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160637552913275792527767365 30119541171239211098956381)
          ·
            refine ⟨11294827939214704162108643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30119541171239211098956381 11294827939214704162108643)
            ·
              refine ⟨16942241908822056243162965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11294827939214704162108643 16942241908822056243162965)
              ·
                refine ⟨99270948684504235799783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16942241908822056243162965 99270948684504235799783)
                ·
                  rfl

theorem cell23_5219896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 9].length) (baseStart_5219896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219896 prefixEnd_5219896 := by exact prefixLift 5219896
  have htrace : WordTrace (prefixWord ++ tailWord_5219896) baseStart_5219896 baseEnd_5219896 := by
    simpa [prefixWord, tailWord_5219896, baseEnd_5219896] using wordTrace_append hprefix tailTrace_5219896
  have hstable : (prefixWord ++ tailWord_5219896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219896).length < 2 ^ (prefixWord ++ tailWord_5219896).sum := by decide
  have hdescent : baseEnd_5219896 < baseStart_5219896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5219901 : List Nat := [1, 4, 1, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_5219901 : Nat := 118140960795 + 5219901 * 2 ^ 59
def prefixEnd_5219901 : Nat := 4983230072969 + 3 ^ 40 * 5219901 * 2
def baseEnd_5219901 : Nat := 2680318181884886847031619

theorem tailTrace_5219901 : CollatzResearch.WordTrace tailWord_5219901 prefixEnd_5219901 2680318181884886847031619 := by
  unfold tailWord_5219901
  simp only [CollatzResearch.WordTrace]
  refine ⟨190385430262197639960915557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126923620174798426640610371 190385430262197639960915557)
  ·
    refine ⟨35697268174162057492671667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190385430262197639960915557 35697268174162057492671667)
    ·
      refine ⟨53545902261243086239007501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35697268174162057492671667 53545902261243086239007501)
      ·
        refine ⟨20079713347966157339627813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53545902261243086239007501 20079713347966157339627813)
        ·
          refine ⟨3764946252743654501180215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20079713347966157339627813 3764946252743654501180215)
          ·
            refine ⟨5647419379115481751770323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764946252743654501180215 5647419379115481751770323)
            ·
              refine ⟨8471129068673222627655485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5647419379115481751770323 8471129068673222627655485)
              ·
                refine ⟨3176673400752458485370807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8471129068673222627655485 3176673400752458485370807)
                ·
                  refine ⟨4765010101128687728056211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176673400752458485370807 4765010101128687728056211)
                  ·
                    refine ⟨7147515151693031592084317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4765010101128687728056211 7147515151693031592084317)
                    ·
                      refine ⟨2680318181884886847031619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147515151693031592084317 2680318181884886847031619)
                      ·
                        rfl

theorem cell23_5219901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_5219901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5219901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5219901 prefixEnd_5219901 := by exact prefixLift 5219901
  have htrace : WordTrace (prefixWord ++ tailWord_5219901) baseStart_5219901 baseEnd_5219901 := by
    simpa [prefixWord, tailWord_5219901, baseEnd_5219901] using wordTrace_append hprefix tailTrace_5219901
  have hstable : (prefixWord ++ tailWord_5219901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5219901).length < 2 ^ (prefixWord ++ tailWord_5219901).sum := by decide
  have hdescent : baseEnd_5219901 < baseStart_5219901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5219901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
