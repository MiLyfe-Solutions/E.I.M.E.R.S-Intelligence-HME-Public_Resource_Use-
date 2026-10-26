import V185TrunkScan23Chunk0023

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_142088 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 8]
def baseStart_142088 : Nat := 118140960795 + 142088 * 2 ^ 59
def prefixEnd_142088 : Nat := 4983230072969 + 3 ^ 40 * 142088 * 2
def baseEnd_142088 : Nat := 8106604359571701527395

theorem tailTrace_142088 : CollatzResearch.WordTrace tailWord_142088 prefixEnd_142088 8106604359571701527395 := by
  unfold tailWord_142088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591187554623458771769459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3454916739497945029025945 2591187554623458771769459)
  ·
    refine ⟨3886781331935188157654189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2591187554623458771769459 3886781331935188157654189)
    ·
      refine ⟨1457542999475695559120321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3886781331935188157654189 1457542999475695559120321)
      ·
        refine ⟨1093157249606771669340241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1457542999475695559120321 1093157249606771669340241)
        ·
          refine ⟨819867937205078752005181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093157249606771669340241 819867937205078752005181)
          ·
            refine ⟨307450476451904532001943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 819867937205078752005181 307450476451904532001943)
            ·
              refine ⟨461175714677856798002915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307450476451904532001943 461175714677856798002915)
              ·
                refine ⟨691763572016785197004373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461175714677856798002915 691763572016785197004373)
                ·
                  refine ⟨8106604359571701527395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 691763572016785197004373 8106604359571701527395)
                  ·
                    rfl

theorem cell23_142088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 8].length) (baseStart_142088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142088 prefixEnd_142088 := by exact prefixLift 142088
  have htrace : WordTrace (prefixWord ++ tailWord_142088) baseStart_142088 baseEnd_142088 := by
    simpa [prefixWord, tailWord_142088, baseEnd_142088] using wordTrace_append hprefix tailTrace_142088
  have hstable : (prefixWord ++ tailWord_142088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142088).length < 2 ^ (prefixWord ++ tailWord_142088).sum := by decide
  have hdescent : baseEnd_142088 < baseStart_142088 := by decide
  rcases family_descends (prefixWord ++ tailWord_142088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142126 : List Nat := [4, 1, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_142126 : Nat := 118140960795 + 142126 * 2 ^ 59
def prefixEnd_142126 : Nat := 4983230072969 + 3 ^ 40 * 142126 * 2
def baseEnd_142126 : Nat := 24326317167005388357127

theorem tailTrace_142126 : CollatzResearch.WordTrace tailWord_142126 prefixEnd_142126 24326317167005388357127 := by
  unfold tailWord_142126
  simp only [CollatzResearch.WordTrace]
  refine ⟨647970135388656254177779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3455840722072833355614821 647970135388656254177779)
  ·
    refine ⟨971955203082984381266669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 647970135388656254177779 971955203082984381266669)
    ·
      refine ⟨364483201156119142975001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 971955203082984381266669 364483201156119142975001)
      ·
        refine ⟨273362400867089357231251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364483201156119142975001 273362400867089357231251)
        ·
          refine ⟨410043601300634035846877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273362400867089357231251 410043601300634035846877)
          ·
            refine ⟨153766350487737763442579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410043601300634035846877 153766350487737763442579)
            ·
              refine ⟨230649525731606645163869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153766350487737763442579 230649525731606645163869)
              ·
                refine ⟨86493572149352491936451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230649525731606645163869 86493572149352491936451)
                ·
                  refine ⟨129740358224028737904677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86493572149352491936451 129740358224028737904677)
                  ·
                    refine ⟨24326317167005388357127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129740358224028737904677 24326317167005388357127)
                    ·
                      rfl

theorem cell23_142126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_142126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142126 prefixEnd_142126 := by exact prefixLift 142126
  have htrace : WordTrace (prefixWord ++ tailWord_142126) baseStart_142126 baseEnd_142126 := by
    simpa [prefixWord, tailWord_142126, baseEnd_142126] using wordTrace_append hprefix tailTrace_142126
  have hstable : (prefixWord ++ tailWord_142126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142126).length < 2 ^ (prefixWord ++ tailWord_142126).sum := by decide
  have hdescent : baseEnd_142126 < baseStart_142126 := by decide
  rcases family_descends (prefixWord ++ tailWord_142126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142168 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_142168 : Nat := 118140960795 + 142168 * 2 ^ 59
def prefixEnd_142168 : Nat := 4983230072969 + 3 ^ 40 * 142168 * 2
def baseEnd_142168 : Nat := 73000517688505000746187

theorem tailTrace_142168 : CollatzResearch.WordTrace tailWord_142168 prefixEnd_142168 73000517688505000746187 := by
  unfold tailWord_142168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592646474478545603225579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3456861965971394137634105 2592646474478545603225579)
  ·
    refine ⟨3888969711717818404838369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2592646474478545603225579 3888969711717818404838369)
    ·
      refine ⟨2916727283788363803628777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3888969711717818404838369 2916727283788363803628777)
      ·
        refine ⟨2187545462841272852721583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2916727283788363803628777 2187545462841272852721583)
        ·
          refine ⟨3281318194261909279082375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187545462841272852721583 3281318194261909279082375)
          ·
            refine ⟨4921977291392863918623563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281318194261909279082375 4921977291392863918623563)
            ·
              refine ⟨7382965937089295877935345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921977291392863918623563 7382965937089295877935345)
              ·
                refine ⟨5537224452816971908451509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7382965937089295877935345 5537224452816971908451509)
                ·
                  refine ⟨519114792451591116417329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5537224452816971908451509 519114792451591116417329)
                  ·
                    refine ⟨389336094338693337312997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 519114792451591116417329 389336094338693337312997)
                    ·
                      refine ⟨73000517688505000746187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 389336094338693337312997 73000517688505000746187)
                      ·
                        rfl

theorem cell23_142168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_142168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142168 prefixEnd_142168 := by exact prefixLift 142168
  have htrace : WordTrace (prefixWord ++ tailWord_142168) baseStart_142168 baseEnd_142168 := by
    simpa [prefixWord, tailWord_142168, baseEnd_142168] using wordTrace_append hprefix tailTrace_142168
  have hstable : (prefixWord ++ tailWord_142168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142168).length < 2 ^ (prefixWord ++ tailWord_142168).sum := by decide
  have hdescent : baseEnd_142168 < baseStart_142168 := by decide
  rcases family_descends (prefixWord ++ tailWord_142168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142172 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_142172 : Nat := 118140960795 + 142172 * 2 ^ 59
def prefixEnd_142172 : Nat := 4983230072969 + 3 ^ 40 * 142172 * 2
def baseEnd_142172 : Nat := 73002571611122985096169

theorem tailTrace_142172 : CollatzResearch.WordTrace tailWord_142172 prefixEnd_142172 73002571611122985096169 := by
  unfold tailWord_142172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592719420471299944798385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3456959227295066593064513 2592719420471299944798385)
  ·
    refine ⟨1944539565353474958598789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2592719420471299944798385 1944539565353474958598789)
    ·
      refine ⟨364601168503776554737273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1944539565353474958598789 364601168503776554737273)
      ·
        refine ⟨273450876377832416052955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364601168503776554737273 273450876377832416052955)
        ·
          refine ⟨410176314566748624079433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273450876377832416052955 410176314566748624079433)
          ·
            refine ⟨307632235925061468059575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410176314566748624079433 307632235925061468059575)
            ·
              refine ⟨461448353887592202089363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307632235925061468059575 461448353887592202089363)
              ·
                refine ⟨692172530831388303134045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461448353887592202089363 692172530831388303134045)
                ·
                  refine ⟨259564699061770613675267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692172530831388303134045 259564699061770613675267)
                  ·
                    refine ⟨389347048592655920512901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 259564699061770613675267 389347048592655920512901)
                    ·
                      refine ⟨73002571611122985096169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 389347048592655920512901 73002571611122985096169)
                      ·
                        rfl

theorem cell23_142172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_142172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142172 prefixEnd_142172 := by exact prefixLift 142172
  have htrace : WordTrace (prefixWord ++ tailWord_142172) baseStart_142172 baseEnd_142172 := by
    simpa [prefixWord, tailWord_142172, baseEnd_142172] using wordTrace_append hprefix tailTrace_142172
  have hstable : (prefixWord ++ tailWord_142172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142172).length < 2 ^ (prefixWord ++ tailWord_142172).sum := by decide
  have hdescent : baseEnd_142172 < baseStart_142172 := by decide
  rcases family_descends (prefixWord ++ tailWord_142172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142175 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 3]
def baseStart_142175 : Nat := 118140960795 + 142175 * 2 ^ 59
def prefixEnd_142175 : Nat := 4983230072969 + 3 ^ 40 * 142175 * 2
def baseEnd_142175 : Nat := 73004112053086473358655

theorem tailTrace_142175 : CollatzResearch.WordTrace tailWord_142175 prefixEnd_142175 73004112053086473358655 := by
  unfold tailWord_142175
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185548259931731401955979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3457032173287820934637319 5185548259931731401955979)
  ·
    refine ⟨7778322389897597102933969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5185548259931731401955979 7778322389897597102933969)
    ·
      refine ⟨5833741792423197827200477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7778322389897597102933969 5833741792423197827200477)
      ·
        refine ⟨2187653172158699185200179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5833741792423197827200477 2187653172158699185200179)
        ·
          refine ⟨3281479758238048777800269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187653172158699185200179 3281479758238048777800269)
          ·
            refine ⟨1230554909339268291675101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3281479758238048777800269 1230554909339268291675101)
            ·
              refine ⟨461458091002225609378163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230554909339268291675101 461458091002225609378163)
              ·
                refine ⟨692187136503338414067245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461458091002225609378163 692187136503338414067245)
                ·
                  refine ⟨259570176188751905275217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692187136503338414067245 259570176188751905275217)
                  ·
                    refine ⟨194677632141563928956413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 259570176188751905275217 194677632141563928956413)
                    ·
                      refine ⟨73004112053086473358655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 194677632141563928956413 73004112053086473358655)
                      ·
                        rfl

theorem cell23_142175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_142175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142175 prefixEnd_142175 := by exact prefixLift 142175
  have htrace : WordTrace (prefixWord ++ tailWord_142175) baseStart_142175 baseEnd_142175 := by
    simpa [prefixWord, tailWord_142175, baseEnd_142175] using wordTrace_append hprefix tailTrace_142175
  have hstable : (prefixWord ++ tailWord_142175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142175).length < 2 ^ (prefixWord ++ tailWord_142175).sum := by decide
  have hdescent : baseEnd_142175 < baseStart_142175 := by decide
  rcases family_descends (prefixWord ++ tailWord_142175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142279 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_142279 : Nat := 118140960795 + 142279 * 2 ^ 59
def prefixEnd_142279 : Nat := 4983230072969 + 3 ^ 40 * 142279 * 2
def baseEnd_142279 : Nat := 73057514041154066458177

theorem tailTrace_142279 : CollatzResearch.WordTrace tailWord_142279 prefixEnd_142279 73057514041154066458177 := by
  unfold tailWord_142279
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189341451554957163741891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3459560967703304775827927 5189341451554957163741891)
  ·
    refine ⟨7784012177332435745612837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5189341451554957163741891 7784012177332435745612837)
    ·
      refine ⟨1459502283249831702302407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7784012177332435745612837 1459502283249831702302407)
      ·
        refine ⟨2189253424874747553453611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459502283249831702302407 2189253424874747553453611)
        ·
          refine ⟨3283880137312121330180417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189253424874747553453611 3283880137312121330180417)
          ·
            refine ⟨2462910102984090997635313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3283880137312121330180417 2462910102984090997635313)
            ·
              refine ⟨1847182577238068248226485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462910102984090997635313 1847182577238068248226485)
              ·
                refine ⟨173173366616068898271233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1847182577238068248226485 173173366616068898271233)
                ·
                  refine ⟨129880024962051673703425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173173366616068898271233 129880024962051673703425)
                  ·
                    refine ⟨97410018721538755277569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129880024962051673703425 97410018721538755277569)
                    ·
                      refine ⟨73057514041154066458177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97410018721538755277569 73057514041154066458177)
                      ·
                        rfl

theorem cell23_142279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_142279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142279 prefixEnd_142279 := by exact prefixLift 142279
  have htrace : WordTrace (prefixWord ++ tailWord_142279) baseStart_142279 baseEnd_142279 := by
    simpa [prefixWord, tailWord_142279, baseEnd_142279] using wordTrace_append hprefix tailTrace_142279
  have hstable : (prefixWord ++ tailWord_142279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142279).length < 2 ^ (prefixWord ++ tailWord_142279).sum := by decide
  have hdescent : baseEnd_142279 < baseStart_142279 := by decide
  rcases family_descends (prefixWord ++ tailWord_142279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142295 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_142295 : Nat := 118140960795 + 142295 * 2 ^ 59
def prefixEnd_142295 : Nat := 4983230072969 + 3 ^ 40 * 142295 * 2
def baseEnd_142295 : Nat := 73065729731626003858103

theorem tailTrace_142295 : CollatzResearch.WordTrace tailWord_142295 prefixEnd_142295 73065729731626003858103 := by
  unfold tailWord_142295
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189925019496991896324339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3459950012997994597549559 5189925019496991896324339)
  ·
    refine ⟨7784887529245487844486509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5189925019496991896324339 7784887529245487844486509)
    ·
      refine ⟨2919332823467057941682441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7784887529245487844486509 2919332823467057941682441)
      ·
        refine ⟨2189499617600293456261831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2919332823467057941682441 2189499617600293456261831)
        ·
          refine ⟨3284249426400440184392747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189499617600293456261831 3284249426400440184392747)
          ·
            refine ⟨4926374139600660276589121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284249426400440184392747 4926374139600660276589121)
            ·
              refine ⟨3694780604700495207441841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4926374139600660276589121 3694780604700495207441841)
              ·
                refine ⟨2771085453525371405581381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694780604700495207441841 2771085453525371405581381)
                ·
                  refine ⟨519578522536007138546509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2771085453525371405581381 519578522536007138546509)
                  ·
                    refine ⟨194841945951002676954941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519578522536007138546509 194841945951002676954941)
                    ·
                      refine ⟨73065729731626003858103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 194841945951002676954941 73065729731626003858103)
                      ·
                        rfl

theorem cell23_142295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_142295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142295 prefixEnd_142295 := by exact prefixLift 142295
  have htrace : WordTrace (prefixWord ++ tailWord_142295) baseStart_142295 baseEnd_142295 := by
    simpa [prefixWord, tailWord_142295, baseEnd_142295] using wordTrace_append hprefix tailTrace_142295
  have hstable : (prefixWord ++ tailWord_142295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142295).length < 2 ^ (prefixWord ++ tailWord_142295).sum := by decide
  have hdescent : baseEnd_142295 < baseStart_142295 := by decide
  rcases family_descends (prefixWord ++ tailWord_142295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142319 : List Nat := [1, 1, 2, 1, 4, 4, 3, 2, 5]
def baseStart_142319 : Nat := 118140960795 + 142319 * 2 ^ 59
def prefixEnd_142319 : Nat := 4983230072969 + 3 ^ 40 * 142319 * 2
def baseEnd_142319 : Nat := 8119783696370434439777

theorem tailTrace_142319 : CollatzResearch.WordTrace tailWord_142319 prefixEnd_142319 8119783696370434439777 := by
  unfold tailWord_142319
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190800371410043995198011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3460533580940029330132007 5190800371410043995198011)
  ·
    refine ⟨7786200557115065992797017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5190800371410043995198011 7786200557115065992797017)
    ·
      refine ⟨5839650417836299494597763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7786200557115065992797017 5839650417836299494597763)
      ·
        refine ⟨8759475626754449241896645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5839650417836299494597763 8759475626754449241896645)
        ·
          refine ⟨1642401680016459232855621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8759475626754449241896645 1642401680016459232855621)
          ·
            refine ⟨307950315003086106160429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1642401680016459232855621 307950315003086106160429)
            ·
              refine ⟨115481368126157289810161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307950315003086106160429 115481368126157289810161)
              ·
                refine ⟨86611026094617967357621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115481368126157289810161 86611026094617967357621)
                ·
                  refine ⟨8119783696370434439777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86611026094617967357621 8119783696370434439777)
                  ·
                    rfl

theorem cell23_142319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 5].length) (baseStart_142319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142319 prefixEnd_142319 := by exact prefixLift 142319
  have htrace : WordTrace (prefixWord ++ tailWord_142319) baseStart_142319 baseEnd_142319 := by
    simpa [prefixWord, tailWord_142319, baseEnd_142319] using wordTrace_append hprefix tailTrace_142319
  have hstable : (prefixWord ++ tailWord_142319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142319).length < 2 ^ (prefixWord ++ tailWord_142319).sum := by decide
  have hdescent : baseEnd_142319 < baseStart_142319 := by decide
  rcases family_descends (prefixWord ++ tailWord_142319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142324 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_142324 : Nat := 118140960795 + 142324 * 2 ^ 59
def prefixEnd_142324 : Nat := 4983230072969 + 3 ^ 40 * 142324 * 2
def baseEnd_142324 : Nat := 73080620670606390395471

theorem tailTrace_142324 : CollatzResearch.WordTrace tailWord_142324 prefixEnd_142324 73080620670606390395471 := by
  unfold tailWord_142324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2595491368195964924565013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3460655157594619899420017 2595491368195964924565013)
  ·
    refine ⟨121663657884185855838985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2595491368195964924565013 121663657884185855838985)
    ·
      refine ⟨91247743413139391879239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121663657884185855838985 91247743413139391879239)
      ·
        refine ⟨136871615119709087818859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91247743413139391879239 136871615119709087818859)
        ·
          refine ⟨205307422679563631728289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136871615119709087818859 205307422679563631728289)
          ·
            refine ⟨153980567009672723796217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205307422679563631728289 153980567009672723796217)
            ·
              refine ⟨115485425257254542847163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153980567009672723796217 115485425257254542847163)
              ·
                refine ⟨173228137885881814270745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115485425257254542847163 173228137885881814270745)
                ·
                  refine ⟨129921103414411360703059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173228137885881814270745 129921103414411360703059)
                  ·
                    refine ⟨194881655121617041054589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129921103414411360703059 194881655121617041054589)
                    ·
                      refine ⟨73080620670606390395471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 194881655121617041054589 73080620670606390395471)
                      ·
                        rfl

theorem cell23_142324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_142324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142324 prefixEnd_142324 := by exact prefixLift 142324
  have htrace : WordTrace (prefixWord ++ tailWord_142324) baseStart_142324 baseEnd_142324 := by
    simpa [prefixWord, tailWord_142324, baseEnd_142324] using wordTrace_append hprefix tailTrace_142324
  have hstable : (prefixWord ++ tailWord_142324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142324).length < 2 ^ (prefixWord ++ tailWord_142324).sum := by decide
  have hdescent : baseEnd_142324 < baseStart_142324 := by decide
  rcases family_descends (prefixWord ++ tailWord_142324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142379 : List Nat := [1, 1, 1, 1, 2, 1, 7, 4, 1, 4]
def baseStart_142379 : Nat := 118140960795 + 142379 * 2 ^ 59
def prefixEnd_142379 : Nat := 4983230072969 + 3 ^ 40 * 142379 * 2
def baseEnd_142379 : Nat := 24369620702201225069239

theorem tailTrace_142379 : CollatzResearch.WordTrace tailWord_142379 prefixEnd_142379 24369620702201225069239 := by
  unfold tailWord_142379
  simp only [CollatzResearch.WordTrace]
  refine ⟨5192988751192674242382191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3461992500795116161588127 5192988751192674242382191)
  ·
    refine ⟨7789483126789011363573287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5192988751192674242382191 7789483126789011363573287)
    ·
      refine ⟨11684224690183517045359931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7789483126789011363573287 11684224690183517045359931)
      ·
        refine ⟨17526337035275275568039897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11684224690183517045359931 17526337035275275568039897)
        ·
          refine ⟨13144752776456456676029923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17526337035275275568039897 13144752776456456676029923)
          ·
            refine ⟨19717129164684685014044885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13144752776456456676029923 19717129164684685014044885)
            ·
              refine ⟨462120214797297305016677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19717129164684685014044885 462120214797297305016677)
              ·
                refine ⟨86647540274493244690627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462120214797297305016677 86647540274493244690627)
                ·
                  refine ⟨129971310411739867035941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86647540274493244690627 129971310411739867035941)
                  ·
                    refine ⟨24369620702201225069239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129971310411739867035941 24369620702201225069239)
                    ·
                      rfl

theorem cell23_142379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 4].length) (baseStart_142379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142379 prefixEnd_142379 := by exact prefixLift 142379
  have htrace : WordTrace (prefixWord ++ tailWord_142379) baseStart_142379 baseEnd_142379 := by
    simpa [prefixWord, tailWord_142379, baseEnd_142379] using wordTrace_append hprefix tailTrace_142379
  have hstable : (prefixWord ++ tailWord_142379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142379).length < 2 ^ (prefixWord ++ tailWord_142379).sum := by decide
  have hdescent : baseEnd_142379 < baseStart_142379 := by decide
  rcases family_descends (prefixWord ++ tailWord_142379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142392 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 6]
def baseStart_142392 : Nat := 118140960795 + 142392 * 2 ^ 59
def prefixEnd_142392 : Nat := 4983230072969 + 3 ^ 40 * 142392 * 2
def baseEnd_142392 : Nat := 8123948595012458260573

theorem tailTrace_142392 : CollatzResearch.WordTrace tailWord_142392 prefixEnd_142392 8123948595012458260573 := by
  unfold tailWord_142392
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596731450072788731302715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3462308600097051641736953 2596731450072788731302715)
  ·
    refine ⟨3895097175109183096954073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2596731450072788731302715 3895097175109183096954073)
    ·
      refine ⟨2921322881331887322715555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3895097175109183096954073 2921322881331887322715555)
      ·
        refine ⟨4381984321997830984073333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921322881331887322715555 4381984321997830984073333)
        ·
          refine ⟨410811030187296654756875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4381984321997830984073333 410811030187296654756875)
          ·
            refine ⟨616216545280944982135313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410811030187296654756875 616216545280944982135313)
            ·
              refine ⟨462162408960708736601485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616216545280944982135313 462162408960708736601485)
              ·
                refine ⟨173310903360265776225557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462162408960708736601485 173310903360265776225557)
                ·
                  refine ⟨8123948595012458260573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 173310903360265776225557 8123948595012458260573)
                  ·
                    rfl

theorem cell23_142392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 6].length) (baseStart_142392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142392 prefixEnd_142392 := by exact prefixLift 142392
  have htrace : WordTrace (prefixWord ++ tailWord_142392) baseStart_142392 baseEnd_142392 := by
    simpa [prefixWord, tailWord_142392, baseEnd_142392] using wordTrace_append hprefix tailTrace_142392
  have hstable : (prefixWord ++ tailWord_142392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142392).length < 2 ^ (prefixWord ++ tailWord_142392).sum := by decide
  have hdescent : baseEnd_142392 < baseStart_142392 := by decide
  rcases family_descends (prefixWord ++ tailWord_142392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142406 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_142406 : Nat := 118140960795 + 142406 * 2 ^ 59
def prefixEnd_142406 : Nat := 4983230072969 + 3 ^ 40 * 142406 * 2
def baseEnd_142406 : Nat := 73122726084275069570093

theorem tailTrace_142406 : CollatzResearch.WordTrace tailWord_142406 prefixEnd_142406 73122726084275069570093 := by
  unfold tailWord_142406
  simp only [CollatzResearch.WordTrace]
  refine ⟨162311672565464307925471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3462649014729905235743381 162311672565464307925471)
  ·
    refine ⟨243467508848196461888207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162311672565464307925471 243467508848196461888207)
    ·
      refine ⟨365201263272294692832311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243467508848196461888207 365201263272294692832311)
      ·
        refine ⟨547801894908442039248467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365201263272294692832311 547801894908442039248467)
        ·
          refine ⟨821702842362663058872701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547801894908442039248467 821702842362663058872701)
          ·
            refine ⟨308138565885998647077263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 821702842362663058872701 308138565885998647077263)
            ·
              refine ⟨462207848828997970615895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308138565885998647077263 462207848828997970615895)
              ·
                refine ⟨693311773243496955923843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462207848828997970615895 693311773243496955923843)
                ·
                  refine ⟨1039967659865245433885765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693311773243496955923843 1039967659865245433885765)
                  ·
                    refine ⟨194993936224733518853581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039967659865245433885765 194993936224733518853581)
                    ·
                      refine ⟨73122726084275069570093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 194993936224733518853581 73122726084275069570093)
                      ·
                        rfl

theorem cell23_142406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_142406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142406 prefixEnd_142406 := by exact prefixLift 142406
  have htrace : WordTrace (prefixWord ++ tailWord_142406) baseStart_142406 baseEnd_142406 := by
    simpa [prefixWord, tailWord_142406, baseEnd_142406] using wordTrace_append hprefix tailTrace_142406
  have hstable : (prefixWord ++ tailWord_142406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142406).length < 2 ^ (prefixWord ++ tailWord_142406).sum := by decide
  have hdescent : baseEnd_142406 < baseStart_142406 := by decide
  rcases family_descends (prefixWord ++ tailWord_142406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142413 : List Nat := [1, 6, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_142413 : Nat := 118140960795 + 142413 * 2 ^ 59
def prefixEnd_142413 : Nat := 4983230072969 + 3 ^ 40 * 142413 * 2
def baseEnd_142413 : Nat := 24375440149618847394187

theorem tailTrace_142413 : CollatzResearch.WordTrace tailWord_142413 prefixEnd_142413 24375440149618847394187 := by
  unfold tailWord_142413
  simp only [CollatzResearch.WordTrace]
  refine ⟨5194228833069498049119893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3462819222046332032746595 5194228833069498049119893)
  ·
    refine ⟨243479476550132721052495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5194228833069498049119893 243479476550132721052495)
    ·
      refine ⟨365219214825199081578743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243479476550132721052495 365219214825199081578743)
      ·
        refine ⟨547828822237798622368115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365219214825199081578743 547828822237798622368115)
        ·
          refine ⟨821743233356697933552173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547828822237798622368115 821743233356697933552173)
          ·
            refine ⟨308153712508761725082065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 821743233356697933552173 308153712508761725082065)
            ·
              refine ⟨231115284381571293811549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308153712508761725082065 231115284381571293811549)
              ·
                refine ⟨86668231643089235179331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231115284381571293811549 86668231643089235179331)
                ·
                  refine ⟨130002347464633852768997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86668231643089235179331 130002347464633852768997)
                  ·
                    refine ⟨24375440149618847394187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130002347464633852768997 24375440149618847394187)
                    ·
                      rfl

theorem cell23_142413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_142413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142413 prefixEnd_142413 := by exact prefixLift 142413
  have htrace : WordTrace (prefixWord ++ tailWord_142413) baseStart_142413 baseEnd_142413 := by
    simpa [prefixWord, tailWord_142413, baseEnd_142413] using wordTrace_append hprefix tailTrace_142413
  have hstable : (prefixWord ++ tailWord_142413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142413).length < 2 ^ (prefixWord ++ tailWord_142413).sum := by decide
  have hdescent : baseEnd_142413 < baseStart_142413 := by decide
  rcases family_descends (prefixWord ++ tailWord_142413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142430 : List Nat := [4, 4, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_142430 : Nat := 118140960795 + 142430 * 2 ^ 59
def prefixEnd_142430 : Nat := 4983230072969 + 3 ^ 40 * 142430 * 2
def baseEnd_142430 : Nat := 24378349873327658556661

theorem tailTrace_142430 : CollatzResearch.WordTrace tailWord_142430 prefixEnd_142430 24378349873327658556661 := by
  unfold tailWord_142430
  simp only [CollatzResearch.WordTrace]
  refine ⟨649356109250988744061093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3463232582671939968325829 649356109250988744061093)
  ·
    refine ⟨121754270484560389511455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 649356109250988744061093 121754270484560389511455)
    ·
      refine ⟨182631405726840584267183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121754270484560389511455 182631405726840584267183)
      ·
        refine ⟨273947108590260876400775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182631405726840584267183 273947108590260876400775)
        ·
          refine ⟨410920662885391314601163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273947108590260876400775 410920662885391314601163)
          ·
            refine ⟨616380994328086971901745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410920662885391314601163 616380994328086971901745)
            ·
              refine ⟨462285745746065228926309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616380994328086971901745 462285745746065228926309)
              ·
                refine ⟨86678577327387230423683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462285745746065228926309 86678577327387230423683)
                ·
                  refine ⟨130017865991080845635525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86678577327387230423683 130017865991080845635525)
                  ·
                    refine ⟨24378349873327658556661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130017865991080845635525 24378349873327658556661)
                    ·
                      rfl

theorem cell23_142430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_142430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142430 prefixEnd_142430 := by exact prefixLift 142430
  have htrace : WordTrace (prefixWord ++ tailWord_142430) baseStart_142430 baseEnd_142430 := by
    simpa [prefixWord, tailWord_142430, baseEnd_142430] using wordTrace_append hprefix tailTrace_142430
  have hstable : (prefixWord ++ tailWord_142430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142430).length < 2 ^ (prefixWord ++ tailWord_142430).sum := by decide
  have hdescent : baseEnd_142430 < baseStart_142430 := by decide
  rcases family_descends (prefixWord ++ tailWord_142430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142482 : List Nat := [3, 2, 3, 1, 1, 2, 11]
def baseStart_142482 : Nat := 118140960795 + 142482 * 2 ^ 59
def prefixEnd_142482 : Nat := 4983230072969 + 3 ^ 40 * 142482 * 2
def baseEnd_142482 : Nat := 903231489061935459503

theorem tailTrace_142482 : CollatzResearch.WordTrace tailWord_142482 prefixEnd_142482 903231489061935459503 := by
  unfold tailWord_142482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299186367454880708345425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3464496979879681888921133 1299186367454880708345425)
  ·
    refine ⟨974389775591160531259069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1299186367454880708345425 974389775591160531259069)
    ·
      refine ⟨365396165846685199222151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 974389775591160531259069 365396165846685199222151)
      ·
        refine ⟨548094248770027798833227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365396165846685199222151 548094248770027798833227)
        ·
          refine ⟨822141373155041698249841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548094248770027798833227 822141373155041698249841)
          ·
            refine ⟨616606029866281273687381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 822141373155041698249841 616606029866281273687381)
            ·
              refine ⟨903231489061935459503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 616606029866281273687381 903231489061935459503)
              ·
                rfl

theorem cell23_142482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 11].length) (baseStart_142482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142482 prefixEnd_142482 := by exact prefixLift 142482
  have htrace : WordTrace (prefixWord ++ tailWord_142482) baseStart_142482 baseEnd_142482 := by
    simpa [prefixWord, tailWord_142482, baseEnd_142482] using wordTrace_append hprefix tailTrace_142482
  have hstable : (prefixWord ++ tailWord_142482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142482).length < 2 ^ (prefixWord ++ tailWord_142482).sum := by decide
  have hdescent : baseEnd_142482 < baseStart_142482 := by decide
  rcases family_descends (prefixWord ++ tailWord_142482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142503 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 2, 4]
def baseStart_142503 : Nat := 118140960795 + 142503 * 2 ^ 59
def prefixEnd_142503 : Nat := 4983230072969 + 3 ^ 40 * 142503 * 2
def baseEnd_142503 : Nat := 24390844569253730019049

theorem tailTrace_142503 : CollatzResearch.WordTrace tailWord_142503 prefixEnd_142503 24390844569253730019049 := by
  unfold tailWord_142503
  simp only [CollatzResearch.WordTrace]
  refine ⟨5197511402743443419896163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3465007601828962279930775 5197511402743443419896163)
  ·
    refine ⟨7796267104115165129844245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5197511402743443419896163 7796267104115165129844245)
    ·
      refine ⟨365450020505398365461449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7796267104115165129844245 365450020505398365461449)
      ·
        refine ⟨274087515379048774096087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365450020505398365461449 274087515379048774096087)
        ·
          refine ⟨411131273068573161144131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274087515379048774096087 411131273068573161144131)
          ·
            refine ⟨616696909602859741716197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411131273068573161144131 616696909602859741716197)
            ·
              refine ⟨115630670550536201571787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 616696909602859741716197 115630670550536201571787)
              ·
                refine ⟨173446005825804302357681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115630670550536201571787 173446005825804302357681)
                ·
                  refine ⟨130084504369353226768261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173446005825804302357681 130084504369353226768261)
                  ·
                    refine ⟨24390844569253730019049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130084504369353226768261 24390844569253730019049)
                    ·
                      rfl

theorem cell23_142503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_142503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142503 prefixEnd_142503 := by exact prefixLift 142503
  have htrace : WordTrace (prefixWord ++ tailWord_142503) baseStart_142503 baseEnd_142503 := by
    simpa [prefixWord, tailWord_142503, baseEnd_142503] using wordTrace_append hprefix tailTrace_142503
  have hstable : (prefixWord ++ tailWord_142503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142503).length < 2 ^ (prefixWord ++ tailWord_142503).sum := by decide
  have hdescent : baseEnd_142503 < baseStart_142503 := by decide
  rcases family_descends (prefixWord ++ tailWord_142503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142513 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_142513 : Nat := 118140960795 + 142513 * 2 ^ 59
def prefixEnd_142513 : Nat := 4983230072969 + 3 ^ 40 * 142513 * 2
def baseEnd_142513 : Nat := 73177668514306150932101

theorem tailTrace_142513 : CollatzResearch.WordTrace tailWord_142513 prefixEnd_142513 73177668514306150932101 := by
  unfold tailWord_142513
  simp only [CollatzResearch.WordTrace]
  refine ⟨5197876132707215127760193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3465250755138143418506795 5197876132707215127760193)
  ·
    refine ⟨3898407099530411345820145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5197876132707215127760193 3898407099530411345820145)
    ·
      refine ⟨2923805324647808509365109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3898407099530411345820145 2923805324647808509365109)
      ·
        refine ⟨274106749185732047752979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2923805324647808509365109 274106749185732047752979)
        ·
          refine ⟨411160123778598071629469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274106749185732047752979 411160123778598071629469)
          ·
            refine ⟨154185046416974276861051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 411160123778598071629469 154185046416974276861051)
            ·
              refine ⟨231277569625461415291577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154185046416974276861051 231277569625461415291577)
              ·
                refine ⟨173458177219096061468683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231277569625461415291577 173458177219096061468683)
                ·
                  refine ⟨260187265828644092203025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173458177219096061468683 260187265828644092203025)
                  ·
                    refine ⟨195140449371483069152269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 260187265828644092203025 195140449371483069152269)
                    ·
                      refine ⟨73177668514306150932101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195140449371483069152269 73177668514306150932101)
                      ·
                        rfl

theorem cell23_142513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_142513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142513 prefixEnd_142513 := by exact prefixLift 142513
  have htrace : WordTrace (prefixWord ++ tailWord_142513) baseStart_142513 baseEnd_142513 := by
    simpa [prefixWord, tailWord_142513, baseEnd_142513] using wordTrace_append hprefix tailTrace_142513
  have hstable : (prefixWord ++ tailWord_142513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142513).length < 2 ^ (prefixWord ++ tailWord_142513).sum := by decide
  have hdescent : baseEnd_142513 < baseStart_142513 := by decide
  rcases family_descends (prefixWord ++ tailWord_142513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142526 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_142526 : Nat := 118140960795 + 142526 * 2 ^ 59
def prefixEnd_142526 : Nat := 4983230072969 + 3 ^ 40 * 142526 * 2
def baseEnd_142526 : Nat := 73184343762814600069541

theorem tailTrace_142526 : CollatzResearch.WordTrace tailWord_142526 prefixEnd_142526 73184343762814600069541 := by
  unfold tailWord_142526
  simp only [CollatzResearch.WordTrace]
  refine ⟨649793785207514793497929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3465566854440078898655621 649793785207514793497929)
  ·
    refine ⟨487345338905636095123447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 649793785207514793497929 487345338905636095123447)
    ·
      refine ⟨731018008358454142685171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487345338905636095123447 731018008358454142685171)
      ·
        refine ⟨1096527012537681214027757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731018008358454142685171 1096527012537681214027757)
        ·
          refine ⟨411197629701630455260409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1096527012537681214027757 411197629701630455260409)
          ·
            refine ⟨308398222276222841445307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411197629701630455260409 308398222276222841445307)
            ·
              refine ⟨462597333414334262167961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308398222276222841445307 462597333414334262167961)
              ·
                refine ⟨346948000060750696625971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462597333414334262167961 346948000060750696625971)
                ·
                  refine ⟨520422000091126044938957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346948000060750696625971 520422000091126044938957)
                  ·
                    refine ⟨195158250034172266852109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 520422000091126044938957 195158250034172266852109)
                    ·
                      refine ⟨73184343762814600069541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195158250034172266852109 73184343762814600069541)
                      ·
                        rfl

theorem cell23_142526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_142526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142526 prefixEnd_142526 := by exact prefixLift 142526
  have htrace : WordTrace (prefixWord ++ tailWord_142526) baseStart_142526 baseEnd_142526 := by
    simpa [prefixWord, tailWord_142526, baseEnd_142526] using wordTrace_append hprefix tailTrace_142526
  have hstable : (prefixWord ++ tailWord_142526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142526).length < 2 ^ (prefixWord ++ tailWord_142526).sum := by decide
  have hdescent : baseEnd_142526 < baseStart_142526 := by decide
  rcases family_descends (prefixWord ++ tailWord_142526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142530 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_142530 : Nat := 118140960795 + 142530 * 2 ^ 59
def prefixEnd_142530 : Nat := 4983230072969 + 3 ^ 40 * 142530 * 2
def baseEnd_142530 : Nat := 73186397685432584419523

theorem tailTrace_142530 : CollatzResearch.WordTrace tailWord_142530 prefixEnd_142530 73186397685432584419523 := by
  unfold tailWord_142530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299624043411406757782261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3465664115763751354086029 1299624043411406757782261)
  ·
    refine ⟨121839754069819383542087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1299624043411406757782261 121839754069819383542087)
    ·
      refine ⟨182759631104729075313131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121839754069819383542087 182759631104729075313131)
      ·
        refine ⟨274139446657093612969697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182759631104729075313131 274139446657093612969697)
        ·
          refine ⟨205604584992820209727273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274139446657093612969697 205604584992820209727273)
          ·
            refine ⟨154203438744615157295455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205604584992820209727273 154203438744615157295455)
            ·
              refine ⟨231305158116922735943183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154203438744615157295455 231305158116922735943183)
              ·
                refine ⟨346957737175384103914775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231305158116922735943183 346957737175384103914775)
                ·
                  refine ⟨520436605763076155872163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346957737175384103914775 520436605763076155872163)
                  ·
                    refine ⟨780654908644614233808245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 520436605763076155872163 780654908644614233808245)
                    ·
                      refine ⟨73186397685432584419523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 780654908644614233808245 73186397685432584419523)
                      ·
                        rfl

theorem cell23_142530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_142530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142530 prefixEnd_142530 := by exact prefixLift 142530
  have htrace : WordTrace (prefixWord ++ tailWord_142530) baseStart_142530 baseEnd_142530 := by
    simpa [prefixWord, tailWord_142530, baseEnd_142530] using wordTrace_append hprefix tailTrace_142530
  have hstable : (prefixWord ++ tailWord_142530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142530).length < 2 ^ (prefixWord ++ tailWord_142530).sum := by decide
  have hdescent : baseEnd_142530 < baseStart_142530 := by decide
  rcases family_descends (prefixWord ++ tailWord_142530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142536 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_142536 : Nat := 118140960795 + 142536 * 2 ^ 59
def prefixEnd_142536 : Nat := 4983230072969 + 3 ^ 40 * 142536 * 2
def baseEnd_142536 : Nat := 73189478569359560944495

theorem tailTrace_142536 : CollatzResearch.WordTrace tailWord_142536 prefixEnd_142536 73189478569359560944495 := by
  unfold tailWord_142536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2599357505811945027923731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3465810007749260037231641 2599357505811945027923731)
  ·
    refine ⟨3899036258717917541885597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2599357505811945027923731 3899036258717917541885597)
    ·
      refine ⟨1462138597019219078207099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3899036258717917541885597 1462138597019219078207099)
      ·
        refine ⟨2193207895528828617310649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462138597019219078207099 2193207895528828617310649)
        ·
          refine ⟨1644905921646621462982987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193207895528828617310649 1644905921646621462982987)
          ·
            refine ⟨2467358882469932194474481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644905921646621462982987 2467358882469932194474481)
            ·
              refine ⟨1850519161852449145855861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467358882469932194474481 1850519161852449145855861)
              ·
                refine ⟨173486171423667107423987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1850519161852449145855861 173486171423667107423987)
                ·
                  refine ⟨260229257135500661135981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173486171423667107423987 260229257135500661135981)
                  ·
                    refine ⟨97585971425812747925993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260229257135500661135981 97585971425812747925993)
                    ·
                      refine ⟨73189478569359560944495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97585971425812747925993 73189478569359560944495)
                      ·
                        rfl

theorem cell23_142536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_142536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142536 prefixEnd_142536 := by exact prefixLift 142536
  have htrace : WordTrace (prefixWord ++ tailWord_142536) baseStart_142536 baseEnd_142536 := by
    simpa [prefixWord, tailWord_142536, baseEnd_142536] using wordTrace_append hprefix tailTrace_142536
  have hstable : (prefixWord ++ tailWord_142536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142536).length < 2 ^ (prefixWord ++ tailWord_142536).sum := by decide
  have hdescent : baseEnd_142536 < baseStart_142536 := by decide
  rcases family_descends (prefixWord ++ tailWord_142536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142549 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_142549 : Nat := 118140960795 + 142549 * 2 ^ 59
def prefixEnd_142549 : Nat := 4983230072969 + 3 ^ 40 * 142549 * 2
def baseEnd_142549 : Nat := 73196153817868010081935

theorem tailTrace_142549 : CollatzResearch.WordTrace tailWord_142549 prefixEnd_142549 73196153817868010081935 := by
  unfold tailWord_142549
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199189160576793276070701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3466126107051195517380467 5199189160576793276070701)
  ·
    refine ⟨1949695935216297478526513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5199189160576793276070701 1949695935216297478526513)
    ·
      refine ⟨1462271951412223108894885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1949695935216297478526513 1462271951412223108894885)
      ·
        refine ⟨274175990889791832917791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1462271951412223108894885 274175990889791832917791)
        ·
          refine ⟨411263986334687749376687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274175990889791832917791 411263986334687749376687)
          ·
            refine ⟨616895979502031624065031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411263986334687749376687 616895979502031624065031)
            ·
              refine ⟨925343969253047436097547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616895979502031624065031 925343969253047436097547)
              ·
                refine ⟨1388015953879571154146321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925343969253047436097547 1388015953879571154146321)
                ·
                  refine ⟨1041011965409678365609741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1388015953879571154146321 1041011965409678365609741)
                  ·
                    refine ⟨390379487028629387103653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1041011965409678365609741 390379487028629387103653)
                    ·
                      refine ⟨73196153817868010081935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 390379487028629387103653 73196153817868010081935)
                      ·
                        rfl

theorem cell23_142549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_142549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142549 prefixEnd_142549 := by exact prefixLift 142549
  have htrace : WordTrace (prefixWord ++ tailWord_142549) baseStart_142549 baseEnd_142549 := by
    simpa [prefixWord, tailWord_142549, baseEnd_142549] using wordTrace_append hprefix tailTrace_142549
  have hstable : (prefixWord ++ tailWord_142549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142549).length < 2 ^ (prefixWord ++ tailWord_142549).sum := by decide
  have hdescent : baseEnd_142549 < baseStart_142549 := by decide
  rcases family_descends (prefixWord ++ tailWord_142549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142572 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 9]
def baseStart_142572 : Nat := 118140960795 + 142572 * 2 ^ 59
def prefixEnd_142572 : Nat := 4983230072969 + 3 ^ 40 * 142572 * 2
def baseEnd_142572 : Nat := 8134218208102380010481

theorem tailTrace_142572 : CollatzResearch.WordTrace tailWord_142572 prefixEnd_142572 8134218208102380010481 := by
  unfold tailWord_142572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600014019746734102078985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3466685359662312136105313 2600014019746734102078985)
  ·
    refine ⟨1950010514810050576559239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2600014019746734102078985 1950010514810050576559239)
    ·
      refine ⟨2925015772215075864838859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1950010514810050576559239 2925015772215075864838859)
      ·
        refine ⟨4387523658322613797258289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2925015772215075864838859 4387523658322613797258289)
        ·
          refine ⟨3290642743741960347943717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4387523658322613797258289 3290642743741960347943717)
          ·
            refine ⟨616995514451617565239447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3290642743741960347943717 616995514451617565239447)
            ·
              refine ⟨925493271677426347859171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616995514451617565239447 925493271677426347859171)
              ·
                refine ⟨1388239907516139521788757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925493271677426347859171 1388239907516139521788757)
                ·
                  refine ⟨8134218208102380010481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1388239907516139521788757 8134218208102380010481)
                  ·
                    rfl

theorem cell23_142572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_142572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142572 prefixEnd_142572 := by exact prefixLift 142572
  have htrace : WordTrace (prefixWord ++ tailWord_142572) baseStart_142572 baseEnd_142572 := by
    simpa [prefixWord, tailWord_142572, baseEnd_142572] using wordTrace_append hprefix tailTrace_142572
  have hstable : (prefixWord ++ tailWord_142572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142572).length < 2 ^ (prefixWord ++ tailWord_142572).sum := by decide
  have hdescent : baseEnd_142572 < baseStart_142572 := by decide
  rcases family_descends (prefixWord ++ tailWord_142572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142606 : List Nat := [4, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_142606 : Nat := 118140960795 + 142606 * 2 ^ 59
def prefixEnd_142606 : Nat := 4983230072969 + 3 ^ 40 * 142606 * 2
def baseEnd_142606 : Nat := 8136158023908254118797

theorem tailTrace_142606 : CollatzResearch.WordTrace tailWord_142606 prefixEnd_142606 8136158023908254118797 := by
  unfold tailWord_142606
  simp only [CollatzResearch.WordTrace]
  refine ⟨650158515171286501361959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3467512080913528007263781 650158515171286501361959)
  ·
    refine ⟨975237772756929752042939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 650158515171286501361959 975237772756929752042939)
    ·
      refine ⟨1462856659135394628064409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975237772756929752042939 1462856659135394628064409)
      ·
        refine ⟨1097142494351545971048307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1462856659135394628064409 1097142494351545971048307)
        ·
          refine ⟨1645713741527318956572461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097142494351545971048307 1645713741527318956572461)
          ·
            refine ⟨617142653072744608714673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1645713741527318956572461 617142653072744608714673)
            ·
              refine ⟨462856989804558456536005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617142653072744608714673 462856989804558456536005)
              ·
                refine ⟨86785685588354710600501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462856989804558456536005 86785685588354710600501)
                ·
                  refine ⟨8136158023908254118797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86785685588354710600501 8136158023908254118797)
                  ·
                    rfl

theorem cell23_142606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_142606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142606 prefixEnd_142606 := by exact prefixLift 142606
  have htrace : WordTrace (prefixWord ++ tailWord_142606) baseStart_142606 baseEnd_142606 := by
    simpa [prefixWord, tailWord_142606, baseEnd_142606] using wordTrace_append hprefix tailTrace_142606
  have hstable : (prefixWord ++ tailWord_142606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142606).length < 2 ^ (prefixWord ++ tailWord_142606).sum := by decide
  have hdescent : baseEnd_142606 < baseStart_142606 := by decide
  rcases family_descends (prefixWord ++ tailWord_142606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142639 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_142639 : Nat := 118140960795 + 142639 * 2 ^ 59
def prefixEnd_142639 : Nat := 4983230072969 + 3 ^ 40 * 142639 * 2
def baseEnd_142639 : Nat := 73242367076772657956521

theorem tailTrace_142639 : CollatzResearch.WordTrace tailWord_142639 prefixEnd_142639 73242367076772657956521 := by
  unfold tailWord_142639
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202471730250738646846971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3468314486833825764564647 5202471730250738646846971)
  ·
    refine ⟨7803707595376107970270457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5202471730250738646846971 7803707595376107970270457)
    ·
      refine ⟨5852780696532080977702843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7803707595376107970270457 5852780696532080977702843)
      ·
        refine ⟨8779171044798121466554265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852780696532080977702843 8779171044798121466554265)
        ·
          refine ⟨6584378283598591099915699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8779171044798121466554265 6584378283598591099915699)
          ·
            refine ⟨9876567425397886649873549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6584378283598591099915699 9876567425397886649873549)
            ·
              refine ⟨3703712784524207493702581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9876567425397886649873549 3703712784524207493702581)
              ·
                refine ⟨347223073549144452534617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3703712784524207493702581 347223073549144452534617)
                ·
                  refine ⟨260417305161858339400963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347223073549144452534617 260417305161858339400963)
                  ·
                    refine ⟨390625957742787509101445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260417305161858339400963 390625957742787509101445)
                    ·
                      refine ⟨73242367076772657956521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 390625957742787509101445 73242367076772657956521)
                      ·
                        rfl

theorem cell23_142639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_142639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142639 prefixEnd_142639 := by exact prefixLift 142639
  have htrace : WordTrace (prefixWord ++ tailWord_142639) baseStart_142639 baseEnd_142639 := by
    simpa [prefixWord, tailWord_142639, baseEnd_142639] using wordTrace_append hprefix tailTrace_142639
  have hstable : (prefixWord ++ tailWord_142639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142639).length < 2 ^ (prefixWord ++ tailWord_142639).sum := by decide
  have hdescent : baseEnd_142639 < baseStart_142639 := by decide
  rcases family_descends (prefixWord ++ tailWord_142639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142653 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_142653 : Nat := 118140960795 + 142653 * 2 ^ 59
def prefixEnd_142653 : Nat := 4983230072969 + 3 ^ 40 * 142653 * 2
def baseEnd_142653 : Nat := 24416518601978534393819

theorem tailTrace_142653 : CollatzResearch.WordTrace tailWord_142653 prefixEnd_142653 24416518601978534393819 := by
  unfold tailWord_142653
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202982352200019037856613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3468654901466679358571075 5202982352200019037856613)
  ·
    refine ⟨975559191037503569598115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5202982352200019037856613 975559191037503569598115)
    ·
      refine ⟨1463338786556255354397173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975559191037503569598115 1463338786556255354397173)
      ·
        refine ⟨137188011239648939474735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1463338786556255354397173 137188011239648939474735)
        ·
          refine ⟨205782016859473409212103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137188011239648939474735 205782016859473409212103)
          ·
            refine ⟨308673025289210113818155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205782016859473409212103 308673025289210113818155)
            ·
              refine ⟨463009537933815170727233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308673025289210113818155 463009537933815170727233)
              ·
                refine ⟨347257153450361378045425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463009537933815170727233 347257153450361378045425)
                ·
                  refine ⟨260442865087771033534069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347257153450361378045425 260442865087771033534069)
                  ·
                    refine ⟨24416518601978534393819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 260442865087771033534069 24416518601978534393819)
                    ·
                      rfl

theorem cell23_142653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_142653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142653 prefixEnd_142653 := by exact prefixLift 142653
  have htrace : WordTrace (prefixWord ++ tailWord_142653) baseStart_142653 baseEnd_142653 := by
    simpa [prefixWord, tailWord_142653, baseEnd_142653] using wordTrace_append hprefix tailTrace_142653
  have hstable : (prefixWord ++ tailWord_142653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142653).length < 2 ^ (prefixWord ++ tailWord_142653).sum := by decide
  have hdescent : baseEnd_142653 < baseStart_142653 := by decide
  rcases family_descends (prefixWord ++ tailWord_142653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142676 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_142676 : Nat := 118140960795 + 142676 * 2 ^ 59
def prefixEnd_142676 : Nat := 4983230072969 + 3 ^ 40 * 142676 * 2
def baseEnd_142676 : Nat := 73261365860989013193851

theorem tailTrace_142676 : CollatzResearch.WordTrace tailWord_142676 prefixEnd_142676 73261365860989013193851 := by
  unfold tailWord_142676
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601910615558346982971941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3469214154077795977295921 2601910615558346982971941)
  ·
    refine ⟨487858240417190059307239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2601910615558346982971941 487858240417190059307239)
    ·
      refine ⟨731787360625785088960859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487858240417190059307239 731787360625785088960859)
      ·
        refine ⟨1097681040938677633441289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731787360625785088960859 1097681040938677633441289)
        ·
          refine ⟨823260780704008225080967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1097681040938677633441289 823260780704008225080967)
          ·
            refine ⟨1234891171056012337621451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823260780704008225080967 1234891171056012337621451)
            ·
              refine ⟨1852336756584018506432177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234891171056012337621451 1852336756584018506432177)
              ·
                refine ⟨1389252567438013879824133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1852336756584018506432177 1389252567438013879824133)
                ·
                  refine ⟨260484856394627602467025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1389252567438013879824133 260484856394627602467025)
                  ·
                    refine ⟨195363642295970701850269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 260484856394627602467025 195363642295970701850269)
                    ·
                      refine ⟨73261365860989013193851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195363642295970701850269 73261365860989013193851)
                      ·
                        rfl

theorem cell23_142676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_142676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142676 prefixEnd_142676 := by exact prefixLift 142676
  have htrace : WordTrace (prefixWord ++ tailWord_142676) baseStart_142676 baseEnd_142676 := by
    simpa [prefixWord, tailWord_142676, baseEnd_142676] using wordTrace_append hprefix tailTrace_142676
  have hstable : (prefixWord ++ tailWord_142676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142676).length < 2 ^ (prefixWord ++ tailWord_142676).sum := by decide
  have hdescent : baseEnd_142676 < baseStart_142676 := by decide
  rcases family_descends (prefixWord ++ tailWord_142676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142689 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_142689 : Nat := 118140960795 + 142689 * 2 ^ 59
def prefixEnd_142689 : Nat := 4983230072969 + 3 ^ 40 * 142689 * 2
def baseEnd_142689 : Nat := 73268041109497462331291

theorem tailTrace_142689 : CollatzResearch.WordTrace tailWord_142689 prefixEnd_142689 73268041109497462331291 := by
  unfold tailWord_142689
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204295380069597186167121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3469530253379731457444747 5204295380069597186167121)
  ·
    refine ⟨3903221535052197889625341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5204295380069597186167121 3903221535052197889625341)
    ·
      refine ⟨1463708075644574208609503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3903221535052197889625341 1463708075644574208609503)
      ·
        refine ⟨2195562113466861312914255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463708075644574208609503 2195562113466861312914255)
        ·
          refine ⟨3293343170200291969371383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195562113466861312914255 3293343170200291969371383)
          ·
            refine ⟨4940014755300437954057075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293343170200291969371383 4940014755300437954057075)
            ·
              refine ⟨7410022132950656931085613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940014755300437954057075 7410022132950656931085613)
              ·
                refine ⟨2778758299856496349157105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7410022132950656931085613 2778758299856496349157105)
                ·
                  refine ⟨2084068724892372261867829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2778758299856496349157105 2084068724892372261867829)
                  ·
                    refine ⟨195381442958659899550109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2084068724892372261867829 195381442958659899550109)
                    ·
                      refine ⟨73268041109497462331291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195381442958659899550109 73268041109497462331291)
                      ·
                        rfl

theorem cell23_142689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_142689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142689 prefixEnd_142689 := by exact prefixLift 142689
  have htrace : WordTrace (prefixWord ++ tailWord_142689) baseStart_142689 baseEnd_142689 := by
    simpa [prefixWord, tailWord_142689, baseEnd_142689] using wordTrace_append hprefix tailTrace_142689
  have hstable : (prefixWord ++ tailWord_142689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142689).length < 2 ^ (prefixWord ++ tailWord_142689).sum := by decide
  have hdescent : baseEnd_142689 < baseStart_142689 := by decide
  rcases family_descends (prefixWord ++ tailWord_142689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142740 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_142740 : Nat := 118140960795 + 142740 * 2 ^ 59
def prefixEnd_142740 : Nat := 4983230072969 + 3 ^ 40 * 142740 * 2
def baseEnd_142740 : Nat := 73294228622876762793557

theorem tailTrace_142740 : CollatzResearch.WordTrace tailWord_142740 prefixEnd_142740 73294228622876762793557 := by
  unfold tailWord_142740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603077751442416448136837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3470770335256555264182449 2603077751442416448136837)
  ·
    refine ⟨488077078395453084025657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2603077751442416448136837 488077078395453084025657)
    ·
      refine ⟨366057808796589813019243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 488077078395453084025657 366057808796589813019243)
      ·
        refine ⟨549086713194884719528865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366057808796589813019243 549086713194884719528865)
        ·
          refine ⟨411815034896163539646649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549086713194884719528865 411815034896163539646649)
          ·
            refine ⟨308861276172122654734987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411815034896163539646649 308861276172122654734987)
            ·
              refine ⟨463291914258183982102481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308861276172122654734987 463291914258183982102481)
              ·
                refine ⟨347468935693637986576861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463291914258183982102481 347468935693637986576861)
                ·
                  refine ⟨130300850885114244966323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347468935693637986576861 130300850885114244966323)
                  ·
                    refine ⟨195451276327671367449485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130300850885114244966323 195451276327671367449485)
                    ·
                      refine ⟨73294228622876762793557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195451276327671367449485 73294228622876762793557)
                      ·
                        rfl

theorem cell23_142740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_142740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142740 prefixEnd_142740 := by exact prefixLift 142740
  have htrace : WordTrace (prefixWord ++ tailWord_142740) baseStart_142740 baseEnd_142740 := by
    simpa [prefixWord, tailWord_142740, baseEnd_142740] using wordTrace_append hprefix tailTrace_142740
  have hstable : (prefixWord ++ tailWord_142740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142740).length < 2 ^ (prefixWord ++ tailWord_142740).sum := by decide
  have hdescent : baseEnd_142740 < baseStart_142740 := by decide
  rcases family_descends (prefixWord ++ tailWord_142740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142746 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_142746 : Nat := 118140960795 + 142746 * 2 ^ 59
def prefixEnd_142746 : Nat := 4983230072969 + 3 ^ 40 * 142746 * 2
def baseEnd_142746 : Nat := 73297309506803739318529

theorem tailTrace_142746 : CollatzResearch.WordTrace tailWord_142746 prefixEnd_142746 73297309506803739318529 := by
  unfold tailWord_142746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301593585215773980248023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3470916227242063947328061 1301593585215773980248023)
  ·
    refine ⟨1952390377823660970372035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1301593585215773980248023 1952390377823660970372035)
    ·
      refine ⟨2928585566735491455558053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1952390377823660970372035 2928585566735491455558053)
      ·
        refine ⟨549109793762904647917135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2928585566735491455558053 549109793762904647917135)
        ·
          refine ⟨823664690644356971875703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549109793762904647917135 823664690644356971875703)
          ·
            refine ⟨1235497035966535457813555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823664690644356971875703 1235497035966535457813555)
            ·
              refine ⟨1853245553949803186720333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235497035966535457813555 1853245553949803186720333)
              ·
                refine ⟨694967082731176195020125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1853245553949803186720333 694967082731176195020125)
                ·
                  refine ⟨260612656024191073132547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694967082731176195020125 260612656024191073132547)
                  ·
                    refine ⟨390918984036286609698821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260612656024191073132547 390918984036286609698821)
                    ·
                      refine ⟨73297309506803739318529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 390918984036286609698821 73297309506803739318529)
                      ·
                        rfl

theorem cell23_142746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_142746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142746 prefixEnd_142746 := by exact prefixLift 142746
  have htrace : WordTrace (prefixWord ++ tailWord_142746) baseStart_142746 baseEnd_142746 := by
    simpa [prefixWord, tailWord_142746, baseEnd_142746] using wordTrace_append hprefix tailTrace_142746
  have hstable : (prefixWord ++ tailWord_142746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142746).length < 2 ^ (prefixWord ++ tailWord_142746).sum := by decide
  have hdescent : baseEnd_142746 < baseStart_142746 := by decide
  rcases family_descends (prefixWord ++ tailWord_142746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142756 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_142756 : Nat := 118140960795 + 142756 * 2 ^ 59
def prefixEnd_142756 : Nat := 4983230072969 + 3 ^ 40 * 142756 * 2
def baseEnd_142756 : Nat := 24434148104449566731161

theorem tailTrace_142756 : CollatzResearch.WordTrace tailWord_142756 prefixEnd_142756 24434148104449566731161 := by
  unfold tailWord_142756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603369535413433814428061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3471159380551245085904081 2603369535413433814428061)
  ·
    refine ⟨976263575780037680410523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2603369535413433814428061 976263575780037680410523)
    ·
      refine ⟨1464395363670056520615785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976263575780037680410523 1464395363670056520615785)
      ·
        refine ⟨1098296522752542390461839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1464395363670056520615785 1098296522752542390461839)
        ·
          refine ⟨1647444784128813585692759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098296522752542390461839 1647444784128813585692759)
          ·
            refine ⟨2471167176193220378539139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647444784128813585692759 2471167176193220378539139)
            ·
              refine ⟨3706750764289830567808709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471167176193220378539139 3706750764289830567808709)
              ·
                refine ⟨695015768304343231464133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3706750764289830567808709 695015768304343231464133)
                ·
                  refine ⟨130315456557064355899525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695015768304343231464133 130315456557064355899525)
                  ·
                    refine ⟨24434148104449566731161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130315456557064355899525 24434148104449566731161)
                    ·
                      rfl

theorem cell23_142756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_142756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142756 prefixEnd_142756 := by exact prefixLift 142756
  have htrace : WordTrace (prefixWord ++ tailWord_142756) baseStart_142756 baseEnd_142756 := by
    simpa [prefixWord, tailWord_142756, baseEnd_142756] using wordTrace_append hprefix tailTrace_142756
  have hstable : (prefixWord ++ tailWord_142756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142756).length < 2 ^ (prefixWord ++ tailWord_142756).sum := by decide
  have hdescent : baseEnd_142756 < baseStart_142756 := by decide
  rcases family_descends (prefixWord ++ tailWord_142756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142760 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 1, 5]
def baseStart_142760 : Nat := 118140960795 + 142760 * 2 ^ 59
def prefixEnd_142760 : Nat := 4983230072969 + 3 ^ 40 * 142760 * 2
def baseEnd_142760 : Nat := 24434832745322228181155

theorem tailTrace_142760 : CollatzResearch.WordTrace tailWord_142760 prefixEnd_142760 24434832745322228181155 := by
  unfold tailWord_142760
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603442481406188156000867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3471256641874917541334489 2603442481406188156000867)
  ·
    refine ⟨3905163722109282234001301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2603442481406188156000867 3905163722109282234001301)
    ·
      refine ⟨183054549473872604718811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3905163722109282234001301 183054549473872604718811)
      ·
        refine ⟨274581824210808907078217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183054549473872604718811 274581824210808907078217)
        ·
          refine ⟨205936368158106680308663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274581824210808907078217 205936368158106680308663)
          ·
            refine ⟨308904552237160020462995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205936368158106680308663 308904552237160020462995)
            ·
              refine ⟨463356828355740030694493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308904552237160020462995 463356828355740030694493)
              ·
                refine ⟨173758810633402511510435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463356828355740030694493 173758810633402511510435)
                ·
                  refine ⟨260638215950103767265653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173758810633402511510435 260638215950103767265653)
                  ·
                    refine ⟨24434832745322228181155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 260638215950103767265653 24434832745322228181155)
                    ·
                      rfl

theorem cell23_142760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_142760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142760 prefixEnd_142760 := by exact prefixLift 142760
  have htrace : WordTrace (prefixWord ++ tailWord_142760) baseStart_142760 baseEnd_142760 := by
    simpa [prefixWord, tailWord_142760, baseEnd_142760] using wordTrace_append hprefix tailTrace_142760
  have hstable : (prefixWord ++ tailWord_142760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142760).length < 2 ^ (prefixWord ++ tailWord_142760).sum := by decide
  have hdescent : baseEnd_142760 < baseStart_142760 := by decide
  rcases family_descends (prefixWord ++ tailWord_142760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142769 : List Nat := [1, 2, 2, 4, 1, 1, 12]
def baseStart_142769 : Nat := 118140960795 + 142769 * 2 ^ 59
def prefixEnd_142769 : Nat := 4983230072969 + 3 ^ 40 * 142769 * 2
def baseEnd_142769 : Nat := 905050858788359868283

theorem tailTrace_142769 : CollatzResearch.WordTrace tailWord_142769 prefixEnd_142769 905050858788359868283 := by
  unfold tailWord_142769
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207213219779770849079361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3471475479853180566052907 5207213219779770849079361)
  ·
    refine ⟨3905409914834828136809521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5207213219779770849079361 3905409914834828136809521)
    ·
      refine ⟨2929057436126121102607141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3905409914834828136809521 2929057436126121102607141)
      ·
        refine ⟨549198269273647706738839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2929057436126121102607141 549198269273647706738839)
        ·
          refine ⟨823797403910471560108259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549198269273647706738839 823797403910471560108259)
          ·
            refine ⟨1235696105865707340162389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823797403910471560108259 1235696105865707340162389)
            ·
              refine ⟨905050858788359868283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 1235696105865707340162389 905050858788359868283)
              ·
                rfl

theorem cell23_142769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 12].length) (baseStart_142769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142769 prefixEnd_142769 := by exact prefixLift 142769
  have htrace : WordTrace (prefixWord ++ tailWord_142769) baseStart_142769 baseEnd_142769 := by
    simpa [prefixWord, tailWord_142769, baseEnd_142769] using wordTrace_append hprefix tailTrace_142769
  have hstable : (prefixWord ++ tailWord_142769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142769).length < 2 ^ (prefixWord ++ tailWord_142769).sum := by decide
  have hdescent : baseEnd_142769 < baseStart_142769 := by decide
  rcases family_descends (prefixWord ++ tailWord_142769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142773 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_142773 : Nat := 118140960795 + 142773 * 2 ^ 59
def prefixEnd_142773 : Nat := 4983230072969 + 3 ^ 40 * 142773 * 2
def baseEnd_142773 : Nat := 24437057828158377893635

theorem tailTrace_142773 : CollatzResearch.WordTrace tailWord_142773 prefixEnd_142773 24437057828158377893635 := by
  unfold tailWord_142773
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207359111765279532224973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3471572741176853021483315 5207359111765279532224973)
  ·
    refine ⟨1952759666911979824584365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5207359111765279532224973 1952759666911979824584365)
    ·
      refine ⟨732284875091992434219137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1952759666911979824584365 732284875091992434219137)
      ·
        refine ⟨549213656318994325664353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 732284875091992434219137 549213656318994325664353)
        ·
          refine ⟨411910242239245744248265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549213656318994325664353 411910242239245744248265)
          ·
            refine ⟨308932681679434308186199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411910242239245744248265 308932681679434308186199)
            ·
              refine ⟨463399022519151462279299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308932681679434308186199 463399022519151462279299)
              ·
                refine ⟨695098533778727193418949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463399022519151462279299 695098533778727193418949)
                ·
                  refine ⟨130330975083511348766053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695098533778727193418949 130330975083511348766053)
                  ·
                    refine ⟨24437057828158377893635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130330975083511348766053 24437057828158377893635)
                    ·
                      rfl

theorem cell23_142773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_142773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142773 prefixEnd_142773 := by exact prefixLift 142773
  have htrace : WordTrace (prefixWord ++ tailWord_142773) baseStart_142773 baseEnd_142773 := by
    simpa [prefixWord, tailWord_142773, baseEnd_142773] using wordTrace_append hprefix tailTrace_142773
  have hstable : (prefixWord ++ tailWord_142773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142773).length < 2 ^ (prefixWord ++ tailWord_142773).sum := by decide
  have hdescent : baseEnd_142773 < baseStart_142773 := by decide
  rcases family_descends (prefixWord ++ tailWord_142773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142799 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 2, 7]
def baseStart_142799 : Nat := 118140960795 + 142799 * 2 ^ 59
def prefixEnd_142799 : Nat := 4983230072969 + 3 ^ 40 * 142799 * 2
def baseEnd_142799 : Nat := 24441507993830677318595

theorem tailTrace_142799 : CollatzResearch.WordTrace tailWord_142799 prefixEnd_142799 24441507993830677318595 := by
  unfold tailWord_142799
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208307409671085972671451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3472204939780723981780967 5208307409671085972671451)
  ·
    refine ⟨7812461114506628959007177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5208307409671085972671451 7812461114506628959007177)
    ·
      refine ⟨5859345835879971719255383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7812461114506628959007177 5859345835879971719255383)
      ·
        refine ⟨8789018753819957578883075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5859345835879971719255383 8789018753819957578883075)
        ·
          refine ⟨13183528130729936368324613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8789018753819957578883075 13183528130729936368324613)
          ·
            refine ⟨2471911524511863069060865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13183528130729936368324613 2471911524511863069060865)
            ·
              refine ⟨1853933643383897301795649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471911524511863069060865 1853933643383897301795649)
              ·
                refine ⟨1390450232537922976346737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853933643383897301795649 1390450232537922976346737)
                ·
                  refine ⟨1042837674403442232260053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1390450232537922976346737 1042837674403442232260053)
                  ·
                    refine ⟨24441507993830677318595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1042837674403442232260053 24441507993830677318595)
                    ·
                      rfl

theorem cell23_142799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_142799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142799 prefixEnd_142799 := by exact prefixLift 142799
  have htrace : WordTrace (prefixWord ++ tailWord_142799) baseStart_142799 baseEnd_142799 := by
    simpa [prefixWord, tailWord_142799, baseEnd_142799] using wordTrace_append hprefix tailTrace_142799
  have hstable : (prefixWord ++ tailWord_142799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142799).length < 2 ^ (prefixWord ++ tailWord_142799).sum := by decide
  have hdescent : baseEnd_142799 < baseStart_142799 := by decide
  rcases family_descends (prefixWord ++ tailWord_142799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142830 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_142830 : Nat := 118140960795 + 142830 * 2 ^ 59
def prefixEnd_142830 : Nat := 4983230072969 + 3 ^ 40 * 142830 * 2
def baseEnd_142830 : Nat := 73340441881781410668143

theorem tailTrace_142830 : CollatzResearch.WordTrace tailWord_142830 prefixEnd_142830 73340441881781410668143 := by
  unfold tailWord_142830
  simp only [CollatzResearch.WordTrace]
  refine ⟨651179759069847283381243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3472958715039185511366629 651179759069847283381243)
  ·
    refine ⟨976769638604770925071865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 651179759069847283381243 976769638604770925071865)
    ·
      refine ⟨732577228953578193803899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 976769638604770925071865 732577228953578193803899)
      ·
        refine ⟨1098865843430367290705849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732577228953578193803899 1098865843430367290705849)
        ·
          refine ⟨824149382572775468029387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1098865843430367290705849 824149382572775468029387)
          ·
            refine ⟨1236224073859163202044081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824149382572775468029387 1236224073859163202044081)
            ·
              refine ⟨927168055394372401533061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236224073859163202044081 927168055394372401533061)
              ·
                refine ⟨173844010386444825287449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 927168055394372401533061 173844010386444825287449)
                ·
                  refine ⟨130383007789833618965587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173844010386444825287449 130383007789833618965587)
                  ·
                    refine ⟨195574511684750428448381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130383007789833618965587 195574511684750428448381)
                    ·
                      refine ⟨73340441881781410668143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195574511684750428448381 73340441881781410668143)
                      ·
                        rfl

theorem cell23_142830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_142830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142830 prefixEnd_142830 := by exact prefixLift 142830
  have htrace : WordTrace (prefixWord ++ tailWord_142830) baseStart_142830 baseEnd_142830 := by
    simpa [prefixWord, tailWord_142830, baseEnd_142830] using wordTrace_append hprefix tailTrace_142830
  have hstable : (prefixWord ++ tailWord_142830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142830).length < 2 ^ (prefixWord ++ tailWord_142830).sum := by decide
  have hdescent : baseEnd_142830 < baseStart_142830 := by decide
  rcases family_descends (prefixWord ++ tailWord_142830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142853 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 1, 4, 2]
def baseStart_142853 : Nat := 118140960795 + 142853 * 2 ^ 59
def prefixEnd_142853 : Nat := 4983230072969 + 3 ^ 40 * 142853 * 2
def baseEnd_142853 : Nat := 73352251936834820680537

theorem tailTrace_142853 : CollatzResearch.WordTrace tailWord_142853 prefixEnd_142853 73352251936834820680537 := by
  unfold tailWord_142853
  simp only [CollatzResearch.WordTrace]
  refine ⟨5210276951475453195137213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3473517967650302130091475 5210276951475453195137213)
  ·
    refine ⟨1953853856803294948176455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5210276951475453195137213 1953853856803294948176455)
    ·
      refine ⟨2930780785204942422264683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1953853856803294948176455 2930780785204942422264683)
      ·
        refine ⟨4396171177807413633397025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2930780785204942422264683 4396171177807413633397025)
        ·
          refine ⟨3297128383355560225047769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4396171177807413633397025 3297128383355560225047769)
          ·
            refine ⟨2472846287516670168785827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297128383355560225047769 2472846287516670168785827)
            ·
              refine ⟨3709269431275005253178741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472846287516670168785827 3709269431275005253178741)
              ·
                refine ⟨347744009182031742485507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3709269431275005253178741 347744009182031742485507)
                ·
                  refine ⟨521616013773047613728261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347744009182031742485507 521616013773047613728261)
                  ·
                    refine ⟨97803002582446427574049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521616013773047613728261 97803002582446427574049)
                    ·
                      refine ⟨73352251936834820680537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97803002582446427574049 73352251936834820680537)
                      ·
                        rfl

theorem cell23_142853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_142853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142853 prefixEnd_142853 := by exact prefixLift 142853
  have htrace : WordTrace (prefixWord ++ tailWord_142853) baseStart_142853 baseEnd_142853 := by
    simpa [prefixWord, tailWord_142853, baseEnd_142853] using wordTrace_append hprefix tailTrace_142853
  have hstable : (prefixWord ++ tailWord_142853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142853).length < 2 ^ (prefixWord ++ tailWord_142853).sum := by decide
  have hdescent : baseEnd_142853 < baseStart_142853 := by decide
  rcases family_descends (prefixWord ++ tailWord_142853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142856 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_142856 : Nat := 118140960795 + 142856 * 2 ^ 59
def prefixEnd_142856 : Nat := 4983230072969 + 3 ^ 40 * 142856 * 2
def baseEnd_142856 : Nat := 73353792378798308943023

theorem tailTrace_142856 : CollatzResearch.WordTrace tailWord_142856 prefixEnd_142856 73353792378798308943023 := by
  unfold tailWord_142856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605193185232292353748211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3473590913643056471664281 2605193185232292353748211)
  ·
    refine ⟨3907789777848438530622317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2605193185232292353748211 3907789777848438530622317)
    ·
      refine ⟨1465421166693164448983369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3907789777848438530622317 1465421166693164448983369)
      ·
        refine ⟨1099065875019873336737527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1465421166693164448983369 1099065875019873336737527)
        ·
          refine ⟨1648598812529810005106291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099065875019873336737527 1648598812529810005106291)
          ·
            refine ⟨2472898218794715007659437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648598812529810005106291 2472898218794715007659437)
            ·
              refine ⟨927336832048018127872289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2472898218794715007659437 927336832048018127872289)
              ·
                refine ⟨695502624036013595904217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927336832048018127872289 695502624036013595904217)
                ·
                  refine ⟨521626968027010196928163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 695502624036013595904217 521626968027010196928163)
                  ·
                    refine ⟨782440452040515295392245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 521626968027010196928163 782440452040515295392245)
                    ·
                      refine ⟨73353792378798308943023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 782440452040515295392245 73353792378798308943023)
                      ·
                        rfl

theorem cell23_142856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_142856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142856 prefixEnd_142856 := by exact prefixLift 142856
  have htrace : WordTrace (prefixWord ++ tailWord_142856) baseStart_142856 baseEnd_142856 := by
    simpa [prefixWord, tailWord_142856, baseEnd_142856] using wordTrace_append hprefix tailTrace_142856
  have hstable : (prefixWord ++ tailWord_142856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142856).length < 2 ^ (prefixWord ++ tailWord_142856).sum := by decide
  have hdescent : baseEnd_142856 < baseStart_142856 := by decide
  rcases family_descends (prefixWord ++ tailWord_142856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142903 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_142903 : Nat := 118140960795 + 142903 * 2 ^ 59
def prefixEnd_142903 : Nat := 4983230072969 + 3 ^ 40 * 142903 * 2
def baseEnd_142903 : Nat := 73377925969559625055307

theorem tailTrace_142903 : CollatzResearch.WordTrace tailWord_142903 prefixEnd_142903 73377925969559625055307 := by
  unfold tailWord_142903
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212100601294311734457363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3474733734196207822971575 5212100601294311734457363)
  ·
    refine ⟨7818150901941467601686045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5212100601294311734457363 7818150901941467601686045)
    ·
      refine ⟨2931806588228050350632267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7818150901941467601686045 2931806588228050350632267)
      ·
        refine ⟨4397709882342075525948401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931806588228050350632267 4397709882342075525948401)
        ·
          refine ⟨3298282411756556644461301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4397709882342075525948401 3298282411756556644461301)
          ·
            refine ⟨309213976102177185418247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3298282411756556644461301 309213976102177185418247)
            ·
              refine ⟨463820964153265778127371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309213976102177185418247 463820964153265778127371)
              ·
                refine ⟨695731446229898667191057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463820964153265778127371 695731446229898667191057)
                ·
                  refine ⟨521798584672424000393293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 695731446229898667191057 521798584672424000393293)
                  ·
                    refine ⟨195674469252159000147485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 521798584672424000393293 195674469252159000147485)
                    ·
                      refine ⟨73377925969559625055307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195674469252159000147485 73377925969559625055307)
                      ·
                        rfl

theorem cell23_142903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_142903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142903 prefixEnd_142903 := by exact prefixLift 142903
  have htrace : WordTrace (prefixWord ++ tailWord_142903) baseStart_142903 baseEnd_142903 := by
    simpa [prefixWord, tailWord_142903, baseEnd_142903] using wordTrace_append hprefix tailTrace_142903
  have hstable : (prefixWord ++ tailWord_142903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142903).length < 2 ^ (prefixWord ++ tailWord_142903).sum := by decide
  have hdescent : baseEnd_142903 < baseStart_142903 := by decide
  rcases family_descends (prefixWord ++ tailWord_142903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142906 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_142906 : Nat := 118140960795 + 142906 * 2 ^ 59
def prefixEnd_142906 : Nat := 4983230072969 + 3 ^ 40 * 142906 * 2
def baseEnd_142906 : Nat := 24459822137174371105931

theorem tailTrace_142906 : CollatzResearch.WordTrace tailWord_142906 prefixEnd_142906 24459822137174371105931 := by
  unfold tailWord_142906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303052505070860811704143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3474806680188962164544381 1303052505070860811704143)
  ·
    refine ⟨1954578757606291217556215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1303052505070860811704143 1954578757606291217556215)
    ·
      refine ⟨2931868136409436826334323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1954578757606291217556215 2931868136409436826334323)
      ·
        refine ⟨4397802204614155239501485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931868136409436826334323 4397802204614155239501485)
        ·
          refine ⟨1649175826730308214813057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4397802204614155239501485 1649175826730308214813057)
          ·
            refine ⟨1236881870047731161109793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1649175826730308214813057 1236881870047731161109793)
            ·
              refine ⟨927661402535798370832345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236881870047731161109793 927661402535798370832345)
              ·
                refine ⟨695746051901848778124259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927661402535798370832345 695746051901848778124259)
                ·
                  refine ⟨1043619077852773167186389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695746051901848778124259 1043619077852773167186389)
                  ·
                    refine ⟨24459822137174371105931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1043619077852773167186389 24459822137174371105931)
                    ·
                      rfl

theorem cell23_142906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_142906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142906 prefixEnd_142906 := by exact prefixLift 142906
  have htrace : WordTrace (prefixWord ++ tailWord_142906) baseStart_142906 baseEnd_142906 := by
    simpa [prefixWord, tailWord_142906, baseEnd_142906] using wordTrace_append hprefix tailTrace_142906
  have hstable : (prefixWord ++ tailWord_142906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142906).length < 2 ^ (prefixWord ++ tailWord_142906).sum := by decide
  have hdescent : baseEnd_142906 < baseStart_142906 := by decide
  rcases family_descends (prefixWord ++ tailWord_142906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142953 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 3, 4]
def baseStart_142953 : Nat := 118140960795 + 142953 * 2 ^ 59
def prefixEnd_142953 : Nat := 4983230072969 + 3 ^ 40 * 142953 * 2
def baseEnd_142953 : Nat := 24467866667428143143359

theorem tailTrace_142953 : CollatzResearch.WordTrace tailWord_142953 prefixEnd_142953 24467866667428143143359 := by
  unfold tailWord_142953
  simp only [CollatzResearch.WordTrace]
  refine ⟨5213924251113170273777513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3475949500742113515851675 5213924251113170273777513)
  ·
    refine ⟨3910443188334877705333135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5213924251113170273777513 3910443188334877705333135)
    ·
      refine ⟨5865664782502316557999703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3910443188334877705333135 5865664782502316557999703)
      ·
        refine ⟨8798497173753474836999555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865664782502316557999703 8798497173753474836999555)
        ·
          refine ⟨13197745760630212255499333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8798497173753474836999555 13197745760630212255499333)
          ·
            refine ⟨2474577330118164797906125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13197745760630212255499333 2474577330118164797906125)
            ·
              refine ⟨927966498794311799214797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2474577330118164797906125 927966498794311799214797)
              ·
                refine ⟨347987437047866924705549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 927966498794311799214797 347987437047866924705549)
                ·
                  refine ⟨130495288892950096764581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347987437047866924705549 130495288892950096764581)
                  ·
                    refine ⟨24467866667428143143359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130495288892950096764581 24467866667428143143359)
                    ·
                      rfl

theorem cell23_142953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_142953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142953 prefixEnd_142953 := by exact prefixLift 142953
  have htrace : WordTrace (prefixWord ++ tailWord_142953) baseStart_142953 baseEnd_142953 := by
    simpa [prefixWord, tailWord_142953, baseEnd_142953] using wordTrace_append hprefix tailTrace_142953
  have hstable : (prefixWord ++ tailWord_142953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142953).length < 2 ^ (prefixWord ++ tailWord_142953).sum := by decide
  have hdescent : baseEnd_142953 < baseStart_142953 := by decide
  rcases family_descends (prefixWord ++ tailWord_142953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142956 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_142956 : Nat := 118140960795 + 142956 * 2 ^ 59
def prefixEnd_142956 : Nat := 4983230072969 + 3 ^ 40 * 142956 * 2
def baseEnd_142956 : Nat := 73405140444247917692563

theorem tailTrace_142956 : CollatzResearch.WordTrace tailWord_142956 prefixEnd_142956 73405140444247917692563 := by
  unfold tailWord_142956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607016835051150893068361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3476022446734867857424481 2607016835051150893068361)
  ·
    refine ⟨1955262626288363169801271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2607016835051150893068361 1955262626288363169801271)
    ·
      refine ⟨2932893939432544754701907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955262626288363169801271 2932893939432544754701907)
      ·
        refine ⟨4399340909148817132052861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932893939432544754701907 4399340909148817132052861)
        ·
          refine ⟨1649752840930806424519823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4399340909148817132052861 1649752840930806424519823)
          ·
            refine ⟨2474629261396209636779735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649752840930806424519823 2474629261396209636779735)
            ·
              refine ⟨3711943892094314455169603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474629261396209636779735 3711943892094314455169603)
              ·
                refine ⟨5567915838141471682754405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3711943892094314455169603 5567915838141471682754405)
                ·
                  refine ⟨1043984219651525940516451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5567915838141471682754405 1043984219651525940516451)
                  ·
                    refine ⟨1565976329477288910774677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1043984219651525940516451 1565976329477288910774677)
                    ·
                      refine ⟨73405140444247917692563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1565976329477288910774677 73405140444247917692563)
                      ·
                        rfl

theorem cell23_142956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_142956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142956 prefixEnd_142956 := by exact prefixLift 142956
  have htrace : WordTrace (prefixWord ++ tailWord_142956) baseStart_142956 baseEnd_142956 := by
    simpa [prefixWord, tailWord_142956, baseEnd_142956] using wordTrace_append hprefix tailTrace_142956
  have hstable : (prefixWord ++ tailWord_142956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142956).length < 2 ^ (prefixWord ++ tailWord_142956).sum := by decide
  have hdescent : baseEnd_142956 < baseStart_142956 := by decide
  rcases family_descends (prefixWord ++ tailWord_142956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142960 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 2, 4, 2]
def baseStart_142960 : Nat := 118140960795 + 142960 * 2 ^ 59
def prefixEnd_142960 : Nat := 4983230072969 + 3 ^ 40 * 142960 * 2
def baseEnd_142960 : Nat := 73407194366865902042545

theorem tailTrace_142960 : CollatzResearch.WordTrace tailWord_142960 prefixEnd_142960 73407194366865902042545 := by
  unfold tailWord_142960
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607089781043905234641167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3476119708058540312854889 2607089781043905234641167)
  ·
    refine ⟨3910634671565857851961751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2607089781043905234641167 3910634671565857851961751)
    ·
      refine ⟨5865952007348786777942627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3910634671565857851961751 5865952007348786777942627)
      ·
        refine ⟨8798928011023180166913941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865952007348786777942627 8798928011023180166913941)
        ·
          refine ⟨412449750516711570324091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8798928011023180166913941 412449750516711570324091)
          ·
            refine ⟨618674625775067355486137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412449750516711570324091 618674625775067355486137)
            ·
              refine ⟨464005969331300516614603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618674625775067355486137 464005969331300516614603)
              ·
                refine ⟨696008953996950774921905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464005969331300516614603 696008953996950774921905)
                ·
                  refine ⟨522006715497713081191429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 696008953996950774921905 522006715497713081191429)
                  ·
                    refine ⟨97876259155821202723393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 522006715497713081191429 97876259155821202723393)
                    ·
                      refine ⟨73407194366865902042545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97876259155821202723393 73407194366865902042545)
                      ·
                        rfl

theorem cell23_142960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 4, 2].length) (baseStart_142960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142960 prefixEnd_142960 := by exact prefixLift 142960
  have htrace : WordTrace (prefixWord ++ tailWord_142960) baseStart_142960 baseEnd_142960 := by
    simpa [prefixWord, tailWord_142960, baseEnd_142960] using wordTrace_append hprefix tailTrace_142960
  have hstable : (prefixWord ++ tailWord_142960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142960).length < 2 ^ (prefixWord ++ tailWord_142960).sum := by decide
  have hdescent : baseEnd_142960 < baseStart_142960 := by decide
  rcases family_descends (prefixWord ++ tailWord_142960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143004 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_143004 : Nat := 118140960795 + 143004 * 2 ^ 59
def prefixEnd_143004 : Nat := 4983230072969 + 3 ^ 40 * 143004 * 2
def baseEnd_143004 : Nat := 24476595838554576630781

theorem tailTrace_143004 : CollatzResearch.WordTrace tailWord_143004 prefixEnd_143004 24476595838554576630781 := by
  unfold tailWord_143004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607892186964202991942033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3477189582618937322589377 2607892186964202991942033)
  ·
    refine ⟨1955919140223152243956525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2607892186964202991942033 1955919140223152243956525)
    ·
      refine ⟨733469677583682091483697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1955919140223152243956525 733469677583682091483697)
      ·
        refine ⟨550102258187761568612773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 733469677583682091483697 550102258187761568612773)
        ·
          refine ⟨103144173410205294114895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 550102258187761568612773 103144173410205294114895)
          ·
            refine ⟨154716260115307941172343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103144173410205294114895 154716260115307941172343)
            ·
              refine ⟨232074390172961911758515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154716260115307941172343 232074390172961911758515)
              ·
                refine ⟨348111585259442867637773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232074390172961911758515 348111585259442867637773)
                ·
                  refine ⟨130541844472291075364165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348111585259442867637773 130541844472291075364165)
                  ·
                    refine ⟨24476595838554576630781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130541844472291075364165 24476595838554576630781)
                    ·
                      rfl

theorem cell23_143004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_143004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143004 prefixEnd_143004 := by exact prefixLift 143004
  have htrace : WordTrace (prefixWord ++ tailWord_143004) baseStart_143004 baseEnd_143004 := by
    simpa [prefixWord, tailWord_143004, baseEnd_143004] using wordTrace_append hprefix tailTrace_143004
  have hstable : (prefixWord ++ tailWord_143004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143004).length < 2 ^ (prefixWord ++ tailWord_143004).sum := by decide
  have hdescent : baseEnd_143004 < baseStart_143004 := by decide
  rcases family_descends (prefixWord ++ tailWord_143004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143037 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_143037 : Nat := 118140960795 + 143037 * 2 ^ 59
def prefixEnd_143037 : Nat := 4983230072969 + 3 ^ 40 * 143037 * 2
def baseEnd_143037 : Nat := 73446732377262100779691

theorem tailTrace_143037 : CollatzResearch.WordTrace tailWord_143037 prefixEnd_143037 73446732377262100779691 := by
  unfold tailWord_143037
  simp only [CollatzResearch.WordTrace]
  refine ⟨5216987982808852619835365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3477991988539235079890243 5216987982808852619835365)
  ·
    refine ⟨978185246776659866219131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5216987982808852619835365 978185246776659866219131)
    ·
      refine ⟨1467277870164989799328697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978185246776659866219131 1467277870164989799328697)
      ·
        refine ⟨1100458402623742349496523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1467277870164989799328697 1100458402623742349496523)
        ·
          refine ⟨1650687603935613524244785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100458402623742349496523 1650687603935613524244785)
          ·
            refine ⟨1238015702951710143183589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1650687603935613524244785 1238015702951710143183589)
            ·
              refine ⟨232127944303445651846923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1238015702951710143183589 232127944303445651846923)
              ·
                refine ⟨348191916455168477770385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232127944303445651846923 348191916455168477770385)
                ·
                  refine ⟨261143937341376358327789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348191916455168477770385 261143937341376358327789)
                  ·
                    refine ⟨97928976503016134372921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261143937341376358327789 97928976503016134372921)
                    ·
                      refine ⟨73446732377262100779691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97928976503016134372921 73446732377262100779691)
                      ·
                        rfl

theorem cell23_143037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_143037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143037 prefixEnd_143037 := by exact prefixLift 143037
  have htrace : WordTrace (prefixWord ++ tailWord_143037) baseStart_143037 baseEnd_143037 := by
    simpa [prefixWord, tailWord_143037, baseEnd_143037] using wordTrace_append hprefix tailTrace_143037
  have hstable : (prefixWord ++ tailWord_143037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143037).length < 2 ^ (prefixWord ++ tailWord_143037).sum := by decide
  have hdescent : baseEnd_143037 < baseStart_143037 := by decide
  rcases family_descends (prefixWord ++ tailWord_143037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143044 : List Nat := [2, 3, 3, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_143044 : Nat := 118140960795 + 143044 * 2 ^ 59
def prefixEnd_143044 : Nat := 4983230072969 + 3 ^ 40 * 143044 * 2
def baseEnd_143044 : Nat := 73450326741843573392159

theorem tailTrace_143044 : CollatzResearch.WordTrace tailWord_143044 prefixEnd_143044 73450326741843573392159 := by
  unfold tailWord_143044
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608621646891746407670093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3478162195855661876893457 2608621646891746407670093)
  ·
    refine ⟨978233117584404902876285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2608621646891746407670093 978233117584404902876285)
    ·
      refine ⟨366837419094151838578607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 978233117584404902876285 366837419094151838578607)
      ·
        refine ⟨550256128641227757867911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366837419094151838578607 550256128641227757867911)
        ·
          refine ⟨825384192961841636801867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550256128641227757867911 825384192961841636801867)
          ·
            refine ⟨1238076289442762455202801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825384192961841636801867 1238076289442762455202801)
            ·
              refine ⟨928557217082071841402101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1238076289442762455202801 928557217082071841402101)
              ·
                refine ⟨87052239101444235131447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 928557217082071841402101 87052239101444235131447)
                ·
                  refine ⟨130578358652166352697171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87052239101444235131447 130578358652166352697171)
                  ·
                    refine ⟨195867537978249529045757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130578358652166352697171 195867537978249529045757)
                    ·
                      refine ⟨73450326741843573392159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195867537978249529045757 73450326741843573392159)
                      ·
                        rfl

theorem cell23_143044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_143044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143044 prefixEnd_143044 := by exact prefixLift 143044
  have htrace : WordTrace (prefixWord ++ tailWord_143044) baseStart_143044 baseEnd_143044 := by
    simpa [prefixWord, tailWord_143044, baseEnd_143044] using wordTrace_append hprefix tailTrace_143044
  have hstable : (prefixWord ++ tailWord_143044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143044).length < 2 ^ (prefixWord ++ tailWord_143044).sum := by decide
  have hdescent : baseEnd_143044 < baseStart_143044 := by decide
  rcases family_descends (prefixWord ++ tailWord_143044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143063 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_143063 : Nat := 118140960795 + 143063 * 2 ^ 59
def prefixEnd_143063 : Nat := 4983230072969 + 3 ^ 40 * 143063 * 2
def baseEnd_143063 : Nat := 73460082874278999054571

theorem tailTrace_143063 : CollatzResearch.WordTrace tailWord_143063 prefixEnd_143063 73460082874278999054571 := by
  unfold tailWord_143063
  simp only [CollatzResearch.WordTrace]
  refine ⟨5217936280714659060281843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3478624187143106040187895 5217936280714659060281843)
  ·
    refine ⟨7826904421071988590422765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5217936280714659060281843 7826904421071988590422765)
    ·
      refine ⟨2935089157901995721408537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7826904421071988590422765 2935089157901995721408537)
      ·
        refine ⟨2201316868426496791056403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935089157901995721408537 2201316868426496791056403)
        ·
          refine ⟨3301975302639745186584605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201316868426496791056403 3301975302639745186584605)
          ·
            refine ⟨1238240738489904444969227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3301975302639745186584605 1238240738489904444969227)
            ·
              refine ⟨1857361107734856667453841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238240738489904444969227 1857361107734856667453841)
              ·
                refine ⟨1393020830801142500590381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1857361107734856667453841 1393020830801142500590381)
                ·
                  refine ⟨522382811550428437721393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1393020830801142500590381 522382811550428437721393)
                  ·
                    refine ⟨391787108662821328291045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 522382811550428437721393 391787108662821328291045)
                    ·
                      refine ⟨73460082874278999054571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 391787108662821328291045 73460082874278999054571)
                      ·
                        rfl

theorem cell23_143063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_143063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143063 prefixEnd_143063 := by exact prefixLift 143063
  have htrace : WordTrace (prefixWord ++ tailWord_143063) baseStart_143063 baseEnd_143063 := by
    simpa [prefixWord, tailWord_143063, baseEnd_143063] using wordTrace_append hprefix tailTrace_143063
  have hstable : (prefixWord ++ tailWord_143063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143063).length < 2 ^ (prefixWord ++ tailWord_143063).sum := by decide
  have hdescent : baseEnd_143063 < baseStart_143063 := by decide
  rcases family_descends (prefixWord ++ tailWord_143063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143080 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_143080 : Nat := 118140960795 + 143080 * 2 ^ 59
def prefixEnd_143080 : Nat := 4983230072969 + 3 ^ 40 * 143080 * 2
def baseEnd_143080 : Nat := 73468812045405432541993

theorem tailTrace_143080 : CollatzResearch.WordTrace tailWord_143080 prefixEnd_143080 73468812045405432541993 := by
  unfold tailWord_143080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609278160826535481825347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3479037547768713975767129 2609278160826535481825347)
  ·
    refine ⟨3913917241239803222738021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2609278160826535481825347 3913917241239803222738021)
    ·
      refine ⟨733859482732463104263379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3913917241239803222738021 733859482732463104263379)
      ·
        refine ⟨1100789224098694656395069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733859482732463104263379 1100789224098694656395069)
        ·
          refine ⟨412795959037010496148151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1100789224098694656395069 412795959037010496148151)
          ·
            refine ⟨619193938555515744222227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412795959037010496148151 619193938555515744222227)
            ·
              refine ⟨928790907833273616333341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619193938555515744222227 928790907833273616333341)
              ·
                refine ⟨348296590437477606125003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 928790907833273616333341 348296590437477606125003)
                ·
                  refine ⟨522444885656216409187505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348296590437477606125003 522444885656216409187505)
                  ·
                    refine ⟨391833664242162306890629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 522444885656216409187505 391833664242162306890629)
                    ·
                      refine ⟨73468812045405432541993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 391833664242162306890629 73468812045405432541993)
                      ·
                        rfl

theorem cell23_143080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_143080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143080 prefixEnd_143080 := by exact prefixLift 143080
  have htrace : WordTrace (prefixWord ++ tailWord_143080) baseStart_143080 baseEnd_143080 := by
    simpa [prefixWord, tailWord_143080, baseEnd_143080] using wordTrace_append hprefix tailTrace_143080
  have hstable : (prefixWord ++ tailWord_143080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143080).length < 2 ^ (prefixWord ++ tailWord_143080).sum := by decide
  have hdescent : baseEnd_143080 < baseStart_143080 := by decide
  rcases family_descends (prefixWord ++ tailWord_143080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143090 : List Nat := [3, 2, 1, 3, 1, 1, 5, 7]
def baseStart_143090 : Nat := 118140960795 + 143090 * 2 ^ 59
def prefixEnd_143090 : Nat := 4983230072969 + 3 ^ 40 * 143090 * 2
def baseEnd_143090 : Nat := 2721257290812977533961

theorem tailTrace_143090 : CollatzResearch.WordTrace tailWord_143090 prefixEnd_143090 2721257290812977533961 := by
  unfold tailWord_143090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304730262904210667878681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3479280701077895114343149 1304730262904210667878681)
  ·
    refine ⟨978547697178158000909011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1304730262904210667878681 978547697178158000909011)
    ·
      refine ⟨1467821545767237001363517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978547697178158000909011 1467821545767237001363517)
      ·
        refine ⟨550433079662713875511319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1467821545767237001363517 550433079662713875511319)
        ·
          refine ⟨825649619494070813266979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550433079662713875511319 825649619494070813266979)
          ·
            refine ⟨1238474429241106219900469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825649619494070813266979 1238474429241106219900469)
            ·
              refine ⟨116106977741353708115669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1238474429241106219900469 116106977741353708115669)
              ·
                refine ⟨2721257290812977533961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 116106977741353708115669 2721257290812977533961)
                ·
                  rfl

theorem cell23_143090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 7].length) (baseStart_143090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143090 prefixEnd_143090 := by exact prefixLift 143090
  have htrace : WordTrace (prefixWord ++ tailWord_143090) baseStart_143090 baseEnd_143090 := by
    simpa [prefixWord, tailWord_143090, baseEnd_143090] using wordTrace_append hprefix tailTrace_143090
  have hstable : (prefixWord ++ tailWord_143090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143090).length < 2 ^ (prefixWord ++ tailWord_143090).sum := by decide
  have hdescent : baseEnd_143090 < baseStart_143090 := by decide
  rcases family_descends (prefixWord ++ tailWord_143090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143100 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_143100 : Nat := 118140960795 + 143100 * 2 ^ 59
def prefixEnd_143100 : Nat := 4983230072969 + 3 ^ 40 * 143100 * 2
def baseEnd_143100 : Nat := 73479081658495354291901

theorem tailTrace_143100 : CollatzResearch.WordTrace tailWord_143100 prefixEnd_143100 73479081658495354291901 := by
  unfold tailWord_143100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609642890790307189689377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3479523854387076252919169 2609642890790307189689377)
  ·
    refine ⟨1957232168092730392267033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2609642890790307189689377 1957232168092730392267033)
    ·
      refine ⟨1467924126069547794200275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1957232168092730392267033 1467924126069547794200275)
      ·
        refine ⟨2201886189104321691300413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467924126069547794200275 2201886189104321691300413)
        ·
          refine ⟨825707320914120634237655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2201886189104321691300413 825707320914120634237655)
          ·
            refine ⟨1238560981371180951356483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825707320914120634237655 1238560981371180951356483)
            ·
              refine ⟨1857841472056771427034725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238560981371180951356483 1857841472056771427034725)
              ·
                refine ⟨348345276010644642569011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1857841472056771427034725 348345276010644642569011)
                ·
                  refine ⟨522517914015966963853517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348345276010644642569011 522517914015966963853517)
                  ·
                    refine ⟨195944217755987611445069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522517914015966963853517 195944217755987611445069)
                    ·
                      refine ⟨73479081658495354291901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 195944217755987611445069 73479081658495354291901)
                      ·
                        rfl

theorem cell23_143100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_143100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143100 prefixEnd_143100 := by exact prefixLift 143100
  have htrace : WordTrace (prefixWord ++ tailWord_143100) baseStart_143100 baseEnd_143100 := by
    simpa [prefixWord, tailWord_143100, baseEnd_143100] using wordTrace_append hprefix tailTrace_143100
  have hstable : (prefixWord ++ tailWord_143100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143100).length < 2 ^ (prefixWord ++ tailWord_143100).sum := by decide
  have hdescent : baseEnd_143100 < baseStart_143100 := by decide
  rcases family_descends (prefixWord ++ tailWord_143100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143111 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 2, 4]
def baseStart_143111 : Nat := 118140960795 + 143111 * 2 ^ 59
def prefixEnd_143111 : Nat := 4983230072969 + 3 ^ 40 * 143111 * 2
def baseEnd_143111 : Nat := 24494909981898270418117

theorem tailTrace_143111 : CollatzResearch.WordTrace tailWord_143111 prefixEnd_143111 24494909981898270418117 := by
  unfold tailWord_143111
  simp only [CollatzResearch.WordTrace]
  refine ⟨5219686984540763258029187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3479791323027175505352791 5219686984540763258029187)
  ·
    refine ⟨7829530476811144887043781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5219686984540763258029187 7829530476811144887043781)
    ·
      refine ⟨1468036964402089666320709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7829530476811144887043781 1468036964402089666320709)
      ·
        refine ⟨275256930825391812435133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1468036964402089666320709 275256930825391812435133)
        ·
          refine ⟨103221349059521929663175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275256930825391812435133 103221349059521929663175)
          ·
            refine ⟨154832023589282894494763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103221349059521929663175 154832023589282894494763)
            ·
              refine ⟨232248035383924341742145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154832023589282894494763 232248035383924341742145)
              ·
                refine ⟨174186026537943256306609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232248035383924341742145 174186026537943256306609)
                ·
                  refine ⟨130639519903457442229957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174186026537943256306609 130639519903457442229957)
                  ·
                    refine ⟨24494909981898270418117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130639519903457442229957 24494909981898270418117)
                    ·
                      rfl

theorem cell23_143111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_143111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143111 prefixEnd_143111 := by exact prefixLift 143111
  have htrace : WordTrace (prefixWord ++ tailWord_143111) baseStart_143111 baseEnd_143111 := by
    simpa [prefixWord, tailWord_143111, baseEnd_143111] using wordTrace_append hprefix tailTrace_143111
  have hstable : (prefixWord ++ tailWord_143111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143111).length < 2 ^ (prefixWord ++ tailWord_143111).sum := by decide
  have hdescent : baseEnd_143111 < baseStart_143111 := by decide
  rcases family_descends (prefixWord ++ tailWord_143111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143123 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4]
def baseStart_143123 : Nat := 118140960795 + 143123 * 2 ^ 59
def prefixEnd_143123 : Nat := 4983230072969 + 3 ^ 40 * 143123 * 2
def baseEnd_143123 : Nat := 73490891713548764304295

theorem tailTrace_143123 : CollatzResearch.WordTrace tailWord_143123 prefixEnd_143123 73490891713548764304295 := by
  unfold tailWord_143123
  simp only [CollatzResearch.WordTrace]
  refine ⟨5220124660497289307466023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3480083106998192871644015 5220124660497289307466023)
  ·
    refine ⟨7830186990745933961199035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5220124660497289307466023 7830186990745933961199035)
    ·
      refine ⟨11745280486118900941798553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7830186990745933961199035 11745280486118900941798553)
      ·
        refine ⟨8808960364589175706348915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11745280486118900941798553 8808960364589175706348915)
        ·
          refine ⟨13213440546883763559523373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8808960364589175706348915 13213440546883763559523373)
          ·
            refine ⟨4955040205081411334821265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13213440546883763559523373 4955040205081411334821265)
            ·
              refine ⟨3716280153811058501115949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4955040205081411334821265 3716280153811058501115949)
              ·
                refine ⟨1393605057679146937918481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3716280153811058501115949 1393605057679146937918481)
                ·
                  refine ⟨1045203793259360203438861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393605057679146937918481 1045203793259360203438861)
                  ·
                    refine ⟨391951422472260076289573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045203793259360203438861 391951422472260076289573)
                    ·
                      refine ⟨73490891713548764304295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 391951422472260076289573 73490891713548764304295)
                      ·
                        rfl

theorem cell23_143123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_143123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143123 prefixEnd_143123 := by exact prefixLift 143123
  have htrace : WordTrace (prefixWord ++ tailWord_143123) baseStart_143123 baseEnd_143123 := by
    simpa [prefixWord, tailWord_143123, baseEnd_143123] using wordTrace_append hprefix tailTrace_143123
  have hstable : (prefixWord ++ tailWord_143123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143123).length < 2 ^ (prefixWord ++ tailWord_143123).sum := by decide
  have hdescent : baseEnd_143123 < baseStart_143123 := by decide
  rcases family_descends (prefixWord ++ tailWord_143123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143144 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_143144 : Nat := 118140960795 + 143144 * 2 ^ 59
def prefixEnd_143144 : Nat := 4983230072969 + 3 ^ 40 * 143144 * 2
def baseEnd_143144 : Nat := 73501674807293182141699

theorem tailTrace_143144 : CollatzResearch.WordTrace tailWord_143144 prefixEnd_143144 73501674807293182141699 := by
  unfold tailWord_143144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610445296710604946990243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3480593728947473262653657 2610445296710604946990243)
  ·
    refine ⟨3915667945065907420485365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2610445296710604946990243 3915667945065907420485365)
    ·
      refine ⟨367093869849928820670503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3915667945065907420485365 367093869849928820670503)
      ·
        refine ⟨550640804774893231005755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367093869849928820670503 550640804774893231005755)
        ·
          refine ⟨825961207162339846508633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550640804774893231005755 825961207162339846508633)
          ·
            refine ⟨619470905371754884881475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825961207162339846508633 619470905371754884881475)
            ·
              refine ⟨929206358057632327322213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619470905371754884881475 929206358057632327322213)
              ·
                refine ⟨174226192135806061372915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 929206358057632327322213 174226192135806061372915)
                ·
                  refine ⟨261339288203709092059373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174226192135806061372915 261339288203709092059373)
                  ·
                    refine ⟨98002233076390909522265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261339288203709092059373 98002233076390909522265)
                    ·
                      refine ⟨73501674807293182141699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98002233076390909522265 73501674807293182141699)
                      ·
                        rfl

theorem cell23_143144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_143144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143144 prefixEnd_143144 := by exact prefixLift 143144
  have htrace : WordTrace (prefixWord ++ tailWord_143144) baseStart_143144 baseEnd_143144 := by
    simpa [prefixWord, tailWord_143144, baseEnd_143144] using wordTrace_append hprefix tailTrace_143144
  have hstable : (prefixWord ++ tailWord_143144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143144).length < 2 ^ (prefixWord ++ tailWord_143144).sum := by decide
  have hdescent : baseEnd_143144 < baseStart_143144 := by decide
  rcases family_descends (prefixWord ++ tailWord_143144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143160 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_143160 : Nat := 118140960795 + 143160 * 2 ^ 59
def prefixEnd_143160 : Nat := 4983230072969 + 3 ^ 40 * 143160 * 2
def baseEnd_143160 : Nat := 73509890497765119541625

theorem tailTrace_143160 : CollatzResearch.WordTrace tailWord_143160 prefixEnd_143160 73509890497765119541625 := by
  unfold tailWord_143160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610737080681622313281467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3480982774242163084375289 2610737080681622313281467)
  ·
    refine ⟨3916105621022433469922201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2610737080681622313281467 3916105621022433469922201)
    ·
      refine ⟨2937079215766825102441651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3916105621022433469922201 2937079215766825102441651)
      ·
        refine ⟨4405618823650237653662477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937079215766825102441651 4405618823650237653662477)
        ·
          refine ⟨1652107058868839120123429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4405618823650237653662477 1652107058868839120123429)
          ·
            refine ⟨309770073537907335023143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1652107058868839120123429 309770073537907335023143)
            ·
              refine ⟨464655110306861002534715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309770073537907335023143 464655110306861002534715)
              ·
                refine ⟨696982665460291503802073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464655110306861002534715 696982665460291503802073)
                ·
                  refine ⟨522736999095218627851555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 696982665460291503802073 522736999095218627851555)
                  ·
                    refine ⟨784105498642827941777333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522736999095218627851555 784105498642827941777333)
                    ·
                      refine ⟨73509890497765119541625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 784105498642827941777333 73509890497765119541625)
                      ·
                        rfl

theorem cell23_143160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_143160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143160 prefixEnd_143160 := by exact prefixLift 143160
  have htrace : WordTrace (prefixWord ++ tailWord_143160) baseStart_143160 baseEnd_143160 := by
    simpa [prefixWord, tailWord_143160, baseEnd_143160] using wordTrace_append hprefix tailTrace_143160
  have hstable : (prefixWord ++ tailWord_143160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143160).length < 2 ^ (prefixWord ++ tailWord_143160).sum := by decide
  have hdescent : baseEnd_143160 < baseStart_143160 := by decide
  rcases family_descends (prefixWord ++ tailWord_143160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143173 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_143173 : Nat := 118140960795 + 143173 * 2 ^ 59
def prefixEnd_143173 : Nat := 4983230072969 + 3 ^ 40 * 143173 * 2
def baseEnd_143173 : Nat := 73516565746273568679065

theorem tailTrace_143173 : CollatzResearch.WordTrace tailWord_143173 prefixEnd_143173 73516565746273568679065 := by
  unfold tailWord_143173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221948310316147846786173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3481298873544098564524115 5221948310316147846786173)
  ·
    refine ⟨1958230616368555442544815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5221948310316147846786173 1958230616368555442544815)
    ·
      refine ⟨2937345924552833163817223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958230616368555442544815 2937345924552833163817223)
      ·
        refine ⟨4406018886829249745725835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937345924552833163817223 4406018886829249745725835)
        ·
          refine ⟨6609028330243874618588753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406018886829249745725835 6609028330243874618588753)
          ·
            refine ⟨4956771247682905963941565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6609028330243874618588753 4956771247682905963941565)
            ·
              refine ⟨1858789217881089736478087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4956771247682905963941565 1858789217881089736478087)
              ·
                refine ⟨2788183826821634604717131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858789217881089736478087 2788183826821634604717131)
                ·
                  refine ⟨4182275740232451907075697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788183826821634604717131 4182275740232451907075697)
                  ·
                    refine ⟨3136706805174338930306773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4182275740232451907075697 3136706805174338930306773)
                    ·
                      refine ⟨73516565746273568679065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3136706805174338930306773 73516565746273568679065)
                      ·
                        rfl

theorem cell23_143173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_143173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143173 prefixEnd_143173 := by exact prefixLift 143173
  have htrace : WordTrace (prefixWord ++ tailWord_143173) baseStart_143173 baseEnd_143173 := by
    simpa [prefixWord, tailWord_143173, baseEnd_143173] using wordTrace_append hprefix tailTrace_143173
  have hstable : (prefixWord ++ tailWord_143173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143173).length < 2 ^ (prefixWord ++ tailWord_143173).sum := by decide
  have hdescent : baseEnd_143173 < baseStart_143173 := by decide
  rcases family_descends (prefixWord ++ tailWord_143173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143191 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 2, 2, 2]
def baseStart_143191 : Nat := 118140960795 + 143191 * 2 ^ 59
def prefixEnd_143191 : Nat := 4983230072969 + 3 ^ 40 * 143191 * 2
def baseEnd_143191 : Nat := 73525808398054498253983

theorem tailTrace_143191 : CollatzResearch.WordTrace tailWord_143191 prefixEnd_143191 73525808398054498253983 := by
  unfold tailWord_143191
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222604824250936920941427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3481736549500624613960951 5222604824250936920941427)
  ·
    refine ⟨7833907236376405381412141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5222604824250936920941427 7833907236376405381412141)
    ·
      refine ⟨2937715213641152018029553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7833907236376405381412141 2937715213641152018029553)
      ·
        refine ⟨2203286410230864013522165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2937715213641152018029553 2203286410230864013522165)
        ·
          refine ⟨206558100959143501267703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2203286410230864013522165 206558100959143501267703)
          ·
            refine ⟨309837151438715251901555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206558100959143501267703 309837151438715251901555)
            ·
              refine ⟨464755727158072877852333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309837151438715251901555 464755727158072877852333)
              ·
                refine ⟨174283397684277329194625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 464755727158072877852333 174283397684277329194625)
                ·
                  refine ⟨130712548263207996895969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174283397684277329194625 130712548263207996895969)
                  ·
                    refine ⟨98034411197405997671977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130712548263207996895969 98034411197405997671977)
                    ·
                      refine ⟨73525808398054498253983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98034411197405997671977 73525808398054498253983)
                      ·
                        rfl

theorem cell23_143191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_143191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143191 prefixEnd_143191 := by exact prefixLift 143191
  have htrace : WordTrace (prefixWord ++ tailWord_143191) baseStart_143191 baseEnd_143191 := by
    simpa [prefixWord, tailWord_143191, baseEnd_143191] using wordTrace_append hprefix tailTrace_143191
  have hstable : (prefixWord ++ tailWord_143191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143191).length < 2 ^ (prefixWord ++ tailWord_143191).sum := by decide
  have hdescent : baseEnd_143191 < baseStart_143191 := by decide
  rcases family_descends (prefixWord ++ tailWord_143191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143280 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3]
def baseStart_143280 : Nat := 118140960795 + 143280 * 2 ^ 59
def prefixEnd_143280 : Nat := 4983230072969 + 3 ^ 40 * 143280 * 2
def baseEnd_143280 : Nat := 73571508176304650041073

theorem tailTrace_143280 : CollatzResearch.WordTrace tailWord_143280 prefixEnd_143280 73571508176304650041073 := by
  unfold tailWord_143280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612925460464252560465647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3483900613952336747287529 2612925460464252560465647)
  ·
    refine ⟨3919388190696378840698471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2612925460464252560465647 3919388190696378840698471)
    ·
      refine ⟨5879082286044568261047707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3919388190696378840698471 5879082286044568261047707)
      ·
        refine ⟨8818623429066852391571561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5879082286044568261047707 8818623429066852391571561)
        ·
          refine ⟨6613967571800139293678671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8818623429066852391571561 6613967571800139293678671)
          ·
            refine ⟨9920951357700208940518007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613967571800139293678671 9920951357700208940518007)
            ·
              refine ⟨14881427036550313410777011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9920951357700208940518007 14881427036550313410777011)
              ·
                refine ⟨22322140554825470116165517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14881427036550313410777011 22322140554825470116165517)
                ·
                  refine ⟨8370802708059551293562069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22322140554825470116165517 8370802708059551293562069)
                  ·
                    refine ⟨196190688470145733442861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8370802708059551293562069 196190688470145733442861)
                    ·
                      refine ⟨73571508176304650041073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196190688470145733442861 73571508176304650041073)
                      ·
                        rfl

theorem cell23_143280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_143280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143280 prefixEnd_143280 := by exact prefixLift 143280
  have htrace : WordTrace (prefixWord ++ tailWord_143280) baseStart_143280 baseEnd_143280 := by
    simpa [prefixWord, tailWord_143280, baseEnd_143280] using wordTrace_append hprefix tailTrace_143280
  have hstable : (prefixWord ++ tailWord_143280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143280).length < 2 ^ (prefixWord ++ tailWord_143280).sum := by decide
  have hdescent : baseEnd_143280 < baseStart_143280 := by decide
  rcases family_descends (prefixWord ++ tailWord_143280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143304 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 6]
def baseStart_143304 : Nat := 118140960795 + 143304 * 2 ^ 59
def prefixEnd_143304 : Nat := 4983230072969 + 3 ^ 40 * 143304 * 2
def baseEnd_143304 : Nat := 8175981301334728460107

theorem tailTrace_143304 : CollatzResearch.WordTrace tailWord_143304 prefixEnd_143304 8175981301334728460107 := by
  unfold tailWord_143304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613363136420778609902483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3484484181894371479869977 2613363136420778609902483)
  ·
    refine ⟨3920044704631167914853725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613363136420778609902483 3920044704631167914853725)
    ·
      refine ⟨1470016764236687968070147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3920044704631167914853725 1470016764236687968070147)
      ·
        refine ⟨2205025146355031952105221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470016764236687968070147 2205025146355031952105221)
        ·
          refine ⟨413442214941568491019729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2205025146355031952105221 413442214941568491019729)
          ·
            refine ⟨310081661206176368264797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413442214941568491019729 310081661206176368264797)
            ·
              refine ⟨116280622952316138099299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 310081661206176368264797 116280622952316138099299)
              ·
                refine ⟨174420934428474207148949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116280622952316138099299 174420934428474207148949)
                ·
                  refine ⟨8175981301334728460107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174420934428474207148949 8175981301334728460107)
                  ·
                    rfl

theorem cell23_143304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 6].length) (baseStart_143304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143304 prefixEnd_143304 := by exact prefixLift 143304
  have htrace : WordTrace (prefixWord ++ tailWord_143304) baseStart_143304 baseEnd_143304 := by
    simpa [prefixWord, tailWord_143304, baseEnd_143304] using wordTrace_append hprefix tailTrace_143304
  have hstable : (prefixWord ++ tailWord_143304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143304).length < 2 ^ (prefixWord ++ tailWord_143304).sum := by decide
  have hdescent : baseEnd_143304 < baseStart_143304 := by decide
  rcases family_descends (prefixWord ++ tailWord_143304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143307 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 3, 5, 2]
def baseStart_143307 : Nat := 118140960795 + 143307 * 2 ^ 59
def prefixEnd_143307 : Nat := 4983230072969 + 3 ^ 40 * 143307 * 2
def baseEnd_143307 : Nat := 73585372153976044403449

theorem tailTrace_143307 : CollatzResearch.WordTrace tailWord_143307 prefixEnd_143307 73585372153976044403449 := by
  unfold tailWord_143307
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226835691830688732164175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3484557127887125821442783 5226835691830688732164175)
  ·
    refine ⟨7840253537746033098246263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5226835691830688732164175 7840253537746033098246263)
    ·
      refine ⟨11760380306619049647369395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7840253537746033098246263 11760380306619049647369395)
      ·
        refine ⟨17640570459928574471054093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11760380306619049647369395 17640570459928574471054093)
        ·
          refine ⟨6615213922473215426645285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17640570459928574471054093 6615213922473215426645285)
          ·
            refine ⟨1240352610463727892495991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6615213922473215426645285 1240352610463727892495991)
            ·
              refine ⟨1860528915695591838743987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240352610463727892495991 1860528915695591838743987)
              ·
                refine ⟨2790793373543387758115981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860528915695591838743987 2790793373543387758115981)
                ·
                  refine ⟨1046547515078770409293493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2790793373543387758115981 1046547515078770409293493)
                  ·
                    refine ⟨98113829538634725871265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1046547515078770409293493 98113829538634725871265)
                    ·
                      refine ⟨73585372153976044403449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98113829538634725871265 73585372153976044403449)
                      ·
                        rfl

theorem cell23_143307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5, 2].length) (baseStart_143307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143307 prefixEnd_143307 := by exact prefixLift 143307
  have htrace : WordTrace (prefixWord ++ tailWord_143307) baseStart_143307 baseEnd_143307 := by
    simpa [prefixWord, tailWord_143307, baseEnd_143307] using wordTrace_append hprefix tailTrace_143307
  have hstable : (prefixWord ++ tailWord_143307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143307).length < 2 ^ (prefixWord ++ tailWord_143307).sum := by decide
  have hdescent : baseEnd_143307 < baseStart_143307 := by decide
  rcases family_descends (prefixWord ++ tailWord_143307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143325 : List Nat := [1, 4, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_143325 : Nat := 118140960795 + 143325 * 2 ^ 59
def prefixEnd_143325 : Nat := 4983230072969 + 3 ^ 40 * 143325 * 2
def baseEnd_143325 : Nat := 24531538268585657992789

theorem tailTrace_143325 : CollatzResearch.WordTrace tailWord_143325 prefixEnd_143325 24531538268585657992789 := by
  unfold tailWord_143325
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227492205765477806319429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3484994803843651870879619 5227492205765477806319429)
  ·
    refine ⟨980154788581027088684893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5227492205765477806319429 980154788581027088684893)
    ·
      refine ⟨367558045717885158256835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 980154788581027088684893 367558045717885158256835)
      ·
        refine ⟨551337068576827737385253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367558045717885158256835 551337068576827737385253)
        ·
          refine ⟨103375700358155200759735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 551337068576827737385253 103375700358155200759735)
          ·
            refine ⟨155063550537232801139603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103375700358155200759735 155063550537232801139603)
            ·
              refine ⟨232595325805849201709405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155063550537232801139603 232595325805849201709405)
              ·
                refine ⟨87223247177193450641027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232595325805849201709405 87223247177193450641027)
                ·
                  refine ⟨130834870765790175961541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87223247177193450641027 130834870765790175961541)
                  ·
                    refine ⟨24531538268585657992789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130834870765790175961541 24531538268585657992789)
                    ·
                      rfl

theorem cell23_143325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_143325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143325 prefixEnd_143325 := by exact prefixLift 143325
  have htrace : WordTrace (prefixWord ++ tailWord_143325) baseStart_143325 baseEnd_143325 := by
    simpa [prefixWord, tailWord_143325, baseEnd_143325] using wordTrace_append hprefix tailTrace_143325
  have hstable : (prefixWord ++ tailWord_143325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143325).length < 2 ^ (prefixWord ++ tailWord_143325).sum := by decide
  have hdescent : baseEnd_143325 < baseStart_143325 := by decide
  rcases family_descends (prefixWord ++ tailWord_143325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143357 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_143357 : Nat := 118140960795 + 143357 * 2 ^ 59
def prefixEnd_143357 : Nat := 4983230072969 + 3 ^ 40 * 143357 * 2
def baseEnd_143357 : Nat := 73611046186700848778219

theorem tailTrace_143357 : CollatzResearch.WordTrace tailWord_143357 prefixEnd_143357 73611046186700848778219 := by
  unfold tailWord_143357
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228659341649547271484325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3485772894433031514322883 5228659341649547271484325)
  ·
    refine ⟨980373626559290113403311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5228659341649547271484325 980373626559290113403311)
    ·
      refine ⟨1470560439838935170104967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980373626559290113403311 1470560439838935170104967)
      ·
        refine ⟨2205840659758402755157451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470560439838935170104967 2205840659758402755157451)
        ·
          refine ⟨3308760989637604132736177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2205840659758402755157451 3308760989637604132736177)
          ·
            refine ⟨2481570742228203099552133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3308760989637604132736177 2481570742228203099552133)
            ·
              refine ⟨465294514167788081166025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2481570742228203099552133 465294514167788081166025)
              ·
                refine ⟨348970885625841060874519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465294514167788081166025 348970885625841060874519)
                ·
                  refine ⟨523456328438761591311779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348970885625841060874519 523456328438761591311779)
                  ·
                    refine ⟨785184492658142386967669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 523456328438761591311779 785184492658142386967669)
                    ·
                      refine ⟨73611046186700848778219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 785184492658142386967669 73611046186700848778219)
                      ·
                        rfl

theorem cell23_143357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_143357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143357 prefixEnd_143357 := by exact prefixLift 143357
  have htrace : WordTrace (prefixWord ++ tailWord_143357) baseStart_143357 baseEnd_143357 := by
    simpa [prefixWord, tailWord_143357, baseEnd_143357] using wordTrace_append hprefix tailTrace_143357
  have hstable : (prefixWord ++ tailWord_143357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143357).length < 2 ^ (prefixWord ++ tailWord_143357).sum := by decide
  have hdescent : baseEnd_143357 < baseStart_143357 := by decide
  rcases family_descends (prefixWord ++ tailWord_143357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143367 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_143367 : Nat := 118140960795 + 143367 * 2 ^ 59
def prefixEnd_143367 : Nat := 4983230072969 + 3 ^ 40 * 143367 * 2
def baseEnd_143367 : Nat := 73616180993245809653173

theorem tailTrace_143367 : CollatzResearch.WordTrace tailWord_143367 prefixEnd_143367 73616180993245809653173 := by
  unfold tailWord_143367
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229024071613318979348355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3486016047742212652898903 5229024071613318979348355)
  ·
    refine ⟨7843536107419978469022533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5229024071613318979348355 7843536107419978469022533)
    ·
      refine ⟨1470663020141245962941725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7843536107419978469022533 1470663020141245962941725)
      ·
        refine ⟨551498632552967236103147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1470663020141245962941725 551498632552967236103147)
        ·
          refine ⟨827247948829450854154721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551498632552967236103147 827247948829450854154721)
          ·
            refine ⟨620435961622088140616041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827247948829450854154721 620435961622088140616041)
            ·
              refine ⟨465326971216566105462031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620435961622088140616041 465326971216566105462031)
              ·
                refine ⟨697990456824849158193047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465326971216566105462031 697990456824849158193047)
                ·
                  refine ⟨1046985685237273737289571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697990456824849158193047 1046985685237273737289571)
                  ·
                    refine ⟨1570478527855910605934357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1046985685237273737289571 1570478527855910605934357)
                    ·
                      refine ⟨73616180993245809653173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1570478527855910605934357 73616180993245809653173)
                      ·
                        rfl

theorem cell23_143367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_143367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143367 prefixEnd_143367 := by exact prefixLift 143367
  have htrace : WordTrace (prefixWord ++ tailWord_143367) baseStart_143367 baseEnd_143367 := by
    simpa [prefixWord, tailWord_143367, baseEnd_143367] using wordTrace_append hprefix tailTrace_143367
  have hstable : (prefixWord ++ tailWord_143367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143367).length < 2 ^ (prefixWord ++ tailWord_143367).sum := by decide
  have hdescent : baseEnd_143367 < baseStart_143367 := by decide
  rcases family_descends (prefixWord ++ tailWord_143367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143374 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_143374 : Nat := 118140960795 + 143374 * 2 ^ 59
def prefixEnd_143374 : Nat := 4983230072969 + 3 ^ 40 * 143374 * 2
def baseEnd_143374 : Nat := 73619775357827282265641

theorem tailTrace_143374 : CollatzResearch.WordTrace tailWord_143374 prefixEnd_143374 73619775357827282265641 := by
  unfold tailWord_143374
  simp only [CollatzResearch.WordTrace]
  refine ⟨653659922823494896856647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3486186255058639449902117 653659922823494896856647)
  ·
    refine ⟨980489884235242345284971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 653659922823494896856647 980489884235242345284971)
    ·
      refine ⟨1470734826352863517927457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980489884235242345284971 1470734826352863517927457)
      ·
        refine ⟨1103051119764647638445593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1470734826352863517927457 1103051119764647638445593)
        ·
          refine ⟨827288339823485728834195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103051119764647638445593 827288339823485728834195)
          ·
            refine ⟨1240932509735228593251293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827288339823485728834195 1240932509735228593251293)
            ·
              refine ⟨465349691150710722469235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1240932509735228593251293 465349691150710722469235)
              ·
                refine ⟨698024536726066083703853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465349691150710722469235 698024536726066083703853)
                ·
                  refine ⟨261759201272274781388945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698024536726066083703853 261759201272274781388945)
                  ·
                    refine ⟨196319400954206086041709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 261759201272274781388945 196319400954206086041709)
                    ·
                      refine ⟨73619775357827282265641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196319400954206086041709 73619775357827282265641)
                      ·
                        rfl

theorem cell23_143374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_143374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143374 prefixEnd_143374 := by exact prefixLift 143374
  have htrace : WordTrace (prefixWord ++ tailWord_143374) baseStart_143374 baseEnd_143374 := by
    simpa [prefixWord, tailWord_143374, baseEnd_143374] using wordTrace_append hprefix tailTrace_143374
  have hstable : (prefixWord ++ tailWord_143374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143374).length < 2 ^ (prefixWord ++ tailWord_143374).sum := by decide
  have hdescent : baseEnd_143374 < baseStart_143374 := by decide
  rcases family_descends (prefixWord ++ tailWord_143374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143391 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 1, 2, 3]
def baseStart_143391 : Nat := 118140960795 + 143391 * 2 ^ 59
def prefixEnd_143391 : Nat := 4983230072969 + 3 ^ 40 * 143391 * 2
def baseEnd_143391 : Nat := 73628504528953715753063

theorem tailTrace_143391 : CollatzResearch.WordTrace tailWord_143391 prefixEnd_143391 73628504528953715753063 := by
  unfold tailWord_143391
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229899423526371078222027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3486599615684247385481351 5229899423526371078222027)
  ·
    refine ⟨7844849135289556617333041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5229899423526371078222027 7844849135289556617333041)
    ·
      refine ⟨5883636851467167462999781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7844849135289556617333041 5883636851467167462999781)
      ·
        refine ⟨1103181909650093899312459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5883636851467167462999781 1103181909650093899312459)
        ·
          refine ⟨1654772864475140848968689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103181909650093899312459 1654772864475140848968689)
          ·
            refine ⟨1241079648356355636726517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1654772864475140848968689 1241079648356355636726517)
            ·
              refine ⟨116351217033408340943111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1241079648356355636726517 116351217033408340943111)
              ·
                refine ⟨174526825550112511414667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116351217033408340943111 174526825550112511414667)
                ·
                  refine ⟨261790238325168767122001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174526825550112511414667 261790238325168767122001)
                  ·
                    refine ⟨196342678743876575341501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 261790238325168767122001 196342678743876575341501)
                    ·
                      refine ⟨73628504528953715753063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196342678743876575341501 73628504528953715753063)
                      ·
                        rfl

theorem cell23_143391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_143391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143391 prefixEnd_143391 := by exact prefixLift 143391
  have htrace : WordTrace (prefixWord ++ tailWord_143391) baseStart_143391 baseEnd_143391 := by
    simpa [prefixWord, tailWord_143391, baseEnd_143391] using wordTrace_append hprefix tailTrace_143391
  have hstable : (prefixWord ++ tailWord_143391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143391).length < 2 ^ (prefixWord ++ tailWord_143391).sum := by decide
  have hdescent : baseEnd_143391 < baseStart_143391 := by decide
  rcases family_descends (prefixWord ++ tailWord_143391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143399 : List Nat := [1, 1, 7, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_143399 : Nat := 118140960795 + 143399 * 2 ^ 59
def prefixEnd_143399 : Nat := 4983230072969 + 3 ^ 40 * 143399 * 2
def baseEnd_143399 : Nat := 73632612374189684453027

theorem tailTrace_143399 : CollatzResearch.WordTrace tailWord_143399 prefixEnd_143399 73632612374189684453027 := by
  unfold tailWord_143399
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230191207497388444513251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3486794138331592296342167 5230191207497388444513251)
  ·
    refine ⟨7845286811246082666769877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5230191207497388444513251 7845286811246082666769877)
    ·
      refine ⟨183873909638580062502419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7845286811246082666769877 183873909638580062502419)
      ·
        refine ⟨275810864457870093753629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183873909638580062502419 275810864457870093753629)
        ·
          refine ⟨103429074171701285157611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275810864457870093753629 103429074171701285157611)
          ·
            refine ⟨155143611257551927736417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103429074171701285157611 155143611257551927736417)
            ·
              refine ⟨116357708443163945802313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155143611257551927736417 116357708443163945802313)
              ·
                refine ⟨87268281332372959351735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116357708443163945802313 87268281332372959351735)
                ·
                  refine ⟨130902421998559439027603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87268281332372959351735 130902421998559439027603)
                  ·
                    refine ⟨196353632997839158541405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130902421998559439027603 196353632997839158541405)
                    ·
                      refine ⟨73632612374189684453027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196353632997839158541405 73632612374189684453027)
                      ·
                        rfl

theorem cell23_143399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_143399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143399 prefixEnd_143399 := by exact prefixLift 143399
  have htrace : WordTrace (prefixWord ++ tailWord_143399) baseStart_143399 baseEnd_143399 := by
    simpa [prefixWord, tailWord_143399, baseEnd_143399] using wordTrace_append hprefix tailTrace_143399
  have hstable : (prefixWord ++ tailWord_143399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143399).length < 2 ^ (prefixWord ++ tailWord_143399).sum := by decide
  have hdescent : baseEnd_143399 < baseStart_143399 := by decide
  rcases family_descends (prefixWord ++ tailWord_143399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143421 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_143421 : Nat := 118140960795 + 143421 * 2 ^ 59
def prefixEnd_143421 : Nat := 4983230072969 + 3 ^ 40 * 143421 * 2
def baseEnd_143421 : Nat := 73643908948588598377925

theorem tailTrace_143421 : CollatzResearch.WordTrace tailWord_143421 prefixEnd_143421 73643908948588598377925 := by
  unfold tailWord_143421
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230993613417686201814117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3487329075611790801209411 5230993613417686201814117)
  ·
    refine ⟨980811302515816162840147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5230993613417686201814117 980811302515816162840147)
    ·
      refine ⟨1471216953773724244260221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980811302515816162840147 1471216953773724244260221)
      ·
        refine ⟨551706357665146591597583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1471216953773724244260221 551706357665146591597583)
        ·
          refine ⟨827559536497719887396375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551706357665146591597583 827559536497719887396375)
          ·
            refine ⟨1241339304746579831094563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827559536497719887396375 1241339304746579831094563)
            ·
              refine ⟨1862008957119869746641845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241339304746579831094563 1862008957119869746641845)
              ·
                refine ⟨174563339729987788747673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1862008957119869746641845 174563339729987788747673)
                ·
                  refine ⟨130922504797490841560755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174563339729987788747673 130922504797490841560755)
                  ·
                    refine ⟨196383757196236262341133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130922504797490841560755 196383757196236262341133)
                    ·
                      refine ⟨73643908948588598377925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196383757196236262341133 73643908948588598377925)
                      ·
                        rfl

theorem cell23_143421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_143421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143421 prefixEnd_143421 := by exact prefixLift 143421
  have htrace : WordTrace (prefixWord ++ tailWord_143421) baseStart_143421 baseEnd_143421 := by
    simpa [prefixWord, tailWord_143421, baseEnd_143421] using wordTrace_append hprefix tailTrace_143421
  have hstable : (prefixWord ++ tailWord_143421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143421).length < 2 ^ (prefixWord ++ tailWord_143421).sum := by decide
  have hdescent : baseEnd_143421 < baseStart_143421 := by decide
  rcases family_descends (prefixWord ++ tailWord_143421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143431 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_143431 : Nat := 118140960795 + 143431 * 2 ^ 59
def prefixEnd_143431 : Nat := 4983230072969 + 3 ^ 40 * 143431 * 2
def baseEnd_143431 : Nat := 73649043755133559252879

theorem tailTrace_143431 : CollatzResearch.WordTrace tailWord_143431 prefixEnd_143431 73649043755133559252879 := by
  unfold tailWord_143431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5231358343381457909678147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3487572228920971939785431 5231358343381457909678147)
  ·
    refine ⟨7847037515072186864517221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5231358343381457909678147 7847037515072186864517221)
    ·
      refine ⟨1471319534076035037096979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7847037515072186864517221 1471319534076035037096979)
      ·
        refine ⟨2206979301114052555645469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471319534076035037096979 2206979301114052555645469)
        ·
          refine ⟨827617237917769708367051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2206979301114052555645469 827617237917769708367051)
          ·
            refine ⟨1241425856876654562550577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827617237917769708367051 1241425856876654562550577)
            ·
              refine ⟨931069392657490921912933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241425856876654562550577 931069392657490921912933)
              ·
                refine ⟨174575511123279547858675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 931069392657490921912933 174575511123279547858675)
                ·
                  refine ⟨261863266684919321788013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174575511123279547858675 261863266684919321788013)
                  ·
                    refine ⟨98198725006844745670505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261863266684919321788013 98198725006844745670505)
                    ·
                      refine ⟨73649043755133559252879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98198725006844745670505 73649043755133559252879)
                      ·
                        rfl

theorem cell23_143431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_143431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143431 prefixEnd_143431 := by exact prefixLift 143431
  have htrace : WordTrace (prefixWord ++ tailWord_143431) baseStart_143431 baseEnd_143431 := by
    simpa [prefixWord, tailWord_143431, baseEnd_143431] using wordTrace_append hprefix tailTrace_143431
  have hstable : (prefixWord ++ tailWord_143431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143431).length < 2 ^ (prefixWord ++ tailWord_143431).sum := by decide
  have hdescent : baseEnd_143431 < baseStart_143431 := by decide
  rcases family_descends (prefixWord ++ tailWord_143431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143447 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_143447 : Nat := 118140960795 + 143447 * 2 ^ 59
def prefixEnd_143447 : Nat := 4983230072969 + 3 ^ 40 * 143447 * 2
def baseEnd_143447 : Nat := 73657259445605496652805

theorem tailTrace_143447 : CollatzResearch.WordTrace tailWord_143447 prefixEnd_143447 73657259445605496652805 := by
  unfold tailWord_143447
  simp only [CollatzResearch.WordTrace]
  refine ⟨5231941911323492642260595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3487961274215661761507063 5231941911323492642260595)
  ·
    refine ⟨7847912866985238963390893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5231941911323492642260595 7847912866985238963390893)
    ·
      refine ⟨2942967325119464611271585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7847912866985238963390893 2942967325119464611271585)
      ·
        refine ⟨2207225493839598458453689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2942967325119464611271585 2207225493839598458453689)
        ·
          refine ⟨1655419120379698843840267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2207225493839598458453689 1655419120379698843840267)
          ·
            refine ⟨2483128680569548265760401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655419120379698843840267 2483128680569548265760401)
            ·
              refine ⟨1862346510427161199320301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2483128680569548265760401 1862346510427161199320301)
              ·
                refine ⟨698379941410185449745113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1862346510427161199320301 698379941410185449745113)
                ·
                  refine ⟨523784956057639087308835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 698379941410185449745113 523784956057639087308835)
                  ·
                    refine ⟨785677434086458630963253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 523784956057639087308835 785677434086458630963253)
                    ·
                      refine ⟨73657259445605496652805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 785677434086458630963253 73657259445605496652805)
                      ·
                        rfl

theorem cell23_143447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_143447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143447 prefixEnd_143447 := by exact prefixLift 143447
  have htrace : WordTrace (prefixWord ++ tailWord_143447) baseStart_143447 baseEnd_143447 := by
    simpa [prefixWord, tailWord_143447, baseEnd_143447] using wordTrace_append hprefix tailTrace_143447
  have hstable : (prefixWord ++ tailWord_143447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143447).length < 2 ^ (prefixWord ++ tailWord_143447).sum := by decide
  have hdescent : baseEnd_143447 < baseStart_143447 := by decide
  rcases family_descends (prefixWord ++ tailWord_143447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143448 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 1, 3, 2]
def baseStart_143448 : Nat := 118140960795 + 143448 * 2 ^ 59
def prefixEnd_143448 : Nat := 4983230072969 + 3 ^ 40 * 143448 * 2
def baseEnd_143448 : Nat := 73657772926259992740301

theorem tailTrace_143448 : CollatzResearch.WordTrace tailWord_143448 prefixEnd_143448 73657772926259992740301 := by
  unfold tailWord_143448
  simp only [CollatzResearch.WordTrace]
  refine ⟨2615989192159934906523499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3487985589546579875364665 2615989192159934906523499)
  ·
    refine ⟨3923983788239902359785249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2615989192159934906523499 3923983788239902359785249)
    ·
      refine ⟨2942987841179926769838937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3923983788239902359785249 2942987841179926769838937)
      ·
        refine ⟨2207240880884945077379203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2942987841179926769838937 2207240880884945077379203)
        ·
          refine ⟨3310861321327417616068805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207240880884945077379203 3310861321327417616068805)
          ·
            refine ⟨620786497748890803012901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3310861321327417616068805 620786497748890803012901)
            ·
              refine ⟨116397468327917025564919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 620786497748890803012901 116397468327917025564919)
              ·
                refine ⟨174596202491875538347379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116397468327917025564919 174596202491875538347379)
                ·
                  refine ⟨261894303737813307521069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174596202491875538347379 261894303737813307521069)
                  ·
                    refine ⟨98210363901679990320401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261894303737813307521069 98210363901679990320401)
                    ·
                      refine ⟨73657772926259992740301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98210363901679990320401 73657772926259992740301)
                      ·
                        rfl

theorem cell23_143448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_143448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143448 prefixEnd_143448 := by exact prefixLift 143448
  have htrace : WordTrace (prefixWord ++ tailWord_143448) baseStart_143448 baseEnd_143448 := by
    simpa [prefixWord, tailWord_143448, baseEnd_143448] using wordTrace_append hprefix tailTrace_143448
  have hstable : (prefixWord ++ tailWord_143448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143448).length < 2 ^ (prefixWord ++ tailWord_143448).sum := by decide
  have hdescent : baseEnd_143448 < baseStart_143448 := by decide
  rcases family_descends (prefixWord ++ tailWord_143448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143474 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_143474 : Nat := 118140960795 + 143474 * 2 ^ 59
def prefixEnd_143474 : Nat := 4983230072969 + 3 ^ 40 * 143474 * 2
def baseEnd_143474 : Nat := 73671123423276891015181

theorem tailTrace_143474 : CollatzResearch.WordTrace tailWord_143474 prefixEnd_143474 73671123423276891015181 := by
  unfold tailWord_143474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308231670556419063373369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3488617788150450835662317 1308231670556419063373369)
  ·
    refine ⟨981173752917314297530027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1308231670556419063373369 981173752917314297530027)
    ·
      refine ⟨1471760629375971446295041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981173752917314297530027 1471760629375971446295041)
      ·
        refine ⟨1103820472031978584721281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1471760629375971446295041 1103820472031978584721281)
        ·
          refine ⟨827865354023983938540961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103820472031978584721281 827865354023983938540961)
          ·
            refine ⟨620899015517987953905721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827865354023983938540961 620899015517987953905721)
            ·
              refine ⟨465674261638490965429291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620899015517987953905721 465674261638490965429291)
              ·
                refine ⟨698511392457736448143937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465674261638490965429291 698511392457736448143937)
                ·
                  refine ⟨523883544343302336107953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 698511392457736448143937 523883544343302336107953)
                  ·
                    refine ⟨392912658257476752080965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 523883544343302336107953 392912658257476752080965)
                    ·
                      refine ⟨73671123423276891015181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 392912658257476752080965 73671123423276891015181)
                      ·
                        rfl

theorem cell23_143474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_143474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143474 prefixEnd_143474 := by exact prefixLift 143474
  have htrace : WordTrace (prefixWord ++ tailWord_143474) baseStart_143474 baseEnd_143474 := by
    simpa [prefixWord, tailWord_143474, baseEnd_143474] using wordTrace_append hprefix tailTrace_143474
  have hstable : (prefixWord ++ tailWord_143474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143474).length < 2 ^ (prefixWord ++ tailWord_143474).sum := by decide
  have hdescent : baseEnd_143474 < baseStart_143474 := by decide
  rcases family_descends (prefixWord ++ tailWord_143474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143478 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_143478 : Nat := 118140960795 + 143478 * 2 ^ 59
def prefixEnd_143478 : Nat := 4983230072969 + 3 ^ 40 * 143478 * 2
def baseEnd_143478 : Nat := 73673177345894875365163

theorem tailTrace_143478 : CollatzResearch.WordTrace tailWord_143478 prefixEnd_143478 73673177345894875365163 := by
  unfold tailWord_143478
  simp only [CollatzResearch.WordTrace]
  refine ⟨327067035888199058539943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3488715049474123291092725 327067035888199058539943)
  ·
    refine ⟨490600553832298587809915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 327067035888199058539943 490600553832298587809915)
    ·
      refine ⟨735900830748447881714873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490600553832298587809915 735900830748447881714873)
      ·
        refine ⟨551925623061335911286155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 735900830748447881714873 551925623061335911286155)
        ·
          refine ⟨827888434592003866929233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551925623061335911286155 827888434592003866929233)
          ·
            refine ⟨620916325944002900196925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827888434592003866929233 620916325944002900196925)
            ·
              refine ⟨232843622229001087573847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620916325944002900196925 232843622229001087573847)
              ·
                refine ⟨349265433343501631360771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232843622229001087573847 349265433343501631360771)
                ·
                  refine ⟨523898150015252447041157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349265433343501631360771 523898150015252447041157)
                  ·
                    refine ⟨98230903127859833820217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 523898150015252447041157 98230903127859833820217)
                    ·
                      refine ⟨73673177345894875365163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98230903127859833820217 73673177345894875365163)
                      ·
                        rfl

theorem cell23_143478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_143478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143478 prefixEnd_143478 := by exact prefixLift 143478
  have htrace : WordTrace (prefixWord ++ tailWord_143478) baseStart_143478 baseEnd_143478 := by
    simpa [prefixWord, tailWord_143478, baseEnd_143478] using wordTrace_append hprefix tailTrace_143478
  have hstable : (prefixWord ++ tailWord_143478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143478).length < 2 ^ (prefixWord ++ tailWord_143478).sum := by decide
  have hdescent : baseEnd_143478 < baseStart_143478 := by decide
  rcases family_descends (prefixWord ++ tailWord_143478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143497 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 1, 7]
def baseStart_143497 : Nat := 118140960795 + 143497 * 2 ^ 59
def prefixEnd_143497 : Nat := 4983230072969 + 3 ^ 40 * 143497 * 2
def baseEnd_143497 : Nat := 24560977826110100342525

theorem tailTrace_143497 : CollatzResearch.WordTrace tailWord_143497 prefixEnd_143497 24560977826110100342525 := by
  unfold tailWord_143497
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233765561142351181580745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3489177040761567454387163 5233765561142351181580745)
  ·
    refine ⟨3925324170856763386185559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5233765561142351181580745 3925324170856763386185559)
    ·
      refine ⟨5887986256285145079278339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3925324170856763386185559 5887986256285145079278339)
      ·
        refine ⟨8831979384427717618917509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5887986256285145079278339 8831979384427717618917509)
        ·
          refine ⟨1655996134580197053547033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8831979384427717618917509 1655996134580197053547033)
          ·
            refine ⟨1241997100935147790160275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1655996134580197053547033 1241997100935147790160275)
            ·
              refine ⟨1862995651402721685240413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241997100935147790160275 1862995651402721685240413)
              ·
                refine ⟨698623369276020631965155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1862995651402721685240413 698623369276020631965155)
                ·
                  refine ⟨1047935053914030947947733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698623369276020631965155 1047935053914030947947733)
                  ·
                    refine ⟨24560977826110100342525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1047935053914030947947733 24560977826110100342525)
                    ·
                      rfl

theorem cell23_143497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_143497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143497 prefixEnd_143497 := by exact prefixLift 143497
  have htrace : WordTrace (prefixWord ++ tailWord_143497) baseStart_143497 baseEnd_143497 := by
    simpa [prefixWord, tailWord_143497, baseEnd_143497] using wordTrace_append hprefix tailTrace_143497
  have hstable : (prefixWord ++ tailWord_143497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143497).length < 2 ^ (prefixWord ++ tailWord_143497).sum := by decide
  have hdescent : baseEnd_143497 < baseStart_143497 := by decide
  rcases family_descends (prefixWord ++ tailWord_143497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143507 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5]
def baseStart_143507 : Nat := 118140960795 + 143507 * 2 ^ 59
def prefixEnd_143507 : Nat := 4983230072969 + 3 ^ 40 * 143507 * 2
def baseEnd_143507 : Nat := 73688068284875261902529

theorem tailTrace_143507 : CollatzResearch.WordTrace tailWord_143507 prefixEnd_143507 73688068284875261902529 := by
  unfold tailWord_143507
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234130291106122889444775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3489420194070748592963183 5234130291106122889444775)
  ·
    refine ⟨7851195436659184334167163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5234130291106122889444775 7851195436659184334167163)
    ·
      refine ⟨11776793154988776501250745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7851195436659184334167163 11776793154988776501250745)
      ·
        refine ⟨8832594866241582375938059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11776793154988776501250745 8832594866241582375938059)
        ·
          refine ⟨13248892299362373563907089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8832594866241582375938059 13248892299362373563907089)
          ·
            refine ⟨9936669224521780172930317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13248892299362373563907089 9936669224521780172930317)
            ·
              refine ⟨3726250959195667564848869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9936669224521780172930317 3726250959195667564848869)
              ·
                refine ⟨698672054849187668409163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3726250959195667564848869 698672054849187668409163)
                ·
                  refine ⟨1048008082273781502613745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698672054849187668409163 1048008082273781502613745)
                  ·
                    refine ⟨786006061705336126960309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1048008082273781502613745 786006061705336126960309)
                    ·
                      refine ⟨73688068284875261902529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 786006061705336126960309 73688068284875261902529)
                      ·
                        rfl

theorem cell23_143507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_143507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143507 prefixEnd_143507 := by exact prefixLift 143507
  have htrace : WordTrace (prefixWord ++ tailWord_143507) baseStart_143507 baseEnd_143507 := by
    simpa [prefixWord, tailWord_143507, baseEnd_143507] using wordTrace_append hprefix tailTrace_143507
  have hstable : (prefixWord ++ tailWord_143507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143507).length < 2 ^ (prefixWord ++ tailWord_143507).sum := by decide
  have hdescent : baseEnd_143507 < baseStart_143507 := by decide
  rcases family_descends (prefixWord ++ tailWord_143507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143518 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_143518 : Nat := 118140960795 + 143518 * 2 ^ 59
def prefixEnd_143518 : Nat := 4983230072969 + 3 ^ 40 * 143518 * 2
def baseEnd_143518 : Nat := 8188190730230524318331

theorem tailTrace_143518 : CollatzResearch.WordTrace tailWord_143518 prefixEnd_143518 8188190730230524318331 := by
  unfold tailWord_143518
  simp only [CollatzResearch.WordTrace]
  refine ⟨654316436758283971011901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3489687662710847845396805 654316436758283971011901)
  ·
    refine ⟨245368663784356489129463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 654316436758283971011901 245368663784356489129463)
    ·
      refine ⟨368052995676534733694195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245368663784356489129463 368052995676534733694195)
      ·
        refine ⟨552079493514802100541293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368052995676534733694195 552079493514802100541293)
        ·
          refine ⟨207029810068050787702985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 552079493514802100541293 207029810068050787702985)
          ·
            refine ⟨155272357551038090777239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207029810068050787702985 155272357551038090777239)
            ·
              refine ⟨232908536326557136165859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155272357551038090777239 232908536326557136165859)
              ·
                refine ⟨349362804489835704248789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232908536326557136165859 349362804489835704248789)
                ·
                  refine ⟨8188190730230524318331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 349362804489835704248789 8188190730230524318331)
                  ·
                    rfl

theorem cell23_143518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_143518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143518 prefixEnd_143518 := by exact prefixLift 143518
  have htrace : WordTrace (prefixWord ++ tailWord_143518) baseStart_143518 baseEnd_143518 := by
    simpa [prefixWord, tailWord_143518, baseEnd_143518] using wordTrace_append hprefix tailTrace_143518
  have hstable : (prefixWord ++ tailWord_143518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143518).length < 2 ^ (prefixWord ++ tailWord_143518).sum := by decide
  have hdescent : baseEnd_143518 < baseStart_143518 := by decide
  rcases family_descends (prefixWord ++ tailWord_143518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143544 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 5, 4]
def baseStart_143544 : Nat := 118140960795 + 143544 * 2 ^ 59
def prefixEnd_143544 : Nat := 4983230072969 + 3 ^ 40 * 143544 * 2
def baseEnd_143544 : Nat := 24569022356363872379953

theorem tailTrace_143544 : CollatzResearch.WordTrace tailWord_143544 prefixEnd_143544 24569022356363872379953 := by
  unfold tailWord_143544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617739895986039104270843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3490319861314718805694457 2617739895986039104270843)
  ·
    refine ⟨3926609843979058656406265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2617739895986039104270843 3926609843979058656406265)
    ·
      refine ⟨2944957382984293992304699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3926609843979058656406265 2944957382984293992304699)
      ·
        refine ⟨4417436074476440988457049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2944957382984293992304699 4417436074476440988457049)
        ·
          refine ⟨3313077055857330741342787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4417436074476440988457049 3313077055857330741342787)
          ·
            refine ⟨4969615583785996112014181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313077055857330741342787 4969615583785996112014181)
            ·
              refine ⟨931802921959874271002659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4969615583785996112014181 931802921959874271002659)
              ·
                refine ⟨1397704382939811406503989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931802921959874271002659 1397704382939811406503989)
                ·
                  refine ⟨131034785900607319359749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1397704382939811406503989 131034785900607319359749)
                  ·
                    refine ⟨24569022356363872379953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131034785900607319359749 24569022356363872379953)
                    ·
                      rfl

theorem cell23_143544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_143544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143544 prefixEnd_143544 := by exact prefixLift 143544
  have htrace : WordTrace (prefixWord ++ tailWord_143544) baseStart_143544 baseEnd_143544 := by
    simpa [prefixWord, tailWord_143544, baseEnd_143544] using wordTrace_append hprefix tailTrace_143544
  have hstable : (prefixWord ++ tailWord_143544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143544).length < 2 ^ (prefixWord ++ tailWord_143544).sum := by decide
  have hdescent : baseEnd_143544 < baseStart_143544 := by decide
  rcases family_descends (prefixWord ++ tailWord_143544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143557 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 10]
def baseStart_143557 : Nat := 118140960795 + 143557 * 2 ^ 59
def prefixEnd_143557 : Nat := 4983230072969 + 3 ^ 40 * 143557 * 2
def baseEnd_143557 : Nat := 8190415813066674030811

theorem tailTrace_143557 : CollatzResearch.WordTrace tailWord_143557 prefixEnd_143557 8190415813066674030811 := by
  unfold tailWord_143557
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235953940924981428764925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3490635960616654285843283 5235953940924981428764925)
  ·
    refine ⟨1963482727846868035786847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5235953940924981428764925 1963482727846868035786847)
    ·
      refine ⟨2945224091770302053680271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963482727846868035786847 2945224091770302053680271)
      ·
        refine ⟨4417836137655453080520407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945224091770302053680271 4417836137655453080520407)
        ·
          refine ⟨6626754206483179620780611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4417836137655453080520407 6626754206483179620780611)
          ·
            refine ⟨9940131309724769431170917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6626754206483179620780611 9940131309724769431170917)
            ·
              refine ⟨1863774620573394268344547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9940131309724769431170917 1863774620573394268344547)
              ·
                refine ⟨2795661930860091402516821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863774620573394268344547 2795661930860091402516821)
                ·
                  refine ⟨8190415813066674030811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2795661930860091402516821 8190415813066674030811)
                  ·
                    rfl

theorem cell23_143557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_143557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143557 prefixEnd_143557 := by exact prefixLift 143557
  have htrace : WordTrace (prefixWord ++ tailWord_143557) baseStart_143557 baseEnd_143557 := by
    simpa [prefixWord, tailWord_143557, baseEnd_143557] using wordTrace_append hprefix tailTrace_143557
  have hstable : (prefixWord ++ tailWord_143557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143557).length < 2 ^ (prefixWord ++ tailWord_143557).sum := by decide
  have hdescent : baseEnd_143557 < baseStart_143557 := by decide
  rcases family_descends (prefixWord ++ tailWord_143557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143591 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 6]
def baseStart_143591 : Nat := 118140960795 + 143591 * 2 ^ 59
def prefixEnd_143591 : Nat := 4983230072969 + 3 ^ 40 * 143591 * 2
def baseEnd_143591 : Nat := 8192355628872548139127

theorem tailTrace_143591 : CollatzResearch.WordTrace tailWord_143591 prefixEnd_143591 8192355628872548139127 := by
  unfold tailWord_143591
  simp only [CollatzResearch.WordTrace]
  refine ⟨5237194022801805235502627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3491462681867870157001751 5237194022801805235502627)
  ·
    refine ⟨7855791034202707853253941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5237194022801805235502627 7855791034202707853253941)
    ·
      refine ⟨736480409456503861242557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7855791034202707853253941 736480409456503861242557)
      ·
        refine ⟨276180153546188947965959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 736480409456503861242557 276180153546188947965959)
        ·
          refine ⟨414270230319283421948939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276180153546188947965959 414270230319283421948939)
          ·
            refine ⟨621405345478925132923409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414270230319283421948939 621405345478925132923409)
            ·
              refine ⟨466054009109193849692557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621405345478925132923409 466054009109193849692557)
              ·
                refine ⟨174770253415947693634709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466054009109193849692557 174770253415947693634709)
                ·
                  refine ⟨8192355628872548139127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174770253415947693634709 8192355628872548139127)
                  ·
                    rfl

theorem cell23_143591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 6].length) (baseStart_143591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143591 prefixEnd_143591 := by exact prefixLift 143591
  have htrace : WordTrace (prefixWord ++ tailWord_143591) baseStart_143591 baseEnd_143591 := by
    simpa [prefixWord, tailWord_143591, baseEnd_143591] using wordTrace_append hprefix tailTrace_143591
  have hstable : (prefixWord ++ tailWord_143591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143591).length < 2 ^ (prefixWord ++ tailWord_143591).sum := by decide
  have hdescent : baseEnd_143591 < baseStart_143591 := by decide
  rcases family_descends (prefixWord ++ tailWord_143591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143601 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_143601 : Nat := 118140960795 + 143601 * 2 ^ 59
def prefixEnd_143601 : Nat := 4983230072969 + 3 ^ 40 * 143601 * 2
def baseEnd_143601 : Nat := 73736335466397894127097

theorem tailTrace_143601 : CollatzResearch.WordTrace tailWord_143601 prefixEnd_143601 73736335466397894127097 := by
  unfold tailWord_143601
  simp only [CollatzResearch.WordTrace]
  refine ⟨5237558752765576943366657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3491705835177051295577771 5237558752765576943366657)
  ·
    refine ⟨3928169064574182707524993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5237558752765576943366657 3928169064574182707524993)
    ·
      refine ⟨2946126798430637030643745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3928169064574182707524993 2946126798430637030643745)
      ·
        refine ⟨2209595098822977772982809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2946126798430637030643745 2209595098822977772982809)
        ·
          refine ⟨1657196324117233329737107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2209595098822977772982809 1657196324117233329737107)
          ·
            refine ⟨2485794486175849994605661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657196324117233329737107 2485794486175849994605661)
            ·
              refine ⟨932172932315943747977123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2485794486175849994605661 932172932315943747977123)
              ·
                refine ⟨1398259398473915621965685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932172932315943747977123 1398259398473915621965685)
                ·
                  refine ⟨131086818606929589559283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1398259398473915621965685 131086818606929589559283)
                  ·
                    refine ⟨196630227910394384338925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131086818606929589559283 196630227910394384338925)
                    ·
                      refine ⟨73736335466397894127097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196630227910394384338925 73736335466397894127097)
                      ·
                        rfl

theorem cell23_143601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_143601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143601 prefixEnd_143601 := by exact prefixLift 143601
  have htrace : WordTrace (prefixWord ++ tailWord_143601) baseStart_143601 baseEnd_143601 := by
    simpa [prefixWord, tailWord_143601, baseEnd_143601] using wordTrace_append hprefix tailTrace_143601
  have hstable : (prefixWord ++ tailWord_143601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143601).length < 2 ^ (prefixWord ++ tailWord_143601).sum := by decide
  have hdescent : baseEnd_143601 < baseStart_143601 := by decide
  rcases family_descends (prefixWord ++ tailWord_143601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143668 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_143668 : Nat := 118140960795 + 143668 * 2 ^ 59
def prefixEnd_143668 : Nat := 4983230072969 + 3 ^ 40 * 143668 * 2
def baseEnd_143668 : Nat := 24590246223416377329763

theorem tailTrace_143668 : CollatzResearch.WordTrace tailWord_143668 prefixEnd_143668 24590246223416377329763 := by
  unfold tailWord_143668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620001221761423693027829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3493334962348564924037105 2620001221761423693027829)
  ·
    refine ⟨245625114540133471221359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2620001221761423693027829 245625114540133471221359)
    ·
      refine ⟨368437671810200206832039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245625114540133471221359 368437671810200206832039)
      ·
        refine ⟨552656507715300310248059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368437671810200206832039 552656507715300310248059)
        ·
          refine ⟨828984761572950465372089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552656507715300310248059 828984761572950465372089)
          ·
            refine ⟨621738571179712849029067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828984761572950465372089 621738571179712849029067)
            ·
              refine ⟨932607856769569273543601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621738571179712849029067 932607856769569273543601)
              ·
                refine ⟨699455892577176955157701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932607856769569273543601 699455892577176955157701)
                ·
                  refine ⟨131147979858220679092069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 699455892577176955157701 131147979858220679092069)
                  ·
                    refine ⟨24590246223416377329763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131147979858220679092069 24590246223416377329763)
                    ·
                      rfl

theorem cell23_143668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_143668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143668 prefixEnd_143668 := by exact prefixLift 143668
  have htrace : WordTrace (prefixWord ++ tailWord_143668) baseStart_143668 baseEnd_143668 := by
    simpa [prefixWord, tailWord_143668, baseEnd_143668] using wordTrace_append hprefix tailTrace_143668
  have hstable : (prefixWord ++ tailWord_143668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143668).length < 2 ^ (prefixWord ++ tailWord_143668).sum := by decide
  have hdescent : baseEnd_143668 < baseStart_143668 := by decide
  rcases family_descends (prefixWord ++ tailWord_143668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143678 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_143678 : Nat := 118140960795 + 143678 * 2 ^ 59
def prefixEnd_143678 : Nat := 4983230072969 + 3 ^ 40 * 143678 * 2
def baseEnd_143678 : Nat := 73775873476794092864243

theorem tailTrace_143678 : CollatzResearch.WordTrace tailWord_143678 prefixEnd_143678 73775873476794092864243 := by
  unfold tailWord_143678
  simp only [CollatzResearch.WordTrace]
  refine ⟨655045896685827386739961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3493578115657746062613125 655045896685827386739961)
  ·
    refine ⟨491284422514370540054971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 655045896685827386739961 491284422514370540054971)
    ·
      refine ⟨736926633771555810082457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491284422514370540054971 736926633771555810082457)
      ·
        refine ⟨552694975328666857561843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 736926633771555810082457 552694975328666857561843)
        ·
          refine ⟨829042462993000286342765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552694975328666857561843 829042462993000286342765)
          ·
            refine ⟨310890923622375107378537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 829042462993000286342765 310890923622375107378537)
            ·
              refine ⟨233168192716781330533903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310890923622375107378537 233168192716781330533903)
              ·
                refine ⟨349752289075171995800855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233168192716781330533903 349752289075171995800855)
                ·
                  refine ⟨524628433612757993701283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349752289075171995800855 524628433612757993701283)
                  ·
                    refine ⟨786942650419136990551925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 524628433612757993701283 786942650419136990551925)
                    ·
                      refine ⟨73775873476794092864243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 786942650419136990551925 73775873476794092864243)
                      ·
                        rfl

theorem cell23_143678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_143678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143678 prefixEnd_143678 := by exact prefixLift 143678
  have htrace : WordTrace (prefixWord ++ tailWord_143678) baseStart_143678 baseEnd_143678 := by
    simpa [prefixWord, tailWord_143678, baseEnd_143678] using wordTrace_append hprefix tailTrace_143678
  have hstable : (prefixWord ++ tailWord_143678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143678).length < 2 ^ (prefixWord ++ tailWord_143678).sum := by decide
  have hdescent : baseEnd_143678 < baseStart_143678 := by decide
  rcases family_descends (prefixWord ++ tailWord_143678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143704 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_143704 : Nat := 118140960795 + 143704 * 2 ^ 59
def prefixEnd_143704 : Nat := 4983230072969 + 3 ^ 40 * 143704 * 2
def baseEnd_143704 : Nat := 73789223973810991139123

theorem tailTrace_143704 : CollatzResearch.WordTrace tailWord_143704 prefixEnd_143704 73789223973810991139123 := by
  unfold tailWord_143704
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620657735696212767183083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3494210314261617022910777 2620657735696212767183083)
  ·
    refine ⟨3930986603544319150774625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2620657735696212767183083 3930986603544319150774625)
    ·
      refine ⟨2948239952658239363080969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3930986603544319150774625 2948239952658239363080969)
      ·
        refine ⟨2211179964493679522310727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2948239952658239363080969 2211179964493679522310727)
        ·
          refine ⟨3316769946740519283466091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211179964493679522310727 3316769946740519283466091)
          ·
            refine ⟨4975154920110778925199137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316769946740519283466091 4975154920110778925199137)
            ·
              refine ⟨3731366190083084193899353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975154920110778925199137 3731366190083084193899353)
              ·
                refine ⟨2798524642562313145424515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3731366190083084193899353 2798524642562313145424515)
                ·
                  refine ⟨4197786963843469718136773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798524642562313145424515 4197786963843469718136773)
                  ·
                    refine ⟨787085055720650572150645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197786963843469718136773 787085055720650572150645)
                    ·
                      refine ⟨73789223973810991139123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 787085055720650572150645 73789223973810991139123)
                      ·
                        rfl

theorem cell23_143704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_143704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143704 prefixEnd_143704 := by exact prefixLift 143704
  have htrace : WordTrace (prefixWord ++ tailWord_143704) baseStart_143704 baseEnd_143704 := by
    simpa [prefixWord, tailWord_143704, baseEnd_143704] using wordTrace_append hprefix tailTrace_143704
  have hstable : (prefixWord ++ tailWord_143704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143704).length < 2 ^ (prefixWord ++ tailWord_143704).sum := by decide
  have hdescent : baseEnd_143704 < baseStart_143704 := by decide
  rcases family_descends (prefixWord ++ tailWord_143704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143712 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 1, 2, 3]
def baseStart_143712 : Nat := 118140960795 + 143712 * 2 ^ 59
def prefixEnd_143712 : Nat := 4983230072969 + 3 ^ 40 * 143712 * 2
def baseEnd_143712 : Nat := 73793331819046959839087

theorem tailTrace_143712 : CollatzResearch.WordTrace tailWord_143712 prefixEnd_143712 73793331819046959839087 := by
  unfold tailWord_143712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620803627681721450328695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3494404836908961933771593 2620803627681721450328695)
  ·
    refine ⟨3931205441522582175493043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2620803627681721450328695 3931205441522582175493043)
    ·
      refine ⟨5896808162283873263239565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931205441522582175493043 5896808162283873263239565)
      ·
        refine ⟨2211303060856452473714837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5896808162283873263239565 2211303060856452473714837)
        ·
          refine ⟨103654830977646209705383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2211303060856452473714837 103654830977646209705383)
          ·
            refine ⟨155482246466469314558075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103654830977646209705383 155482246466469314558075)
            ·
              refine ⟨233223369699703971837113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155482246466469314558075 233223369699703971837113)
              ·
                refine ⟨174917527274777978877835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233223369699703971837113 174917527274777978877835)
                ·
                  refine ⟨262376290912166968316753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174917527274777978877835 262376290912166968316753)
                  ·
                    refine ⟨196782218184125226237565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 262376290912166968316753 196782218184125226237565)
                    ·
                      refine ⟨73793331819046959839087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196782218184125226237565 73793331819046959839087)
                      ·
                        rfl

theorem cell23_143712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_143712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143712 prefixEnd_143712 := by exact prefixLift 143712
  have htrace : WordTrace (prefixWord ++ tailWord_143712) baseStart_143712 baseEnd_143712 := by
    simpa [prefixWord, tailWord_143712, baseEnd_143712] using wordTrace_append hprefix tailTrace_143712
  have hstable : (prefixWord ++ tailWord_143712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143712).length < 2 ^ (prefixWord ++ tailWord_143712).sum := by decide
  have hdescent : baseEnd_143712 < baseStart_143712 := by decide
  rcases family_descends (prefixWord ++ tailWord_143712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143744 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_143744 : Nat := 118140960795 + 143744 * 2 ^ 59
def prefixEnd_143744 : Nat := 4983230072969 + 3 ^ 40 * 143744 * 2
def baseEnd_143744 : Nat := 73809763199990834638939

theorem tailTrace_143744 : CollatzResearch.WordTrace tailWord_143744 prefixEnd_143744 73809763199990834638939 := by
  unfold tailWord_143744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621387195623756182911143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3495182927498341577214857 2621387195623756182911143)
  ·
    refine ⟨3932080793435634274366715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2621387195623756182911143 3932080793435634274366715)
    ·
      refine ⟨5898121190153451411550073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3932080793435634274366715 5898121190153451411550073)
      ·
        refine ⟨4423590892615088558662555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5898121190153451411550073 4423590892615088558662555)
        ·
          refine ⟨6635386338922632837993833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4423590892615088558662555 6635386338922632837993833)
          ·
            refine ⟨4976539754191974628495375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6635386338922632837993833 4976539754191974628495375)
            ·
              refine ⟨7464809631287961942743063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976539754191974628495375 7464809631287961942743063)
              ·
                refine ⟨11197214446931942914114595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7464809631287961942743063 11197214446931942914114595)
                ·
                  refine ⟨16795821670397914371171893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11197214446931942914114595 16795821670397914371171893)
                  ·
                    refine ⟨1574608281599804472297365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16795821670397914371171893 1574608281599804472297365)
                    ·
                      refine ⟨73809763199990834638939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1574608281599804472297365 73809763199990834638939)
                      ·
                        rfl

theorem cell23_143744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_143744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143744 prefixEnd_143744 := by exact prefixLift 143744
  have htrace : WordTrace (prefixWord ++ tailWord_143744) baseStart_143744 baseEnd_143744 := by
    simpa [prefixWord, tailWord_143744, baseEnd_143744] using wordTrace_append hprefix tailTrace_143744
  have hstable : (prefixWord ++ tailWord_143744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143744).length < 2 ^ (prefixWord ++ tailWord_143744).sum := by decide
  have hdescent : baseEnd_143744 < baseStart_143744 := by decide
  rcases family_descends (prefixWord ++ tailWord_143744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143748 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_143748 : Nat := 118140960795 + 143748 * 2 ^ 59
def prefixEnd_143748 : Nat := 4983230072969 + 3 ^ 40 * 143748 * 2
def baseEnd_143748 : Nat := 73811817122608818988921

theorem tailTrace_143748 : CollatzResearch.WordTrace tailWord_143748 prefixEnd_143748 73811817122608818988921 := by
  unfold tailWord_143748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621460141616510524483949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3495280188822014032645265 2621460141616510524483949)
  ·
    refine ⟨983047553106191446681481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2621460141616510524483949 983047553106191446681481)
    ·
      refine ⟨737285664829643585011111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 983047553106191446681481 737285664829643585011111)
      ·
        refine ⟨1105928497244465377516667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737285664829643585011111 1105928497244465377516667)
        ·
          refine ⟨1658892745866698066275001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105928497244465377516667 1658892745866698066275001)
          ·
            refine ⟨1244169559400023549706251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1658892745866698066275001 1244169559400023549706251)
            ·
              refine ⟨1866254339100035324559377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244169559400023549706251 1866254339100035324559377)
              ·
                refine ⟨1399690754325026493419533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866254339100035324559377 1399690754325026493419533)
                ·
                  refine ⟨524884032871884935032325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1399690754325026493419533 524884032871884935032325)
                  ·
                    refine ⟨98415756163478425318561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524884032871884935032325 98415756163478425318561)
                    ·
                      refine ⟨73811817122608818988921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98415756163478425318561 73811817122608818988921)
                      ·
                        rfl

theorem cell23_143748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_143748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143748 prefixEnd_143748 := by exact prefixLift 143748
  have htrace : WordTrace (prefixWord ++ tailWord_143748) baseStart_143748 baseEnd_143748 := by
    simpa [prefixWord, tailWord_143748, baseEnd_143748] using wordTrace_append hprefix tailTrace_143748
  have hstable : (prefixWord ++ tailWord_143748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143748).length < 2 ^ (prefixWord ++ tailWord_143748).sum := by decide
  have hdescent : baseEnd_143748 < baseStart_143748 := by decide
  rcases family_descends (prefixWord ++ tailWord_143748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143751 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_143751 : Nat := 118140960795 + 143751 * 2 ^ 59
def prefixEnd_143751 : Nat := 4983230072969 + 3 ^ 40 * 143751 * 2
def baseEnd_143751 : Nat := 73813357564572307251407

theorem tailTrace_143751 : CollatzResearch.WordTrace tailWord_143751 prefixEnd_143751 73813357564572307251407 := by
  unfold tailWord_143751
  simp only [CollatzResearch.WordTrace]
  refine ⟨5243029702222152561327107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3495353134814768374218071 5243029702222152561327107)
  ·
    refine ⟨7864544553333228841990661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5243029702222152561327107 7864544553333228841990661)
    ·
      refine ⟨1474602103749980407873249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7864544553333228841990661 1474602103749980407873249)
      ·
        refine ⟨1105951577812485305904937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1474602103749980407873249 1105951577812485305904937)
        ·
          refine ⟨829463683359363979428703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105951577812485305904937 829463683359363979428703)
          ·
            refine ⟨1244195525039045969143055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829463683359363979428703 1244195525039045969143055)
            ·
              refine ⟨1866293287558568953714583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244195525039045969143055 1866293287558568953714583)
              ·
                refine ⟨2799439931337853430571875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866293287558568953714583 2799439931337853430571875)
                ·
                  refine ⟨4199159897006780145857813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799439931337853430571875 4199159897006780145857813)
                  ·
                    refine ⟨196835620172192819337085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4199159897006780145857813 196835620172192819337085)
                    ·
                      refine ⟨73813357564572307251407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196835620172192819337085 73813357564572307251407)
                      ·
                        rfl

theorem cell23_143751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_143751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143751 prefixEnd_143751 := by exact prefixLift 143751
  have htrace : WordTrace (prefixWord ++ tailWord_143751) baseStart_143751 baseEnd_143751 := by
    simpa [prefixWord, tailWord_143751, baseEnd_143751] using wordTrace_append hprefix tailTrace_143751
  have hstable : (prefixWord ++ tailWord_143751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143751).length < 2 ^ (prefixWord ++ tailWord_143751).sum := by decide
  have hdescent : baseEnd_143751 < baseStart_143751 := by decide
  rcases family_descends (prefixWord ++ tailWord_143751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143758 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_143758 : Nat := 118140960795 + 143758 * 2 ^ 59
def prefixEnd_143758 : Nat := 4983230072969 + 3 ^ 40 * 143758 * 2
def baseEnd_143758 : Nat := 24605650643051259954625

theorem tailTrace_143758 : CollatzResearch.WordTrace tailWord_143758 prefixEnd_143758 24605650643051259954625 := by
  unfold tailWord_143758
  simp only [CollatzResearch.WordTrace]
  refine ⟨655410626649599094603991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3495523342131195171221285 655410626649599094603991)
  ·
    refine ⟨983115939974398641905987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655410626649599094603991 983115939974398641905987)
    ·
      refine ⟨1474673909961597962858981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983115939974398641905987 1474673909961597962858981)
      ·
        refine ⟨276501358117799618036059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1474673909961597962858981 276501358117799618036059)
        ·
          refine ⟨414752037176699427054089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276501358117799618036059 414752037176699427054089)
          ·
            refine ⟨311064027882524570290567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414752037176699427054089 311064027882524570290567)
            ·
              refine ⟨466596041823786855435851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311064027882524570290567 466596041823786855435851)
              ·
                refine ⟨699894062735680283153777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466596041823786855435851 699894062735680283153777)
                ·
                  refine ⟨524920547051760212365333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699894062735680283153777 524920547051760212365333)
                  ·
                    refine ⟨24605650643051259954625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 524920547051760212365333 24605650643051259954625)
                    ·
                      rfl

theorem cell23_143758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_143758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143758 prefixEnd_143758 := by exact prefixLift 143758
  have htrace : WordTrace (prefixWord ++ tailWord_143758) baseStart_143758 baseEnd_143758 := by
    simpa [prefixWord, tailWord_143758, baseEnd_143758] using wordTrace_append hprefix tailTrace_143758
  have hstable : (prefixWord ++ tailWord_143758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143758).length < 2 ^ (prefixWord ++ tailWord_143758).sum := by decide
  have hdescent : baseEnd_143758 < baseStart_143758 := by decide
  rcases family_descends (prefixWord ++ tailWord_143758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143781 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_143781 : Nat := 118140960795 + 143781 * 2 ^ 59
def prefixEnd_143781 : Nat := 4983230072969 + 3 ^ 40 * 143781 * 2
def baseEnd_143781 : Nat := 73828761984207189876269

theorem tailTrace_143781 : CollatzResearch.WordTrace tailWord_143781 prefixEnd_143781 73828761984207189876269 := by
  unfold tailWord_143781
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244123892113467684919197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3496082594742311789946131 5244123892113467684919197)
  ·
    refine ⟨1966546459542550381844699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5244123892113467684919197 1966546459542550381844699)
    ·
      refine ⟨2949819689313825572767049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1966546459542550381844699 2949819689313825572767049)
      ·
        refine ⟨2212364766985369179575287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2949819689313825572767049 2212364766985369179575287)
        ·
          refine ⟨3318547150478053769362931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212364766985369179575287 3318547150478053769362931)
          ·
            refine ⟨4977820725717080654044397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318547150478053769362931 4977820725717080654044397)
            ·
              refine ⟨1866682772143905245266649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4977820725717080654044397 1866682772143905245266649)
              ·
                refine ⟨1400012079107928933949987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866682772143905245266649 1400012079107928933949987)
                ·
                  refine ⟨2100018118661893400924981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400012079107928933949987 2100018118661893400924981)
                  ·
                    refine ⟨196876698624552506336717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2100018118661893400924981 196876698624552506336717)
                    ·
                      refine ⟨73828761984207189876269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 196876698624552506336717 73828761984207189876269)
                      ·
                        rfl

theorem cell23_143781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_143781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143781 prefixEnd_143781 := by exact prefixLift 143781
  have htrace : WordTrace (prefixWord ++ tailWord_143781) baseStart_143781 baseEnd_143781 := by
    simpa [prefixWord, tailWord_143781, baseEnd_143781] using wordTrace_append hprefix tailTrace_143781
  have hstable : (prefixWord ++ tailWord_143781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143781).length < 2 ^ (prefixWord ++ tailWord_143781).sum := by decide
  have hdescent : baseEnd_143781 < baseStart_143781 := by decide
  rcases family_descends (prefixWord ++ tailWord_143781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143786 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_143786 : Nat := 118140960795 + 143786 * 2 ^ 59
def prefixEnd_143786 : Nat := 4983230072969 + 3 ^ 40 * 143786 * 2
def baseEnd_143786 : Nat := 73831329387479670313747

theorem tailTrace_143786 : CollatzResearch.WordTrace tailWord_143786 prefixEnd_143786 73831329387479670313747 := by
  unfold tailWord_143786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311076564273838384712803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3496204171396902359234141 1311076564273838384712803)
  ·
    refine ⟨1966614846410757577069205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1311076564273838384712803 1966614846410757577069205)
    ·
      refine ⟨92185070925504261425119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1966614846410757577069205 92185070925504261425119)
      ·
        refine ⟨138277606388256392137679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92185070925504261425119 138277606388256392137679)
        ·
          refine ⟨207416409582384588206519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138277606388256392137679 207416409582384588206519)
          ·
            refine ⟨311124614373576882309779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207416409582384588206519 311124614373576882309779)
            ·
              refine ⟨466686921560365323464669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311124614373576882309779 466686921560365323464669)
              ·
                refine ⟨175007595585136996299251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466686921560365323464669 175007595585136996299251)
                ·
                  refine ⟨262511393377705494448877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175007595585136996299251 262511393377705494448877)
                  ·
                    refine ⟨98441772516639560418329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262511393377705494448877 98441772516639560418329)
                    ·
                      refine ⟨73831329387479670313747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98441772516639560418329 73831329387479670313747)
                      ·
                        rfl

theorem cell23_143786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_143786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143786 prefixEnd_143786 := by exact prefixLift 143786
  have htrace : WordTrace (prefixWord ++ tailWord_143786) baseStart_143786 baseEnd_143786 := by
    simpa [prefixWord, tailWord_143786, baseEnd_143786] using wordTrace_append hprefix tailTrace_143786
  have hstable : (prefixWord ++ tailWord_143786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143786).length < 2 ^ (prefixWord ++ tailWord_143786).sum := by decide
  have hdescent : baseEnd_143786 < baseStart_143786 := by decide
  rcases family_descends (prefixWord ++ tailWord_143786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143865 : List Nat := [1, 2, 1, 3, 1, 2, 2, 6, 1, 4]
def baseStart_143865 : Nat := 118140960795 + 143865 * 2 ^ 59
def prefixEnd_143865 : Nat := 4983230072969 + 3 ^ 40 * 143865 * 2
def baseEnd_143865 : Nat := 24623964786394953741961

theorem tailTrace_143865 : CollatzResearch.WordTrace tailWord_143865 prefixEnd_143865 24623964786394953741961 := by
  unfold tailWord_143865
  simp only [CollatzResearch.WordTrace]
  refine ⟨5247187623809150030977049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3498125082539433353984699 5247187623809150030977049)
  ·
    refine ⟨3935390717856862523232787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5247187623809150030977049 3935390717856862523232787)
    ·
      refine ⟨5903086076785293784849181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3935390717856862523232787 5903086076785293784849181)
      ·
        refine ⟨2213657278794485169318443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5903086076785293784849181 2213657278794485169318443)
        ·
          refine ⟨3320485918191727753977665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213657278794485169318443 3320485918191727753977665)
          ·
            refine ⟨2490364438643795815483249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3320485918191727753977665 2490364438643795815483249)
            ·
              refine ⟨1867773328982846861612437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2490364438643795815483249 1867773328982846861612437)
              ·
                refine ⟨87551874796070946638083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1867773328982846861612437 87551874796070946638083)
                ·
                  refine ⟨131327812194106419957125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87551874796070946638083 131327812194106419957125)
                  ·
                    refine ⟨24623964786394953741961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131327812194106419957125 24623964786394953741961)
                    ·
                      rfl

theorem cell23_143865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 4].length) (baseStart_143865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143865 prefixEnd_143865 := by exact prefixLift 143865
  have htrace : WordTrace (prefixWord ++ tailWord_143865) baseStart_143865 baseEnd_143865 := by
    simpa [prefixWord, tailWord_143865, baseEnd_143865] using wordTrace_append hprefix tailTrace_143865
  have hstable : (prefixWord ++ tailWord_143865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143865).length < 2 ^ (prefixWord ++ tailWord_143865).sum := by decide
  have hdescent : baseEnd_143865 < baseStart_143865 := by decide
  rcases family_descends (prefixWord ++ tailWord_143865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143892 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_143892 : Nat := 118140960795 + 143892 * 2 ^ 59
def prefixEnd_143892 : Nat := 4983230072969 + 3 ^ 40 * 143892 * 2
def baseEnd_143892 : Nat := 73885758336856255588259

theorem tailTrace_143892 : CollatzResearch.WordTrace tailWord_143892 prefixEnd_143892 73885758336856255588259 := by
  unfold tailWord_143892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624086197355666821104965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3498781596474222428139953 2624086197355666821104965)
  ·
    refine ⟨492016162004187528957181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2624086197355666821104965 492016162004187528957181)
    ·
      refine ⟨184506060751570323358943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 492016162004187528957181 184506060751570323358943)
      ·
        refine ⟨276759091127355485038415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184506060751570323358943 276759091127355485038415)
        ·
          refine ⟨415138636691033227557623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276759091127355485038415 415138636691033227557623)
          ·
            refine ⟨622707955036549841336435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415138636691033227557623 622707955036549841336435)
            ·
              refine ⟨934061932554824762004653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622707955036549841336435 934061932554824762004653)
              ·
                refine ⟨350273224708059285751745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 934061932554824762004653 350273224708059285751745)
                ·
                  refine ⟨262704918531044464313809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350273224708059285751745 262704918531044464313809)
                  ·
                    refine ⟨197028688898283348235357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 262704918531044464313809 197028688898283348235357)
                    ·
                      refine ⟨73885758336856255588259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197028688898283348235357 73885758336856255588259)
                      ·
                        rfl

theorem cell23_143892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_143892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143892 prefixEnd_143892 := by exact prefixLift 143892
  have htrace : WordTrace (prefixWord ++ tailWord_143892) baseStart_143892 baseEnd_143892 := by
    simpa [prefixWord, tailWord_143892, baseEnd_143892] using wordTrace_append hprefix tailTrace_143892
  have hstable : (prefixWord ++ tailWord_143892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143892).length < 2 ^ (prefixWord ++ tailWord_143892).sum := by decide
  have hdescent : baseEnd_143892 < baseStart_143892 := by decide
  rcases family_descends (prefixWord ++ tailWord_143892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143928 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_143928 : Nat := 118140960795 + 143928 * 2 ^ 59
def prefixEnd_143928 : Nat := 4983230072969 + 3 ^ 40 * 143928 * 2
def baseEnd_143928 : Nat := 73904243640418114738093

theorem tailTrace_143928 : CollatzResearch.WordTrace tailWord_143928 prefixEnd_143928 73904243640418114738093 := by
  unfold tailWord_143928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624742711290455895260219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3499656948387274527013625 2624742711290455895260219)
  ·
    refine ⟨3937114066935683842890329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2624742711290455895260219 3937114066935683842890329)
    ·
      refine ⟨2952835550201762882167747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3937114066935683842890329 2952835550201762882167747)
      ·
        refine ⟨4429253325302644323251621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952835550201762882167747 4429253325302644323251621)
        ·
          refine ⟨830484998494245810609679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4429253325302644323251621 830484998494245810609679)
          ·
            refine ⟨1245727497741368715914519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830484998494245810609679 1245727497741368715914519)
            ·
              refine ⟨1868591246612053073871779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245727497741368715914519 1868591246612053073871779)
              ·
                refine ⟨2802886869918079610807669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868591246612053073871779 2802886869918079610807669)
                ·
                  refine ⟨262770644054819963513219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2802886869918079610807669 262770644054819963513219)
                  ·
                    refine ⟨394155966082229945269829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262770644054819963513219 394155966082229945269829)
                    ·
                      refine ⟨73904243640418114738093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 394155966082229945269829 73904243640418114738093)
                      ·
                        rfl

theorem cell23_143928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_143928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143928 prefixEnd_143928 := by exact prefixLift 143928
  have htrace : WordTrace (prefixWord ++ tailWord_143928) baseStart_143928 baseEnd_143928 := by
    simpa [prefixWord, tailWord_143928, baseEnd_143928] using wordTrace_append hprefix tailTrace_143928
  have hstable : (prefixWord ++ tailWord_143928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143928).length < 2 ^ (prefixWord ++ tailWord_143928).sum := by decide
  have hdescent : baseEnd_143928 < baseStart_143928 := by decide
  rcases family_descends (prefixWord ++ tailWord_143928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143942 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_143942 : Nat := 118140960795 + 143942 * 2 ^ 59
def prefixEnd_143942 : Nat := 4983230072969 + 3 ^ 40 * 143942 * 2
def baseEnd_143942 : Nat := 24637144123193686654343

theorem tailTrace_143942 : CollatzResearch.WordTrace tailWord_143942 prefixEnd_143942 24637144123193686654343 := by
  unfold tailWord_143942
  simp only [CollatzResearch.WordTrace]
  refine ⟨164062376391568505672815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3499997363020128121020053 164062376391568505672815)
  ·
    refine ⟨246093564587352758509223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164062376391568505672815 246093564587352758509223)
    ·
      refine ⟨369140346881029137763835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246093564587352758509223 369140346881029137763835)
      ·
        refine ⟨553710520321543706645753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369140346881029137763835 553710520321543706645753)
        ·
          refine ⟨415282890241157779984315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553710520321543706645753 415282890241157779984315)
          ·
            refine ⟨622924335361736669976473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415282890241157779984315 622924335361736669976473)
            ·
              refine ⟨467193251521302502482355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622924335361736669976473 467193251521302502482355)
              ·
                refine ⟨700789877281953753723533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467193251521302502482355 700789877281953753723533)
                ·
                  refine ⟨262796203980732657646325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700789877281953753723533 262796203980732657646325)
                  ·
                    refine ⟨24637144123193686654343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 262796203980732657646325 24637144123193686654343)
                    ·
                      rfl

theorem cell23_143942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_143942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143942 prefixEnd_143942 := by exact prefixLift 143942
  have htrace : WordTrace (prefixWord ++ tailWord_143942) baseStart_143942 baseEnd_143942 := by
    simpa [prefixWord, tailWord_143942, baseEnd_143942] using wordTrace_append hprefix tailTrace_143942
  have hstable : (prefixWord ++ tailWord_143942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143942).length < 2 ^ (prefixWord ++ tailWord_143942).sum := by decide
  have hdescent : baseEnd_143942 < baseStart_143942 := by decide
  rcases family_descends (prefixWord ++ tailWord_143942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143949 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_143949 : Nat := 118140960795 + 143949 * 2 ^ 59
def prefixEnd_143949 : Nat := 4983230072969 + 3 ^ 40 * 143949 * 2
def baseEnd_143949 : Nat := 73915026734162532575497

theorem tailTrace_143949 : CollatzResearch.WordTrace tailWord_143949 prefixEnd_143949 73915026734162532575497 := by
  unfold tailWord_143949
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250251355504832377034901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3500167570336554918023267 5250251355504832377034901)
  ·
    refine ⟨246105532289289017673511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5250251355504832377034901 246105532289289017673511)
    ·
      refine ⟨369158298433933526510267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246105532289289017673511 369158298433933526510267)
      ·
        refine ⟨553737447650900289765401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369158298433933526510267 553737447650900289765401)
        ·
          refine ⟨415303085738175217324051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553737447650900289765401 415303085738175217324051)
          ·
            refine ⟨622954628607262825986077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415303085738175217324051 622954628607262825986077)
            ·
              refine ⟨233607985727723559744779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 622954628607262825986077 233607985727723559744779)
              ·
                refine ⟨350411978591585339617169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233607985727723559744779 350411978591585339617169)
                ·
                  refine ⟨262808983943689004712877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350411978591585339617169 262808983943689004712877)
                  ·
                    refine ⟨98553368978883376767329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262808983943689004712877 98553368978883376767329)
                    ·
                      refine ⟨73915026734162532575497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98553368978883376767329 73915026734162532575497)
                      ·
                        rfl

theorem cell23_143949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_143949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143949 prefixEnd_143949 := by exact prefixLift 143949
  have htrace : WordTrace (prefixWord ++ tailWord_143949) baseStart_143949 baseEnd_143949 := by
    simpa [prefixWord, tailWord_143949, baseEnd_143949] using wordTrace_append hprefix tailTrace_143949
  have hstable : (prefixWord ++ tailWord_143949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143949).length < 2 ^ (prefixWord ++ tailWord_143949).sum := by decide
  have hdescent : baseEnd_143949 < baseStart_143949 := by decide
  rcases family_descends (prefixWord ++ tailWord_143949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143951 : List Nat := [1, 1, 2, 1, 1, 2, 4, 11]
def baseStart_143951 : Nat := 118140960795 + 143951 * 2 ^ 59
def prefixEnd_143951 : Nat := 4983230072969 + 3 ^ 40 * 143951 * 2
def baseEnd_143951 : Nat := 2737631618350797212981

theorem tailTrace_143951 : CollatzResearch.WordTrace tailWord_143951 prefixEnd_143951 2737631618350797212981 := by
  unfold tailWord_143951
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250324301497586718607707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3500216200998391145738471 5250324301497586718607707)
  ·
    refine ⟨7875486452246380077911561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5250324301497586718607707 7875486452246380077911561)
    ·
      refine ⟨5906614839184785058433671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7875486452246380077911561 5906614839184785058433671)
      ·
        refine ⟨8859922258777177587650507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5906614839184785058433671 8859922258777177587650507)
        ·
          refine ⟨13289883388165766381475761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8859922258777177587650507 13289883388165766381475761)
          ·
            refine ⟨9967412541124324786106821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13289883388165766381475761 9967412541124324786106821)
            ·
              refine ⟨1868889851460810897395029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9967412541124324786106821 1868889851460810897395029)
              ·
                refine ⟨2737631618350797212981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1868889851460810897395029 2737631618350797212981)
                ·
                  rfl

theorem cell23_143951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 11].length) (baseStart_143951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143951 prefixEnd_143951 := by exact prefixLift 143951
  have htrace : WordTrace (prefixWord ++ tailWord_143951) baseStart_143951 baseEnd_143951 := by
    simpa [prefixWord, tailWord_143951, baseEnd_143951] using wordTrace_append hprefix tailTrace_143951
  have hstable : (prefixWord ++ tailWord_143951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143951).length < 2 ^ (prefixWord ++ tailWord_143951).sum := by decide
  have hdescent : baseEnd_143951 < baseStart_143951 := by decide
  rcases family_descends (prefixWord ++ tailWord_143951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143989 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_143989 : Nat := 118140960795 + 143989 * 2 ^ 59
def prefixEnd_143989 : Nat := 4983230072969 + 3 ^ 40 * 143989 * 2
def baseEnd_143989 : Nat := 24645188653447458691771

theorem tailTrace_143989 : CollatzResearch.WordTrace tailWord_143989 prefixEnd_143989 24645188653447458691771 := by
  unfold tailWord_143989
  simp only [CollatzResearch.WordTrace]
  refine ⟨5251710275359919208491021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3501140183573279472327347 5251710275359919208491021)
  ·
    refine ⟨1969391353259969703184133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5251710275359919208491021 1969391353259969703184133)
    ·
      refine ⟨369260878736244319347025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1969391353259969703184133 369260878736244319347025)
      ·
        refine ⟨276945659052183239510269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369260878736244319347025 276945659052183239510269)
        ·
          refine ⟨103854622144568714816351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276945659052183239510269 103854622144568714816351)
          ·
            refine ⟨155781933216853072224527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103854622144568714816351 155781933216853072224527)
            ·
              refine ⟨233672899825279608336791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155781933216853072224527 233672899825279608336791)
              ·
                refine ⟨350509349737919412505187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233672899825279608336791 350509349737919412505187)
                ·
                  refine ⟨525764024606879118757781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350509349737919412505187 525764024606879118757781)
                  ·
                    refine ⟨24645188653447458691771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 525764024606879118757781 24645188653447458691771)
                    ·
                      rfl

theorem cell23_143989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_143989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_143989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_143989 prefixEnd_143989 := by exact prefixLift 143989
  have htrace : WordTrace (prefixWord ++ tailWord_143989) baseStart_143989 baseEnd_143989 := by
    simpa [prefixWord, tailWord_143989, baseEnd_143989] using wordTrace_append hprefix tailTrace_143989
  have hstable : (prefixWord ++ tailWord_143989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143989).length < 2 ^ (prefixWord ++ tailWord_143989).sum := by decide
  have hdescent : baseEnd_143989 < baseStart_143989 := by decide
  rcases family_descends (prefixWord ++ tailWord_143989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144035 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 5, 4, 2]
def baseStart_144035 : Nat := 118140960795 + 144035 * 2 ^ 59
def prefixEnd_144035 : Nat := 4983230072969 + 3 ^ 40 * 144035 * 2
def baseEnd_144035 : Nat := 73959186070449196100101

theorem tailTrace_144035 : CollatzResearch.WordTrace tailWord_144035 prefixEnd_144035 73959186070449196100101 := by
  unfold tailWord_144035
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253388033193269064665559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3502258688795512709777039 5253388033193269064665559)
  ·
    refine ⟨7880082049789903596998339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5253388033193269064665559 7880082049789903596998339)
    ·
      refine ⟨11820123074684855395497509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7880082049789903596998339 11820123074684855395497509)
      ·
        refine ⟨2216273076503410386655783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11820123074684855395497509 2216273076503410386655783)
        ·
          refine ⟨3324409614755115579983675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216273076503410386655783 3324409614755115579983675)
          ·
            refine ⟨4986614422132673369975513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324409614755115579983675 4986614422132673369975513)
            ·
              refine ⟨3739960816599505027481635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4986614422132673369975513 3739960816599505027481635)
              ·
                refine ⟨5609941224899257541222453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739960816599505027481635 5609941224899257541222453)
                ·
                  refine ⟨525931989834305394489605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5609941224899257541222453 525931989834305394489605)
                  ·
                    refine ⟨98612248093932261466801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525931989834305394489605 98612248093932261466801)
                    ·
                      refine ⟨73959186070449196100101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98612248093932261466801 73959186070449196100101)
                      ·
                        rfl

theorem cell23_144035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_144035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144035 prefixEnd_144035 := by exact prefixLift 144035
  have htrace : WordTrace (prefixWord ++ tailWord_144035) baseStart_144035 baseEnd_144035 := by
    simpa [prefixWord, tailWord_144035, baseEnd_144035] using wordTrace_append hprefix tailTrace_144035
  have hstable : (prefixWord ++ tailWord_144035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144035).length < 2 ^ (prefixWord ++ tailWord_144035).sum := by decide
  have hdescent : baseEnd_144035 < baseStart_144035 := by decide
  rcases family_descends (prefixWord ++ tailWord_144035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144046 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_144046 : Nat := 118140960795 + 144046 * 2 ^ 59
def prefixEnd_144046 : Nat := 4983230072969 + 3 ^ 40 * 144046 * 2
def baseEnd_144046 : Nat := 73964834357648653062551

theorem tailTrace_144046 : CollatzResearch.WordTrace tailWord_144046 prefixEnd_144046 73964834357648653062551 := by
  unfold tailWord_144046
  simp only [CollatzResearch.WordTrace]
  refine ⟨656723654519177242914499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3502526157435611962210661 656723654519177242914499)
  ·
    refine ⟨985085481778765864371749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 656723654519177242914499 985085481778765864371749)
    ·
      refine ⟨184703527833518599569703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 985085481778765864371749 184703527833518599569703)
      ·
        refine ⟨277055291750277899354555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184703527833518599569703 277055291750277899354555)
        ·
          refine ⟨415582937625416849031833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277055291750277899354555 415582937625416849031833)
          ·
            refine ⟨311687203219062636773875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415582937625416849031833 311687203219062636773875)
            ·
              refine ⟨467530804828593955160813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311687203219062636773875 467530804828593955160813)
              ·
                refine ⟨175324051810722733185305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 467530804828593955160813 175324051810722733185305)
                ·
                  refine ⟨131493038858042049888979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175324051810722733185305 131493038858042049888979)
                  ·
                    refine ⟨197239558287063074833469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131493038858042049888979 197239558287063074833469)
                    ·
                      refine ⟨73964834357648653062551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197239558287063074833469 73964834357648653062551)
                      ·
                        rfl

theorem cell23_144046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_144046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144046 prefixEnd_144046 := by exact prefixLift 144046
  have htrace : WordTrace (prefixWord ++ tailWord_144046) baseStart_144046 baseEnd_144046 := by
    simpa [prefixWord, tailWord_144046, baseEnd_144046] using wordTrace_append hprefix tailTrace_144046
  have hstable : (prefixWord ++ tailWord_144046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144046).length < 2 ^ (prefixWord ++ tailWord_144046).sum := by decide
  have hdescent : baseEnd_144046 < baseStart_144046 := by decide
  rcases family_descends (prefixWord ++ tailWord_144046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144048 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_144048 : Nat := 118140960795 + 144048 * 2 ^ 59
def prefixEnd_144048 : Nat := 4983230072969 + 3 ^ 40 * 144048 * 2
def baseEnd_144048 : Nat := 73965861318957645237541

theorem tailTrace_144048 : CollatzResearch.WordTrace tailWord_144048 prefixEnd_144048 73965861318957645237541 := by
  unfold tailWord_144048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626931091073086142444399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3502574788097448189925865 2626931091073086142444399)
  ·
    refine ⟨3940396636609629213666599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2626931091073086142444399 3940396636609629213666599)
    ·
      refine ⟨5910594954914443820499899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940396636609629213666599 5910594954914443820499899)
      ·
        refine ⟨8865892432371665730749849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910594954914443820499899 8865892432371665730749849)
        ·
          refine ⟨6649419324278749298062387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8865892432371665730749849 6649419324278749298062387)
          ·
            refine ⟨9974128986418123947093581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6649419324278749298062387 9974128986418123947093581)
            ·
              refine ⟨3740298369906796480160093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9974128986418123947093581 3740298369906796480160093)
              ·
                refine ⟨1402611888715048680060035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3740298369906796480160093 1402611888715048680060035)
                ·
                  refine ⟨2103917833072573020090053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402611888715048680060035 2103917833072573020090053)
                  ·
                    refine ⟨394484593701107441266885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103917833072573020090053 394484593701107441266885)
                    ·
                      refine ⟨73965861318957645237541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 394484593701107441266885 73965861318957645237541)
                      ·
                        rfl

theorem cell23_144048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_144048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144048 prefixEnd_144048 := by exact prefixLift 144048
  have htrace : WordTrace (prefixWord ++ tailWord_144048) baseStart_144048 baseEnd_144048 := by
    simpa [prefixWord, tailWord_144048, baseEnd_144048] using wordTrace_append hprefix tailTrace_144048
  have hstable : (prefixWord ++ tailWord_144048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144048).length < 2 ^ (prefixWord ++ tailWord_144048).sum := by decide
  have hdescent : baseEnd_144048 < baseStart_144048 := by decide
  rcases family_descends (prefixWord ++ tailWord_144048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144058 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 9]
def baseStart_144058 : Nat := 118140960795 + 144058 * 2 ^ 59
def prefixEnd_144058 : Nat := 4983230072969 + 3 ^ 40 * 144058 * 2
def baseEnd_144058 : Nat := 8218999569500289568055

theorem tailTrace_144058 : CollatzResearch.WordTrace tailWord_144058 prefixEnd_144058 8218999569500289568055 := by
  unfold tailWord_144058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313556728027485998188207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3502817941406629328501885 1313556728027485998188207)
  ·
    refine ⟨1970335092041228997282311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1313556728027485998188207 1970335092041228997282311)
    ·
      refine ⟨2955502638061843495923467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1970335092041228997282311 2955502638061843495923467)
      ·
        refine ⟨4433253957092765243885201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955502638061843495923467 4433253957092765243885201)
        ·
          refine ⟨3324940467819573932913901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4433253957092765243885201 3324940467819573932913901)
          ·
            refine ⟨1246852675432340224842713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3324940467819573932913901 1246852675432340224842713)
            ·
              refine ⟨935139506574255168632035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246852675432340224842713 935139506574255168632035)
              ·
                refine ⟨1402709259861382752948053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935139506574255168632035 1402709259861382752948053)
                ·
                  refine ⟨8218999569500289568055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1402709259861382752948053 8218999569500289568055)
                  ·
                    rfl

theorem cell23_144058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_144058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144058 prefixEnd_144058 := by exact prefixLift 144058
  have htrace : WordTrace (prefixWord ++ tailWord_144058) baseStart_144058 baseEnd_144058 := by
    simpa [prefixWord, tailWord_144058, baseEnd_144058] using wordTrace_append hprefix tailTrace_144058
  have hstable : (prefixWord ++ tailWord_144058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144058).length < 2 ^ (prefixWord ++ tailWord_144058).sum := by decide
  have hdescent : baseEnd_144058 < baseStart_144058 := by decide
  rcases family_descends (prefixWord ++ tailWord_144058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144125 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_144125 : Nat := 118140960795 + 144125 * 2 ^ 59
def prefixEnd_144125 : Nat := 4983230072969 + 3 ^ 40 * 144125 * 2
def baseEnd_144125 : Nat := 74005399329353843974687

theorem tailTrace_144125 : CollatzResearch.WordTrace tailWord_144125 prefixEnd_144125 74005399329353843974687 := by
  unfold tailWord_144125
  simp only [CollatzResearch.WordTrace]
  refine ⟨5256670602867214435441829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3504447068578142956961219 5256670602867214435441829)
  ·
    refine ⟨985625738037602706645343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5256670602867214435441829 985625738037602706645343)
    ·
      refine ⟨1478438607056404059968015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985625738037602706645343 1478438607056404059968015)
      ·
        refine ⟨2217657910584606089952023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478438607056404059968015 2217657910584606089952023)
        ·
          refine ⟨3326486865876909134928035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217657910584606089952023 3326486865876909134928035)
          ·
            refine ⟨4989730298815363702392053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326486865876909134928035 4989730298815363702392053)
            ·
              refine ⟨467787215513940347099255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4989730298815363702392053 467787215513940347099255)
              ·
                refine ⟨701680823270910520648883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467787215513940347099255 701680823270910520648883)
                ·
                  refine ⟨1052521234906365780973325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701680823270910520648883 1052521234906365780973325)
                  ·
                    refine ⟨394695463089887167864997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052521234906365780973325 394695463089887167864997)
                    ·
                      refine ⟨74005399329353843974687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 394695463089887167864997 74005399329353843974687)
                      ·
                        rfl

theorem cell23_144125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_144125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144125 prefixEnd_144125 := by exact prefixLift 144125
  have htrace : WordTrace (prefixWord ++ tailWord_144125) baseStart_144125 baseEnd_144125 := by
    simpa [prefixWord, tailWord_144125, baseEnd_144125] using wordTrace_append hprefix tailTrace_144125
  have hstable : (prefixWord ++ tailWord_144125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144125).length < 2 ^ (prefixWord ++ tailWord_144125).sum := by decide
  have hdescent : baseEnd_144125 < baseStart_144125 := by decide
  rcases family_descends (prefixWord ++ tailWord_144125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144128 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_144128 : Nat := 118140960795 + 144128 * 2 ^ 59
def prefixEnd_144128 : Nat := 4983230072969 + 3 ^ 40 * 144128 * 2
def baseEnd_144128 : Nat := 74006939771317332237173

theorem tailTrace_144128 : CollatzResearch.WordTrace tailWord_144128 prefixEnd_144128 74006939771317332237173 := by
  unfold tailWord_144128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628390010928172973900519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3504520014570897298534025 2628390010928172973900519)
  ·
    refine ⟨3942585016392259460850779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2628390010928172973900519 3942585016392259460850779)
    ·
      refine ⟨5913877524588389191276169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3942585016392259460850779 5913877524588389191276169)
      ·
        refine ⟨4435408143441291893457127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5913877524588389191276169 4435408143441291893457127)
        ·
          refine ⟨6653112215161937840185691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435408143441291893457127 6653112215161937840185691)
          ·
            refine ⟨9979668322742906760278537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653112215161937840185691 9979668322742906760278537)
            ·
              refine ⟨7484751242057180070208903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9979668322742906760278537 7484751242057180070208903)
              ·
                refine ⟨11227126863085770105313355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7484751242057180070208903 11227126863085770105313355)
                ·
                  refine ⟨16840690294628655157970033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11227126863085770105313355 16840690294628655157970033)
                  ·
                    refine ⟨12630517720971491368477525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16840690294628655157970033 12630517720971491368477525)
                    ·
                      refine ⟨74006939771317332237173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 12630517720971491368477525 74006939771317332237173)
                      ·
                        rfl

theorem cell23_144128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_144128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144128 prefixEnd_144128 := by exact prefixLift 144128
  have htrace : WordTrace (prefixWord ++ tailWord_144128) baseStart_144128 baseEnd_144128 := by
    simpa [prefixWord, tailWord_144128, baseEnd_144128] using wordTrace_append hprefix tailTrace_144128
  have hstable : (prefixWord ++ tailWord_144128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144128).length < 2 ^ (prefixWord ++ tailWord_144128).sum := by decide
  have hdescent : baseEnd_144128 < baseStart_144128 := by decide
  rcases family_descends (prefixWord ++ tailWord_144128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144162 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_144162 : Nat := 118140960795 + 144162 * 2 ^ 59
def prefixEnd_144162 : Nat := 4983230072969 + 3 ^ 40 * 144162 * 2
def baseEnd_144162 : Nat := 74024398113570199212017

theorem tailTrace_144162 : CollatzResearch.WordTrace tailWord_144162 prefixEnd_144162 74024398113570199212017 := by
  unfold tailWord_144162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314505025933292438634685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3505346735822113169692493 1314505025933292438634685)
  ·
    refine ⟨492939384724984664488007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1314505025933292438634685 492939384724984664488007)
    ·
      refine ⟨739409077087476996732011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492939384724984664488007 739409077087476996732011)
      ·
        refine ⟨1109113615631215495098017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739409077087476996732011 1109113615631215495098017)
        ·
          refine ⟨831835211723411621323513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109113615631215495098017 831835211723411621323513)
          ·
            refine ⟨623876408792558715992635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831835211723411621323513 623876408792558715992635)
            ·
              refine ⟨935814613188838073988953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623876408792558715992635 935814613188838073988953)
              ·
                refine ⟨701860959891628555491715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935814613188838073988953 701860959891628555491715)
                ·
                  refine ⟨1052791439837442833237573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701860959891628555491715 1052791439837442833237573)
                  ·
                    refine ⟨197398394969520531232045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1052791439837442833237573 197398394969520531232045)
                    ·
                      refine ⟨74024398113570199212017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197398394969520531232045 74024398113570199212017)
                      ·
                        rfl

theorem cell23_144162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_144162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144162 prefixEnd_144162 := by exact prefixLift 144162
  have htrace : WordTrace (prefixWord ++ tailWord_144162) baseStart_144162 baseEnd_144162 := by
    simpa [prefixWord, tailWord_144162, baseEnd_144162] using wordTrace_append hprefix tailTrace_144162
  have hstable : (prefixWord ++ tailWord_144162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144162).length < 2 ^ (prefixWord ++ tailWord_144162).sum := by decide
  have hdescent : baseEnd_144162 < baseStart_144162 := by decide
  rcases family_descends (prefixWord ++ tailWord_144162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144192 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 5, 1, 3]
def baseStart_144192 : Nat := 118140960795 + 144192 * 2 ^ 59
def prefixEnd_144192 : Nat := 4983230072969 + 3 ^ 40 * 144192 * 2
def baseEnd_144192 : Nat := 74039802533205081836879

theorem tailTrace_144192 : CollatzResearch.WordTrace tailWord_144192 prefixEnd_144192 74039802533205081836879 := by
  unfold tailWord_144192
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629557146812242439065415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3506076195749656585420553 2629557146812242439065415)
  ·
    refine ⟨3944335720218363658598123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629557146812242439065415 3944335720218363658598123)
    ·
      refine ⟨5916503580327545487897185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3944335720218363658598123 5916503580327545487897185)
      ·
        refine ⟨4437377685245659115922889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5916503580327545487897185 4437377685245659115922889)
        ·
          refine ⟨3328033263934244336942167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437377685245659115922889 3328033263934244336942167)
          ·
            refine ⟨4992049895901366505413251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328033263934244336942167 4992049895901366505413251)
            ·
              refine ⟨7488074843852049758119877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4992049895901366505413251 7488074843852049758119877)
              ·
                refine ⟨1404014033222259329647477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7488074843852049758119877 1404014033222259329647477)
                ·
                  refine ⟨131626315614586812154451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1404014033222259329647477 131626315614586812154451)
                  ·
                    refine ⟨197439473421880218231677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131626315614586812154451 197439473421880218231677)
                    ·
                      refine ⟨74039802533205081836879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197439473421880218231677 74039802533205081836879)
                      ·
                        rfl

theorem cell23_144192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_144192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144192 prefixEnd_144192 := by exact prefixLift 144192
  have htrace : WordTrace (prefixWord ++ tailWord_144192) baseStart_144192 baseEnd_144192 := by
    simpa [prefixWord, tailWord_144192, baseEnd_144192] using wordTrace_append hprefix tailTrace_144192
  have hstable : (prefixWord ++ tailWord_144192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144192).length < 2 ^ (prefixWord ++ tailWord_144192).sum := by decide
  have hdescent : baseEnd_144192 < baseStart_144192 := by decide
  rcases family_descends (prefixWord ++ tailWord_144192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144202 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_144202 : Nat := 118140960795 + 144202 * 2 ^ 59
def prefixEnd_144202 : Nat := 4983230072969 + 3 ^ 40 * 144202 * 2
def baseEnd_144202 : Nat := 74044937339750042711833

theorem tailTrace_144202 : CollatzResearch.WordTrace tailWord_144202 prefixEnd_144202 74044937339750042711833 := by
  unfold tailWord_144202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314869755897064146498715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3506319349058837723996573 1314869755897064146498715)
  ·
    refine ⟨1972304633845596219748073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1314869755897064146498715 1972304633845596219748073)
    ·
      refine ⟨1479228475384197164811055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1972304633845596219748073 1479228475384197164811055)
      ·
        refine ⟨2218842713076295747216583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479228475384197164811055 2218842713076295747216583)
        ·
          refine ⟨3328264069614443620824875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218842713076295747216583 3328264069614443620824875)
          ·
            refine ⟨4992396104421665431237313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328264069614443620824875 4992396104421665431237313)
            ·
              refine ⟨3744297078316249073427985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4992396104421665431237313 3744297078316249073427985)
              ·
                refine ⟨2808222808737186805070989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744297078316249073427985 2808222808737186805070989)
                ·
                  refine ⟨1053083553276445051901621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2808222808737186805070989 1053083553276445051901621)
                  ·
                    refine ⟨98726583119666723615777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1053083553276445051901621 98726583119666723615777)
                    ·
                      refine ⟨74044937339750042711833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 98726583119666723615777 74044937339750042711833)
                      ·
                        rfl

theorem cell23_144202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_144202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144202 prefixEnd_144202 := by exact prefixLift 144202
  have htrace : WordTrace (prefixWord ++ tailWord_144202) baseStart_144202 baseEnd_144202 := by
    simpa [prefixWord, tailWord_144202, baseEnd_144202] using wordTrace_append hprefix tailTrace_144202
  have hstable : (prefixWord ++ tailWord_144202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144202).length < 2 ^ (prefixWord ++ tailWord_144202).sum := by decide
  have hdescent : baseEnd_144202 < baseStart_144202 := by decide
  rcases family_descends (prefixWord ++ tailWord_144202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144235 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5]
def baseStart_144235 : Nat := 118140960795 + 144235 * 2 ^ 59
def prefixEnd_144235 : Nat := 4983230072969 + 3 ^ 40 * 144235 * 2
def baseEnd_144235 : Nat := 74061882201348413599181

theorem tailTrace_144235 : CollatzResearch.WordTrace tailWord_144235 prefixEnd_144235 74061882201348413599181 := by
  unfold tailWord_144235
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260682632468703221946159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3507121754979135481297439 5260682632468703221946159)
  ·
    refine ⟨7891023948703054832919239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5260682632468703221946159 7891023948703054832919239)
    ·
      refine ⟨11836535923054582249378859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7891023948703054832919239 11836535923054582249378859)
      ·
        refine ⟨17754803884581873374068289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11836535923054582249378859 17754803884581873374068289)
        ·
          refine ⟨13316102913436405030551217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17754803884581873374068289 13316102913436405030551217)
          ·
            refine ⟨9987077185077303772913413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13316102913436405030551217 9987077185077303772913413)
            ·
              refine ⟨1872576972201994457421265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9987077185077303772913413 1872576972201994457421265)
              ·
                refine ⟨1404432729151495843065949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1872576972201994457421265 1404432729151495843065949)
                ·
                  refine ⟨526662273431810941149731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1404432729151495843065949 526662273431810941149731)
                  ·
                    refine ⟨789993410147716411724597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526662273431810941149731 789993410147716411724597)
                    ·
                      refine ⟨74061882201348413599181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 789993410147716411724597 74061882201348413599181)
                      ·
                        rfl

theorem cell23_144235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_144235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144235 prefixEnd_144235 := by exact prefixLift 144235
  have htrace : WordTrace (prefixWord ++ tailWord_144235) baseStart_144235 baseEnd_144235 := by
    simpa [prefixWord, tailWord_144235, baseEnd_144235] using wordTrace_append hprefix tailTrace_144235
  have hstable : (prefixWord ++ tailWord_144235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144235).length < 2 ^ (prefixWord ++ tailWord_144235).sum := by decide
  have hdescent : baseEnd_144235 < baseStart_144235 := by decide
  rcases family_descends (prefixWord ++ tailWord_144235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144242 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_144242 : Nat := 118140960795 + 144242 * 2 ^ 59
def prefixEnd_144242 : Nat := 4983230072969 + 3 ^ 40 * 144242 * 2
def baseEnd_144242 : Nat := 24688492188643295403883

theorem tailTrace_144242 : CollatzResearch.WordTrace tailWord_144242 prefixEnd_144242 24688492188643295403883 := by
  unfold tailWord_144242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315234485860835854362745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3507291962295562278300653 1315234485860835854362745)
  ·
    refine ⟨986425864395626890772059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1315234485860835854362745 986425864395626890772059)
    ·
      refine ⟨1479638796593440336158089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986425864395626890772059 1479638796593440336158089)
      ·
        refine ⟨1109729097445080252118567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479638796593440336158089 1109729097445080252118567)
        ·
          refine ⟨1664593646167620378177851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109729097445080252118567 1664593646167620378177851)
          ·
            refine ⟨2496890469251430567266777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664593646167620378177851 2496890469251430567266777)
            ·
              refine ⟨1872667851938572925450083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496890469251430567266777 1872667851938572925450083)
              ·
                refine ⟨2809001777907859388175125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872667851938572925450083 2809001777907859388175125)
                ·
                  refine ⟨131671958339430908820709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2809001777907859388175125 131671958339430908820709)
                  ·
                    refine ⟨24688492188643295403883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131671958339430908820709 24688492188643295403883)
                    ·
                      rfl

theorem cell23_144242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_144242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144242 prefixEnd_144242 := by exact prefixLift 144242
  have htrace : WordTrace (prefixWord ++ tailWord_144242) baseStart_144242 baseEnd_144242 := by
    simpa [prefixWord, tailWord_144242, baseEnd_144242] using wordTrace_append hprefix tailTrace_144242
  have hstable : (prefixWord ++ tailWord_144242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144242).length < 2 ^ (prefixWord ++ tailWord_144242).sum := by decide
  have hdescent : baseEnd_144242 < baseStart_144242 := by decide
  rcases family_descends (prefixWord ++ tailWord_144242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144259 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 2, 4]
def baseStart_144259 : Nat := 118140960795 + 144259 * 2 ^ 59
def prefixEnd_144259 : Nat := 4983230072969 + 3 ^ 40 * 144259 * 2
def baseEnd_144259 : Nat := 24691401912352106566357

theorem tailTrace_144259 : CollatzResearch.WordTrace tailWord_144259 prefixEnd_144259 24691401912352106566357 := by
  unfold tailWord_144259
  simp only [CollatzResearch.WordTrace]
  refine ⟨5261557984381755320819831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3507705322921170213879887 5261557984381755320819831)
  ·
    refine ⟨7892336976572632981229747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5261557984381755320819831 7892336976572632981229747)
    ·
      refine ⟨11838505464858949471844621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7892336976572632981229747 11838505464858949471844621)
      ·
        refine ⟨4439439549322106051941733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11838505464858949471844621 4439439549322106051941733)
        ·
          refine ⟨832394915497894884739075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4439439549322106051941733 832394915497894884739075)
          ·
            refine ⟨1248592373246842327108613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832394915497894884739075 1248592373246842327108613)
            ·
              refine ⟨234111069983782936332865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1248592373246842327108613 234111069983782936332865)
              ·
                refine ⟨175583302487837202249649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234111069983782936332865 175583302487837202249649)
                ·
                  refine ⟨131687476865877901687237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175583302487837202249649 131687476865877901687237)
                  ·
                    refine ⟨24691401912352106566357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131687476865877901687237 24691401912352106566357)
                    ·
                      rfl

theorem cell23_144259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 4].length) (baseStart_144259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144259 prefixEnd_144259 := by exact prefixLift 144259
  have htrace : WordTrace (prefixWord ++ tailWord_144259) baseStart_144259 baseEnd_144259 := by
    simpa [prefixWord, tailWord_144259, baseEnd_144259] using wordTrace_append hprefix tailTrace_144259
  have hstable : (prefixWord ++ tailWord_144259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144259).length < 2 ^ (prefixWord ++ tailWord_144259).sum := by decide
  have hdescent : baseEnd_144259 < baseStart_144259 := by decide
  rcases family_descends (prefixWord ++ tailWord_144259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144289 : List Nat := [1, 2, 3, 4, 1, 2, 3, 7]
def baseStart_144289 : Nat := 118140960795 + 144289 * 2 ^ 59
def prefixEnd_144289 : Nat := 4983230072969 + 3 ^ 40 * 144289 * 2
def baseEnd_144289 : Nat := 2744059635433007493479

theorem tailTrace_144289 : CollatzResearch.WordTrace tailWord_144289 prefixEnd_144289 2744059635433007493479 := by
  unfold tailWord_144289
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262652174273070444411921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3508434782848713629607947 5262652174273070444411921)
  ·
    refine ⟨3946989130704802833308941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5262652174273070444411921 3946989130704802833308941)
    ·
      refine ⟨1480120924014301062490853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3946989130704802833308941 1480120924014301062490853)
      ·
        refine ⟨277522673252681449217035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1480120924014301062490853 277522673252681449217035)
        ·
          refine ⟨416284009879022173825553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277522673252681449217035 416284009879022173825553)
          ·
            refine ⟨312213007409266630369165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416284009879022173825553 312213007409266630369165)
            ·
              refine ⟨117079877778474986388437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312213007409266630369165 117079877778474986388437)
              ·
                refine ⟨2744059635433007493479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117079877778474986388437 2744059635433007493479)
                ·
                  rfl

theorem cell23_144289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 7].length) (baseStart_144289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144289 prefixEnd_144289 := by exact prefixLift 144289
  have htrace : WordTrace (prefixWord ++ tailWord_144289) baseStart_144289 baseEnd_144289 := by
    simpa [prefixWord, tailWord_144289, baseEnd_144289] using wordTrace_append hprefix tailTrace_144289
  have hstable : (prefixWord ++ tailWord_144289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144289).length < 2 ^ (prefixWord ++ tailWord_144289).sum := by decide
  have hdescent : baseEnd_144289 < baseStart_144289 := by decide
  rcases family_descends (prefixWord ++ tailWord_144289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144310 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_144310 : Nat := 118140960795 + 144310 * 2 ^ 59
def prefixEnd_144310 : Nat := 4983230072969 + 3 ^ 40 * 144310 * 2
def baseEnd_144310 : Nat := 24700131083478540053779

theorem tailTrace_144310 : CollatzResearch.WordTrace tailWord_144310 prefixEnd_144310 24700131083478540053779 := by
  unfold tailWord_144310
  simp only [CollatzResearch.WordTrace]
  refine ⟨328963631699811939432899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3508945404797994020617589 328963631699811939432899)
  ·
    refine ⟨493445447549717909149349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328963631699811939432899 493445447549717909149349)
    ·
      refine ⟨92521021415572107965503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 493445447549717909149349 92521021415572107965503)
      ·
        refine ⟨138781532123358161948255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92521021415572107965503 138781532123358161948255)
        ·
          refine ⟨208172298185037242922383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138781532123358161948255 208172298185037242922383)
          ·
            refine ⟨312258447277555864383575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208172298185037242922383 312258447277555864383575)
            ·
              refine ⟨468387670916333796575363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312258447277555864383575 468387670916333796575363)
              ·
                refine ⟨702581506374500694863045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468387670916333796575363 702581506374500694863045)
                ·
                  refine ⟨131734032445218880286821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702581506374500694863045 131734032445218880286821)
                  ·
                    refine ⟨24700131083478540053779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131734032445218880286821 24700131083478540053779)
                    ·
                      rfl

theorem cell23_144310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_144310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144310 prefixEnd_144310 := by exact prefixLift 144310
  have htrace : WordTrace (prefixWord ++ tailWord_144310) baseStart_144310 baseEnd_144310 := by
    simpa [prefixWord, tailWord_144310, baseEnd_144310] using wordTrace_append hprefix tailTrace_144310
  have hstable : (prefixWord ++ tailWord_144310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144310).length < 2 ^ (prefixWord ++ tailWord_144310).sum := by decide
  have hdescent : baseEnd_144310 < baseStart_144310 := by decide
  rcases family_descends (prefixWord ++ tailWord_144310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144332 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_144332 : Nat := 118140960795 + 144332 * 2 ^ 59
def prefixEnd_144332 : Nat := 4983230072969 + 3 ^ 40 * 144332 * 2
def baseEnd_144332 : Nat := 24703896608278178028745

theorem tailTrace_144332 : CollatzResearch.WordTrace tailWord_144332 prefixEnd_144332 24703896608278178028745 := by
  unfold tailWord_144332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632110256558644394113625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3509480342078192525484833 2632110256558644394113625)
  ·
    refine ⟨1974082692418983295585219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2632110256558644394113625 1974082692418983295585219)
    ·
      refine ⟨2961124038628474943377829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974082692418983295585219 2961124038628474943377829)
      ·
        refine ⟨555210757242839051883343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2961124038628474943377829 555210757242839051883343)
        ·
          refine ⟨832816135864258577825015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555210757242839051883343 832816135864258577825015)
          ·
            refine ⟨1249224203796387866737523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832816135864258577825015 1249224203796387866737523)
            ·
              refine ⟨1873836305694581800106285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249224203796387866737523 1873836305694581800106285)
              ·
                refine ⟨702688614635468175039857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1873836305694581800106285 702688614635468175039857)
                ·
                  refine ⟨527016460976601131279893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 702688614635468175039857 527016460976601131279893)
                  ·
                    refine ⟨24703896608278178028745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 527016460976601131279893 24703896608278178028745)
                    ·
                      rfl

theorem cell23_144332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_144332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144332 prefixEnd_144332 := by exact prefixLift 144332
  have htrace : WordTrace (prefixWord ++ tailWord_144332) baseStart_144332 baseEnd_144332 := by
    simpa [prefixWord, tailWord_144332, baseEnd_144332] using wordTrace_append hprefix tailTrace_144332
  have hstable : (prefixWord ++ tailWord_144332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144332).length < 2 ^ (prefixWord ++ tailWord_144332).sum := by decide
  have hdescent : baseEnd_144332 < baseStart_144332 := by decide
  rcases family_descends (prefixWord ++ tailWord_144332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144359 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_144359 : Nat := 118140960795 + 144359 * 2 ^ 59
def prefixEnd_144359 : Nat := 4983230072969 + 3 ^ 40 * 144359 * 2
def baseEnd_144359 : Nat := 74125553802505928448611

theorem tailTrace_144359 : CollatzResearch.WordTrace tailWord_144359 prefixEnd_144359 74125553802505928448611 := by
  unfold tailWord_144359
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265205284019472399460131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3510136856012981599640087 5265205284019472399460131)
  ·
    refine ⟨7897807926029208599190197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5265205284019472399460131 7897807926029208599190197)
    ·
      refine ⟨740419493065238306174081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7897807926029208599190197 740419493065238306174081)
      ·
        refine ⟨555314619798928729630561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 740419493065238306174081 555314619798928729630561)
        ·
          refine ⟨416485964849196547222921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555314619798928729630561 416485964849196547222921)
          ·
            refine ⟨312364473636897410417191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416485964849196547222921 312364473636897410417191)
            ·
              refine ⟨468546710455346115625787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312364473636897410417191 468546710455346115625787)
              ·
                refine ⟨702820065683019173438681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468546710455346115625787 702820065683019173438681)
                ·
                  refine ⟨527115049262264380079011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 702820065683019173438681 527115049262264380079011)
                  ·
                    refine ⟨790672573893396570118517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 527115049262264380079011 790672573893396570118517)
                    ·
                      refine ⟨74125553802505928448611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 790672573893396570118517 74125553802505928448611)
                      ·
                        rfl

theorem cell23_144359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_144359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144359 prefixEnd_144359 := by exact prefixLift 144359
  have htrace : WordTrace (prefixWord ++ tailWord_144359) baseStart_144359 baseEnd_144359 := by
    simpa [prefixWord, tailWord_144359, baseEnd_144359] using wordTrace_append hprefix tailTrace_144359
  have hstable : (prefixWord ++ tailWord_144359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144359).length < 2 ^ (prefixWord ++ tailWord_144359).sum := by decide
  have hdescent : baseEnd_144359 < baseStart_144359 := by decide
  rcases family_descends (prefixWord ++ tailWord_144359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144432 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_144432 : Nat := 118140960795 + 144432 * 2 ^ 59
def prefixEnd_144432 : Nat := 4983230072969 + 3 ^ 40 * 144432 * 2
def baseEnd_144432 : Nat := 74163037890284142835775

theorem tailTrace_144432 : CollatzResearch.WordTrace tailWord_144432 prefixEnd_144432 74163037890284142835775 := by
  unfold tailWord_144432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633933906377502933433775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3511911875170003911245033 2633933906377502933433775)
  ·
    refine ⟨3950900859566254400150663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2633933906377502933433775 3950900859566254400150663)
    ·
      refine ⟨5926351289349381600225995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3950900859566254400150663 5926351289349381600225995)
      ·
        refine ⟨8889526934024072400338993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926351289349381600225995 8889526934024072400338993)
        ·
          refine ⟨6667145200518054300254245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8889526934024072400338993 6667145200518054300254245)
          ·
            refine ⟨1250089725097135181297671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6667145200518054300254245 1250089725097135181297671)
            ·
              refine ⟨1875134587645702771946507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250089725097135181297671 1875134587645702771946507)
              ·
                refine ⟨2812701881468554157919761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875134587645702771946507 2812701881468554157919761)
                ·
                  refine ⟨2109526411101415618439821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812701881468554157919761 2109526411101415618439821)
                  ·
                    refine ⟨791072404163030856914933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109526411101415618439821 791072404163030856914933)
                    ·
                      refine ⟨74163037890284142835775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 791072404163030856914933 74163037890284142835775)
                      ·
                        rfl

theorem cell23_144432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_144432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144432 prefixEnd_144432 := by exact prefixLift 144432
  have htrace : WordTrace (prefixWord ++ tailWord_144432) baseStart_144432 baseEnd_144432 := by
    simpa [prefixWord, tailWord_144432, baseEnd_144432] using wordTrace_append hprefix tailTrace_144432
  have hstable : (prefixWord ++ tailWord_144432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144432).length < 2 ^ (prefixWord ++ tailWord_144432).sum := by decide
  have hdescent : baseEnd_144432 < baseStart_144432 := by decide
  rcases family_descends (prefixWord ++ tailWord_144432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144436 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_144436 : Nat := 118140960795 + 144436 * 2 ^ 59
def prefixEnd_144436 : Nat := 4983230072969 + 3 ^ 40 * 144436 * 2
def baseEnd_144436 : Nat := 74165091812902127185757

theorem tailTrace_144436 : CollatzResearch.WordTrace tailWord_144436 prefixEnd_144436 74165091812902127185757 := by
  unfold tailWord_144436
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634006852370257275006581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3512009136493676366675441 2634006852370257275006581)
  ·
    refine ⟨246938142409711619531867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2634006852370257275006581 246938142409711619531867)
    ·
      refine ⟨370407213614567429297801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246938142409711619531867 370407213614567429297801)
      ·
        refine ⟨277805410210925571973351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370407213614567429297801 277805410210925571973351)
        ·
          refine ⟨416708115316388357960027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277805410210925571973351 416708115316388357960027)
          ·
            refine ⟨625062172974582536940041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416708115316388357960027 625062172974582536940041)
            ·
              refine ⟨468796629730936902705031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625062172974582536940041 468796629730936902705031)
              ·
                refine ⟨703194944596405354057547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468796629730936902705031 703194944596405354057547)
                ·
                  refine ⟨1054792416894608031086321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703194944596405354057547 1054792416894608031086321)
                  ·
                    refine ⟨791094312670956023314741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054792416894608031086321 791094312670956023314741)
                    ·
                      refine ⟨74165091812902127185757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 791094312670956023314741 74165091812902127185757)
                      ·
                        rfl

theorem cell23_144436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_144436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144436 prefixEnd_144436 := by exact prefixLift 144436
  have htrace : WordTrace (prefixWord ++ tailWord_144436) baseStart_144436 baseEnd_144436 := by
    simpa [prefixWord, tailWord_144436, baseEnd_144436] using wordTrace_append hprefix tailTrace_144436
  have hstable : (prefixWord ++ tailWord_144436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144436).length < 2 ^ (prefixWord ++ tailWord_144436).sum := by decide
  have hdescent : baseEnd_144436 < baseStart_144436 := by decide
  rcases family_descends (prefixWord ++ tailWord_144436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144439 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 3, 4]
def baseStart_144439 : Nat := 118140960795 + 144439 * 2 ^ 59
def prefixEnd_144439 : Nat := 4983230072969 + 3 ^ 40 * 144439 * 2
def baseEnd_144439 : Nat := 24722210751621871816081

theorem tailTrace_144439 : CollatzResearch.WordTrace tailWord_144439 prefixEnd_144439 24722210751621871816081 := by
  unfold tailWord_144439
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268123123729646062372371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3512082082486430708248247 5268123123729646062372371)
  ·
    refine ⟨7902184685594469093558557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5268123123729646062372371 7902184685594469093558557)
    ·
      refine ⟨2963319257097925910084459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7902184685594469093558557 2963319257097925910084459)
      ·
        refine ⟨4444978885646888865126689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963319257097925910084459 4444978885646888865126689)
        ·
          refine ⟨3333734164235166648845017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4444978885646888865126689 3333734164235166648845017)
          ·
            refine ⟨2500300623176374986633763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333734164235166648845017 2500300623176374986633763)
            ·
              refine ⟨3750450934764562479950645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500300623176374986633763 3750450934764562479950645)
              ·
                refine ⟨351604775134177732495373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3750450934764562479950645 351604775134177732495373)
                ·
                  refine ⟨131851790675316649685765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351604775134177732495373 131851790675316649685765)
                  ·
                    refine ⟨24722210751621871816081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131851790675316649685765 24722210751621871816081)
                    ·
                      rfl

theorem cell23_144439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_144439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144439 prefixEnd_144439 := by exact prefixLift 144439
  have htrace : WordTrace (prefixWord ++ tailWord_144439) baseStart_144439 baseEnd_144439 := by
    simpa [prefixWord, tailWord_144439, baseEnd_144439] using wordTrace_append hprefix tailTrace_144439
  have hstable : (prefixWord ++ tailWord_144439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144439).length < 2 ^ (prefixWord ++ tailWord_144439).sum := by decide
  have hdescent : baseEnd_144439 < baseStart_144439 := by decide
  rcases family_descends (prefixWord ++ tailWord_144439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144466 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_144466 : Nat := 118140960795 + 144466 * 2 ^ 59
def prefixEnd_144466 : Nat := 4983230072969 + 3 ^ 40 * 144466 * 2
def baseEnd_144466 : Nat := 74180496232537009810619

theorem tailTrace_144466 : CollatzResearch.WordTrace tailWord_144466 prefixEnd_144466 74180496232537009810619 := by
  unfold tailWord_144466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317276973657957418401313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3512738596421219782403501 1317276973657957418401313)
  ·
    refine ⟨987957730243468063800985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1317276973657957418401313 987957730243468063800985)
    ·
      refine ⟨740968297682601047850739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 987957730243468063800985 740968297682601047850739)
      ·
        refine ⟨1111452446523901571776109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740968297682601047850739 1111452446523901571776109)
        ·
          refine ⟨416794667446463089416041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1111452446523901571776109 416794667446463089416041)
          ·
            refine ⟨312596000584847317062031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416794667446463089416041 312596000584847317062031)
            ·
              refine ⟨468894000877270975593047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312596000584847317062031 468894000877270975593047)
              ·
                refine ⟨703341001315906463389571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468894000877270975593047 703341001315906463389571)
                ·
                  refine ⟨1055011501973859695084357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703341001315906463389571 1055011501973859695084357)
                  ·
                    refine ⟨197814656620098692828317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1055011501973859695084357 197814656620098692828317)
                    ·
                      refine ⟨74180496232537009810619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197814656620098692828317 74180496232537009810619)
                      ·
                        rfl

theorem cell23_144466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_144466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144466 prefixEnd_144466 := by exact prefixLift 144466
  have htrace : WordTrace (prefixWord ++ tailWord_144466) baseStart_144466 baseEnd_144466 := by
    simpa [prefixWord, tailWord_144466, baseEnd_144466] using wordTrace_append hprefix tailTrace_144466
  have hstable : (prefixWord ++ tailWord_144466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144466).length < 2 ^ (prefixWord ++ tailWord_144466).sum := by decide
  have hdescent : baseEnd_144466 < baseStart_144466 := by decide
  rcases family_descends (prefixWord ++ tailWord_144466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144513 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_144513 : Nat := 118140960795 + 144513 * 2 ^ 59
def prefixEnd_144513 : Nat := 4983230072969 + 3 ^ 40 * 144513 * 2
def baseEnd_144513 : Nat := 74204629823298325922903

theorem tailTrace_144513 : CollatzResearch.WordTrace tailWord_144513 prefixEnd_144513 74204629823298325922903 := by
  unfold tailWord_144513
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270822125461556700566193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3513881416974371133710795 5270822125461556700566193)
  ·
    refine ⟨3953116594096167525424645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5270822125461556700566193 3953116594096167525424645)
    ·
      refine ⟨741209361393031411017121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3953116594096167525424645 741209361393031411017121)
      ·
        refine ⟨555907021044773558262841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 741209361393031411017121 555907021044773558262841)
        ·
          refine ⟨416930265783580168697131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555907021044773558262841 416930265783580168697131)
          ·
            refine ⟨625395398675370253045697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416930265783580168697131 625395398675370253045697)
            ·
              refine ⟨469046549006527689784273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625395398675370253045697 469046549006527689784273)
              ·
                refine ⟨351784911754895767338205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469046549006527689784273 351784911754895767338205)
                ·
                  refine ⟨131919341908085912751827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351784911754895767338205 131919341908085912751827)
                  ·
                    refine ⟨197879012862128869127741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131919341908085912751827 197879012862128869127741)
                    ·
                      refine ⟨74204629823298325922903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197879012862128869127741 74204629823298325922903)
                      ·
                        rfl

theorem cell23_144513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_144513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144513 prefixEnd_144513 := by exact prefixLift 144513
  have htrace : WordTrace (prefixWord ++ tailWord_144513) baseStart_144513 baseEnd_144513 := by
    simpa [prefixWord, tailWord_144513, baseEnd_144513] using wordTrace_append hprefix tailTrace_144513
  have hstable : (prefixWord ++ tailWord_144513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144513).length < 2 ^ (prefixWord ++ tailWord_144513).sum := by decide
  have hdescent : baseEnd_144513 < baseStart_144513 := by decide
  rcases family_descends (prefixWord ++ tailWord_144513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144516 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_144516 : Nat := 118140960795 + 144516 * 2 ^ 59
def prefixEnd_144516 : Nat := 4983230072969 + 3 ^ 40 * 144516 * 2
def baseEnd_144516 : Nat := 24735390088420604728463

theorem tailTrace_144516 : CollatzResearch.WordTrace tailWord_144516 prefixEnd_144516 24735390088420604728463 := by
  unfold tailWord_144516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635465772225344106462701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3513954362967125475283601 2635465772225344106462701)
  ·
    refine ⟨988299664584504039923513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2635465772225344106462701 988299664584504039923513)
    ·
      refine ⟨741224748438378029942635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 988299664584504039923513 741224748438378029942635)
      ·
        refine ⟨1111837122657567044913953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741224748438378029942635 1111837122657567044913953)
        ·
          refine ⟨833877841993175283685465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111837122657567044913953 833877841993175283685465)
          ·
            refine ⟨625408381494881462764099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833877841993175283685465 625408381494881462764099)
            ·
              refine ⟨938112572242322194146149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625408381494881462764099 938112572242322194146149)
              ·
                refine ⟨175896107295435411402403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 938112572242322194146149 175896107295435411402403)
                ·
                  refine ⟨263844160943153117103605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175896107295435411402403 263844160943153117103605)
                  ·
                    refine ⟨24735390088420604728463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 263844160943153117103605 24735390088420604728463)
                    ·
                      rfl

theorem cell23_144516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_144516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144516 prefixEnd_144516 := by exact prefixLift 144516
  have htrace : WordTrace (prefixWord ++ tailWord_144516) baseStart_144516 baseEnd_144516 := by
    simpa [prefixWord, tailWord_144516, baseEnd_144516] using wordTrace_append hprefix tailTrace_144516
  have hstable : (prefixWord ++ tailWord_144516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144516).length < 2 ^ (prefixWord ++ tailWord_144516).sum := by decide
  have hdescent : baseEnd_144516 < baseStart_144516 := by decide
  rcases family_descends (prefixWord ++ tailWord_144516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144549 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_144549 : Nat := 118140960795 + 144549 * 2 ^ 59
def prefixEnd_144549 : Nat := 4983230072969 + 3 ^ 40 * 144549 * 2
def baseEnd_144549 : Nat := 74223115126860185072737

theorem tailTrace_144549 : CollatzResearch.WordTrace tailWord_144549 prefixEnd_144549 74223115126860185072737 := by
  unfold tailWord_144549
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272135153331134848876701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3514756768887423232584467 5272135153331134848876701)
  ·
    refine ⟨1977050682499175568328763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5272135153331134848876701 1977050682499175568328763)
    ·
      refine ⟨2965576023748763352493145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1977050682499175568328763 2965576023748763352493145)
      ·
        refine ⟨2224182017811572514369859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2965576023748763352493145 2224182017811572514369859)
        ·
          refine ⟨3336273026717358771554789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224182017811572514369859 3336273026717358771554789)
          ·
            refine ⟨625551192509504769666523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3336273026717358771554789 625551192509504769666523)
            ·
              refine ⟨938326788764257154499785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625551192509504769666523 938326788764257154499785)
              ·
                refine ⟨703745091573192865874839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938326788764257154499785 703745091573192865874839)
                ·
                  refine ⟨1055617637359789298812259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703745091573192865874839 1055617637359789298812259)
                  ·
                    refine ⟨1583426456039683948218389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1055617637359789298812259 1583426456039683948218389)
                    ·
                      refine ⟨74223115126860185072737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1583426456039683948218389 74223115126860185072737)
                      ·
                        rfl

theorem cell23_144549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_144549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144549 prefixEnd_144549 := by exact prefixLift 144549
  have htrace : WordTrace (prefixWord ++ tailWord_144549) baseStart_144549 baseEnd_144549 := by
    simpa [prefixWord, tailWord_144549, baseEnd_144549] using wordTrace_append hprefix tailTrace_144549
  have hstable : (prefixWord ++ tailWord_144549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144549).length < 2 ^ (prefixWord ++ tailWord_144549).sum := by decide
  have hdescent : baseEnd_144549 < baseStart_144549 := by decide
  rcases family_descends (prefixWord ++ tailWord_144549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144563 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 2, 4]
def baseStart_144563 : Nat := 118140960795 + 144563 * 2 ^ 59
def prefixEnd_144563 : Nat := 4983230072969 + 3 ^ 40 * 144563 * 2
def baseEnd_144563 : Nat := 24743434618674376765891

theorem tailTrace_144563 : CollatzResearch.WordTrace tailWord_144563 prefixEnd_144563 24743434618674376765891 := by
  unfold tailWord_144563
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272645775280415239886343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3515097183520276826590895 5272645775280415239886343)
  ·
    refine ⟨7908968662920622859829515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5272645775280415239886343 7908968662920622859829515)
    ·
      refine ⟨11863452994380934289744273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7908968662920622859829515 11863452994380934289744273)
      ·
        refine ⟨8897589745785700717308205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11863452994380934289744273 8897589745785700717308205)
        ·
          refine ⟨3336596154669637768990577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8897589745785700717308205 3336596154669637768990577)
          ·
            refine ⟨2502447116002228326742933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3336596154669637768990577 2502447116002228326742933)
            ·
              refine ⟨117302208562604452816075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2502447116002228326742933 117302208562604452816075)
              ·
                refine ⟨175953312843906679224113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117302208562604452816075 175953312843906679224113)
                ·
                  refine ⟨131964984632930009418085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175953312843906679224113 131964984632930009418085)
                  ·
                    refine ⟨24743434618674376765891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131964984632930009418085 24743434618674376765891)
                    ·
                      rfl

theorem cell23_144563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 4].length) (baseStart_144563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144563 prefixEnd_144563 := by exact prefixLift 144563
  have htrace : WordTrace (prefixWord ++ tailWord_144563) baseStart_144563 baseEnd_144563 := by
    simpa [prefixWord, tailWord_144563, baseEnd_144563] using wordTrace_append hprefix tailTrace_144563
  have hstable : (prefixWord ++ tailWord_144563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144563).length < 2 ^ (prefixWord ++ tailWord_144563).sum := by decide
  have hdescent : baseEnd_144563 < baseStart_144563 := by decide
  rcases family_descends (prefixWord ++ tailWord_144563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144573 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_144573 : Nat := 118140960795 + 144573 * 2 ^ 59
def prefixEnd_144573 : Nat := 4983230072969 + 3 ^ 40 * 144573 * 2
def baseEnd_144573 : Nat := 74235438662568091172627

theorem tailTrace_144573 : CollatzResearch.WordTrace tailWord_144573 prefixEnd_144573 74235438662568091172627 := by
  unfold tailWord_144573
  simp only [CollatzResearch.WordTrace]
  refine ⟨5273010505244186947750373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3515340336829457965166915 5273010505244186947750373)
  ·
    refine ⟨988689469733285052703195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5273010505244186947750373 988689469733285052703195)
    ·
      refine ⟨1483034204599927579054793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988689469733285052703195 1483034204599927579054793)
      ·
        refine ⟨1112275653449945684291095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1483034204599927579054793 1112275653449945684291095)
        ·
          refine ⟨1668413480174918526436643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112275653449945684291095 1668413480174918526436643)
          ·
            refine ⟨2502620220262377789654965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668413480174918526436643 2502620220262377789654965)
            ·
              refine ⟨234620645649597917780153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2502620220262377789654965 234620645649597917780153)
              ·
                refine ⟨175965484237198438335115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234620645649597917780153 175965484237198438335115)
                ·
                  refine ⟨263948226355797657502673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175965484237198438335115 263948226355797657502673)
                  ·
                    refine ⟨197961169766848243127005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 263948226355797657502673 197961169766848243127005)
                    ·
                      refine ⟨74235438662568091172627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197961169766848243127005 74235438662568091172627)
                      ·
                        rfl

theorem cell23_144573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_144573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144573 prefixEnd_144573 := by exact prefixLift 144573
  have htrace : WordTrace (prefixWord ++ tailWord_144573) baseStart_144573 baseEnd_144573 := by
    simpa [prefixWord, tailWord_144573, baseEnd_144573] using wordTrace_append hprefix tailTrace_144573
  have hstable : (prefixWord ++ tailWord_144573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144573).length < 2 ^ (prefixWord ++ tailWord_144573).sum := by decide
  have hdescent : baseEnd_144573 < baseStart_144573 := by decide
  rcases family_descends (prefixWord ++ tailWord_144573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144586 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_144586 : Nat := 118140960795 + 144586 * 2 ^ 59
def prefixEnd_144586 : Nat := 4983230072969 + 3 ^ 40 * 144586 * 2
def baseEnd_144586 : Nat := 74242113911076540310067

theorem tailTrace_144586 : CollatzResearch.WordTrace tailWord_144586 prefixEnd_144586 74242113911076540310067 := by
  unfold tailWord_144586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318371163549272541993403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3515656436131393445315741 1318371163549272541993403)
  ·
    refine ⟨1977556745323908812990105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318371163549272541993403 1977556745323908812990105)
    ·
      refine ⟨1483167558992931609742579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1977556745323908812990105 1483167558992931609742579)
      ·
        refine ⟨2224751338489397414613869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483167558992931609742579 2224751338489397414613869)
        ·
          refine ⟨834281751933524030480201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2224751338489397414613869 834281751933524030480201)
          ·
            refine ⟨625711313950143022860151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834281751933524030480201 625711313950143022860151)
            ·
              refine ⟨938566970925214534290227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625711313950143022860151 938566970925214534290227)
              ·
                refine ⟨1407850456387821801435341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938566970925214534290227 1407850456387821801435341)
                ·
                  refine ⟨527943921145433175538253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1407850456387821801435341 527943921145433175538253)
                  ·
                    refine ⟨197978970429537440826845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 527943921145433175538253 197978970429537440826845)
                    ·
                      refine ⟨74242113911076540310067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197978970429537440826845 74242113911076540310067)
                      ·
                        rfl

theorem cell23_144586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_144586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144586 prefixEnd_144586 := by exact prefixLift 144586
  have htrace : WordTrace (prefixWord ++ tailWord_144586) baseStart_144586 baseEnd_144586 := by
    simpa [prefixWord, tailWord_144586, baseEnd_144586] using wordTrace_append hprefix tailTrace_144586
  have hstable : (prefixWord ++ tailWord_144586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144586).length < 2 ^ (prefixWord ++ tailWord_144586).sum := by decide
  have hdescent : baseEnd_144586 < baseStart_144586 := by decide
  rcases family_descends (prefixWord ++ tailWord_144586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144590 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_144590 : Nat := 118140960795 + 144590 * 2 ^ 59
def prefixEnd_144590 : Nat := 4983230072969 + 3 ^ 40 * 144590 * 2
def baseEnd_144590 : Nat := 74244167833694524660049

theorem tailTrace_144590 : CollatzResearch.WordTrace tailWord_144590 prefixEnd_144590 74244167833694524660049 := by
  unfold tailWord_144590
  simp only [CollatzResearch.WordTrace]
  refine ⟨659203818272824856389903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3515753697455065900746149 659203818272824856389903)
  ·
    refine ⟨988805727409237284584855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659203818272824856389903 988805727409237284584855)
    ·
      refine ⟨1483208591113855926877283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988805727409237284584855 1483208591113855926877283)
      ·
        refine ⟨2224812886670783890315925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483208591113855926877283 2224812886670783890315925)
        ·
          refine ⟨104288104062692994858559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2224812886670783890315925 104288104062692994858559)
          ·
            refine ⟨156432156094039492287839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104288104062692994858559 156432156094039492287839)
            ·
              refine ⟨234648234141059238431759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156432156094039492287839 234648234141059238431759)
              ·
                refine ⟨351972351211588857647639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234648234141059238431759 351972351211588857647639)
                ·
                  refine ⟨527958526817383286471459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351972351211588857647639 527958526817383286471459)
                  ·
                    refine ⟨791937790226074929707189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 527958526817383286471459 791937790226074929707189)
                    ·
                      refine ⟨74244167833694524660049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 791937790226074929707189 74244167833694524660049)
                      ·
                        rfl

theorem cell23_144590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_144590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144590 prefixEnd_144590 := by exact prefixLift 144590
  have htrace : WordTrace (prefixWord ++ tailWord_144590) baseStart_144590 baseEnd_144590 := by
    simpa [prefixWord, tailWord_144590, baseEnd_144590] using wordTrace_append hprefix tailTrace_144590
  have hstable : (prefixWord ++ tailWord_144590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144590).length < 2 ^ (prefixWord ++ tailWord_144590).sum := by decide
  have hdescent : baseEnd_144590 < baseStart_144590 := by decide
  rcases family_descends (prefixWord ++ tailWord_144590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144598 : List Nat := [5, 2, 1, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_144598 : Nat := 118140960795 + 144598 * 2 ^ 59
def prefixEnd_144598 : Nat := 4983230072969 + 3 ^ 40 * 144598 * 2
def baseEnd_144598 : Nat := 74248275678930493360013

theorem tailTrace_144598 : CollatzResearch.WordTrace tailWord_144598 prefixEnd_144598 74248275678930493360013 := by
  unfold tailWord_144598
  simp only [CollatzResearch.WordTrace]
  refine ⟨329620145634601013588153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3515948220102410811606965 329620145634601013588153)
  ·
    refine ⟨247215109225950760191115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 329620145634601013588153 247215109225950760191115)
    ·
      refine ⟨370822663838926140286673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247215109225950760191115 370822663838926140286673)
      ·
        refine ⟨278116997879194605215005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370822663838926140286673 278116997879194605215005)
        ·
          refine ⟨104293874204697976955627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278116997879194605215005 104293874204697976955627)
          ·
            refine ⟨156440811307046965433441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104293874204697976955627 156440811307046965433441)
            ·
              refine ⟨117330608480285224075081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156440811307046965433441 117330608480285224075081)
              ·
                refine ⟨87997956360213918056311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117330608480285224075081 87997956360213918056311)
                ·
                  refine ⟨131996934540320877084467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87997956360213918056311 131996934540320877084467)
                  ·
                    refine ⟨197995401810481315626701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131996934540320877084467 197995401810481315626701)
                    ·
                      refine ⟨74248275678930493360013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 197995401810481315626701 74248275678930493360013)
                      ·
                        rfl

theorem cell23_144598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_144598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144598 prefixEnd_144598 := by exact prefixLift 144598
  have htrace : WordTrace (prefixWord ++ tailWord_144598) baseStart_144598 baseEnd_144598 := by
    simpa [prefixWord, tailWord_144598, baseEnd_144598] using wordTrace_append hprefix tailTrace_144598
  have hstable : (prefixWord ++ tailWord_144598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144598).length < 2 ^ (prefixWord ++ tailWord_144598).sum := by decide
  have hdescent : baseEnd_144598 < baseStart_144598 := by decide
  rcases family_descends (prefixWord ++ tailWord_144598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144599 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_144599 : Nat := 118140960795 + 144599 * 2 ^ 59
def prefixEnd_144599 : Nat := 4983230072969 + 3 ^ 40 * 144599 * 2
def baseEnd_144599 : Nat := 74248789159584989447507

theorem tailTrace_144599 : CollatzResearch.WordTrace tailWord_144599 prefixEnd_144599 74248789159584989447507 := by
  unfold tailWord_144599
  simp only [CollatzResearch.WordTrace]
  refine ⟨5273958803149993388196851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3515972535433328925464567 5273958803149993388196851)
  ·
    refine ⟨7910938204724990082295277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5273958803149993388196851 7910938204724990082295277)
    ·
      refine ⟨2966601826771871280860729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7910938204724990082295277 2966601826771871280860729)
      ·
        refine ⟨2224951370078903460645547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2966601826771871280860729 2224951370078903460645547)
        ·
          refine ⟨3337427055118355190968321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224951370078903460645547 3337427055118355190968321)
          ·
            refine ⟨2503070291338766393226241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337427055118355190968321 2503070291338766393226241)
            ·
              refine ⟨1877302718504074794919681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503070291338766393226241 1877302718504074794919681)
              ·
                refine ⟨1407977038878056096189761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877302718504074794919681 1407977038878056096189761)
                ·
                  refine ⟨1055982779158542072142321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1407977038878056096189761 1055982779158542072142321)
                  ·
                    refine ⟨791987084368906554106741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1055982779158542072142321 791987084368906554106741)
                    ·
                      refine ⟨74248789159584989447507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 791987084368906554106741 74248789159584989447507)
                      ·
                        rfl

theorem cell23_144599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_144599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144599 prefixEnd_144599 := by exact prefixLift 144599
  have htrace : WordTrace (prefixWord ++ tailWord_144599) baseStart_144599 baseEnd_144599 := by
    simpa [prefixWord, tailWord_144599, baseEnd_144599] using wordTrace_append hprefix tailTrace_144599
  have hstable : (prefixWord ++ tailWord_144599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144599).length < 2 ^ (prefixWord ++ tailWord_144599).sum := by decide
  have hdescent : baseEnd_144599 < baseStart_144599 := by decide
  rcases family_descends (prefixWord ++ tailWord_144599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144619 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 1, 8]
def baseStart_144619 : Nat := 118140960795 + 144619 * 2 ^ 59
def prefixEnd_144619 : Nat := 4983230072969 + 3 ^ 40 * 144619 * 2
def baseEnd_144619 : Nat := 24753019590891637065805

theorem tailTrace_144619 : CollatzResearch.WordTrace tailWord_144619 prefixEnd_144619 24753019590891637065805 := by
  unfold tailWord_144619
  simp only [CollatzResearch.WordTrace]
  refine ⟨5274688263077536803924911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3516458842051691202616607 5274688263077536803924911)
  ·
    refine ⟨7912032394616305205887367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5274688263077536803924911 7912032394616305205887367)
    ·
      refine ⟨11868048591924457808831051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7912032394616305205887367 11868048591924457808831051)
      ·
        refine ⟨17802072887886686713246577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11868048591924457808831051 17802072887886686713246577)
        ·
          refine ⟨13351554665915015034934933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17802072887886686713246577 13351554665915015034934933)
          ·
            refine ⟨625854124964766329762575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13351554665915015034934933 625854124964766329762575)
            ·
              refine ⟨938781187447149494643863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625854124964766329762575 938781187447149494643863)
              ·
                refine ⟨1408171781170724241965795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938781187447149494643863 1408171781170724241965795)
                ·
                  refine ⟨2112257671756086362948693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408171781170724241965795 2112257671756086362948693)
                  ·
                    refine ⟨24753019590891637065805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2112257671756086362948693 24753019590891637065805)
                    ·
                      rfl

theorem cell23_144619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 8].length) (baseStart_144619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144619 prefixEnd_144619 := by exact prefixLift 144619
  have htrace : WordTrace (prefixWord ++ tailWord_144619) baseStart_144619 baseEnd_144619 := by
    simpa [prefixWord, tailWord_144619, baseEnd_144619] using wordTrace_append hprefix tailTrace_144619
  have hstable : (prefixWord ++ tailWord_144619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144619).length < 2 ^ (prefixWord ++ tailWord_144619).sum := by decide
  have hdescent : baseEnd_144619 < baseStart_144619 := by decide
  rcases family_descends (prefixWord ++ tailWord_144619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144630 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_144630 : Nat := 118140960795 + 144630 * 2 ^ 59
def prefixEnd_144630 : Nat := 4983230072969 + 3 ^ 40 * 144630 * 2
def baseEnd_144630 : Nat := 74264707059874368159865

theorem tailTrace_144630 : CollatzResearch.WordTrace tailWord_144630 prefixEnd_144630 74264707059874368159865 := by
  unfold tailWord_144630
  simp only [CollatzResearch.WordTrace]
  refine ⟨329693091627355355160959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3516726310691790455050229 329693091627355355160959)
  ·
    refine ⟨494539637441033032741439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329693091627355355160959 494539637441033032741439)
    ·
      refine ⟨741809456161549549112159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494539637441033032741439 741809456161549549112159)
      ·
        refine ⟨1112714184242324323668239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741809456161549549112159 1112714184242324323668239)
        ·
          refine ⟨1669071276363486485502359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112714184242324323668239 1669071276363486485502359)
          ·
            refine ⟨2503606914545229728253539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669071276363486485502359 2503606914545229728253539)
            ·
              refine ⟨3755410371817844592380309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503606914545229728253539 3755410371817844592380309)
              ·
                refine ⟨176034861178961465267827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3755410371817844592380309 176034861178961465267827)
                ·
                  refine ⟨264052291768442197901741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176034861178961465267827 264052291768442197901741)
                  ·
                    refine ⟨99019609413165824213153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264052291768442197901741 99019609413165824213153)
                    ·
                      refine ⟨74264707059874368159865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99019609413165824213153 74264707059874368159865)
                      ·
                        rfl

theorem cell23_144630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_144630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144630 prefixEnd_144630 := by exact prefixLift 144630
  have htrace : WordTrace (prefixWord ++ tailWord_144630) baseStart_144630 baseEnd_144630 := by
    simpa [prefixWord, tailWord_144630, baseEnd_144630] using wordTrace_append hprefix tailTrace_144630
  have hstable : (prefixWord ++ tailWord_144630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144630).length < 2 ^ (prefixWord ++ tailWord_144630).sum := by decide
  have hdescent : baseEnd_144630 < baseStart_144630 := by decide
  rcases family_descends (prefixWord ++ tailWord_144630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144643 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 1, 4, 2]
def baseStart_144643 : Nat := 118140960795 + 144643 * 2 ^ 59
def prefixEnd_144643 : Nat := 4983230072969 + 3 ^ 40 * 144643 * 2
def baseEnd_144643 : Nat := 74271382308382817297305

theorem tailTrace_144643 : CollatzResearch.WordTrace tailWord_144643 prefixEnd_144643 74271382308382817297305 := by
  unfold tailWord_144643
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275563614990588902798583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3517042409993725935199055 5275563614990588902798583)
  ·
    refine ⟨7913345422485883354197875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5275563614990588902798583 7913345422485883354197875)
    ·
      refine ⟨11870018133728825031296813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7913345422485883354197875 11870018133728825031296813)
      ·
        refine ⟨4451256800148309386736305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11870018133728825031296813 4451256800148309386736305)
        ·
          refine ⟨3338442600111232040052229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4451256800148309386736305 3338442600111232040052229)
          ·
            refine ⟨625957987520856007509793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3338442600111232040052229 625957987520856007509793)
            ·
              refine ⟨469468490640642005632345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625957987520856007509793 469468490640642005632345)
              ·
                refine ⟨352101367980481504224259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469468490640642005632345 352101367980481504224259)
                ·
                  refine ⟨528152051970722256336389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352101367980481504224259 528152051970722256336389)
                  ·
                    refine ⟨99028509744510423063073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528152051970722256336389 99028509744510423063073)
                    ·
                      refine ⟨74271382308382817297305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99028509744510423063073 74271382308382817297305)
                      ·
                        rfl

theorem cell23_144643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_144643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144643 prefixEnd_144643 := by exact prefixLift 144643
  have htrace : WordTrace (prefixWord ++ tailWord_144643) baseStart_144643 baseEnd_144643 := by
    simpa [prefixWord, tailWord_144643, baseEnd_144643] using wordTrace_append hprefix tailTrace_144643
  have hstable : (prefixWord ++ tailWord_144643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144643).length < 2 ^ (prefixWord ++ tailWord_144643).sum := by decide
  have hdescent : baseEnd_144643 < baseStart_144643 := by decide
  rcases family_descends (prefixWord ++ tailWord_144643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144649 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 9]
def baseStart_144649 : Nat := 118140960795 + 144649 * 2 ^ 59
def prefixEnd_144649 : Nat := 4983230072969 + 3 ^ 40 * 144649 * 2
def baseEnd_144649 : Nat := 8252718132478865980253

theorem tailTrace_144649 : CollatzResearch.WordTrace tailWord_144649 prefixEnd_144649 8252718132478865980253 := by
  unfold tailWord_144649
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275782452968851927517001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3517188301979234618344667 5275782452968851927517001)
  ·
    refine ⟨3956836839726638945637751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5275782452968851927517001 3956836839726638945637751)
    ·
      refine ⟨5935255259589958418456627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3956836839726638945637751 5935255259589958418456627)
      ·
        refine ⟨8902882889384937627684941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5935255259589958418456627 8902882889384937627684941)
        ·
          refine ⟨3338581083519351610381853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8902882889384937627684941 3338581083519351610381853)
          ·
            refine ⟨1251967906319756853893195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3338581083519351610381853 1251967906319756853893195)
            ·
              refine ⟨1877951859479635280839793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251967906319756853893195 1877951859479635280839793)
              ·
                refine ⟨1408463894609726460629845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877951859479635280839793 1408463894609726460629845)
                ·
                  refine ⟨8252718132478865980253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1408463894609726460629845 8252718132478865980253)
                  ·
                    rfl

theorem cell23_144649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_144649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144649 prefixEnd_144649 := by exact prefixLift 144649
  have htrace : WordTrace (prefixWord ++ tailWord_144649) baseStart_144649 baseEnd_144649 := by
    simpa [prefixWord, tailWord_144649, baseEnd_144649] using wordTrace_append hprefix tailTrace_144649
  have hstable : (prefixWord ++ tailWord_144649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144649).length < 2 ^ (prefixWord ++ tailWord_144649).sum := by decide
  have hdescent : baseEnd_144649 < baseStart_144649 := by decide
  rcases family_descends (prefixWord ++ tailWord_144649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144666 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 7]
def baseStart_144666 : Nat := 118140960795 + 144666 * 2 ^ 59
def prefixEnd_144666 : Nat := 4983230072969 + 3 ^ 40 * 144666 * 2
def baseEnd_144666 : Nat := 8253688040381803034411

theorem tailTrace_144666 : CollatzResearch.WordTrace tailWord_144666 prefixEnd_144666 8253688040381803034411 := by
  unfold tailWord_144666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319100623476815957721463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3517601662604842553923901 1319100623476815957721463)
  ·
    refine ⟨1978650935215223936582195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1319100623476815957721463 1978650935215223936582195)
    ·
      refine ⟨2967976402822835904873293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978650935215223936582195 2967976402822835904873293)
      ·
        refine ⟨1112991151058563464327485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2967976402822835904873293 1112991151058563464327485)
        ·
          refine ⟨417371681646961299122807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1112991151058563464327485 417371681646961299122807)
          ·
            refine ⟨626057522470441948684211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417371681646961299122807 626057522470441948684211)
            ·
              refine ⟨939086283705662923026317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626057522470441948684211 939086283705662923026317)
              ·
                refine ⟨352157356389623596134869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939086283705662923026317 352157356389623596134869)
                ·
                  refine ⟨8253688040381803034411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 352157356389623596134869 8253688040381803034411)
                  ·
                    rfl

theorem cell23_144666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_144666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144666 prefixEnd_144666 := by exact prefixLift 144666
  have htrace : WordTrace (prefixWord ++ tailWord_144666) baseStart_144666 baseEnd_144666 := by
    simpa [prefixWord, tailWord_144666, baseEnd_144666] using wordTrace_append hprefix tailTrace_144666
  have hstable : (prefixWord ++ tailWord_144666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144666).length < 2 ^ (prefixWord ++ tailWord_144666).sum := by decide
  have hdescent : baseEnd_144666 < baseStart_144666 := by decide
  rcases family_descends (prefixWord ++ tailWord_144666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144696 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 2, 5]
def baseStart_144696 : Nat := 118140960795 + 144696 * 2 ^ 59
def prefixEnd_144696 : Nat := 4983230072969 + 3 ^ 40 * 144696 * 2
def baseEnd_144696 : Nat := 24766198927690369978187

theorem tailTrace_144696 : CollatzResearch.WordTrace tailWord_144696 prefixEnd_144696 24766198927690369978187 := by
  unfold tailWord_144696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638748341899289477238971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3518331122532385969651961 2638748341899289477238971)
  ·
    refine ⟨3958122512848934215858457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2638748341899289477238971 3958122512848934215858457)
    ·
      refine ⟨2968591884636700661893843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3958122512848934215858457 2968591884636700661893843)
      ·
        refine ⟨4452887826955050992840765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968591884636700661893843 4452887826955050992840765)
        ·
          refine ⟨1669832935108144122315287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4452887826955050992840765 1669832935108144122315287)
          ·
            refine ⟨2504749402662216183472931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669832935108144122315287 2504749402662216183472931)
            ·
              refine ⟨3757124103993324275209397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504749402662216183472931 3757124103993324275209397)
              ·
                refine ⟨352230384749374150800881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3757124103993324275209397 352230384749374150800881)
                ·
                  refine ⟨264172788562030613100661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352230384749374150800881 264172788562030613100661)
                  ·
                    refine ⟨24766198927690369978187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 264172788562030613100661 24766198927690369978187)
                    ·
                      rfl

theorem cell23_144696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_144696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144696 prefixEnd_144696 := by exact prefixLift 144696
  have htrace : WordTrace (prefixWord ++ tailWord_144696) baseStart_144696 baseEnd_144696 := by
    simpa [prefixWord, tailWord_144696, baseEnd_144696] using wordTrace_append hprefix tailTrace_144696
  have hstable : (prefixWord ++ tailWord_144696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144696).length < 2 ^ (prefixWord ++ tailWord_144696).sum := by decide
  have hdescent : baseEnd_144696 < baseStart_144696 := by decide
  rcases family_descends (prefixWord ++ tailWord_144696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144699 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8]
def baseStart_144699 : Nat := 118140960795 + 144699 * 2 ^ 59
def prefixEnd_144699 : Nat := 4983230072969 + 3 ^ 40 * 144699 * 2
def baseEnd_144699 : Nat := 74300137225034598197047

theorem tailTrace_144699 : CollatzResearch.WordTrace tailWord_144699 prefixEnd_144699 74300137225034598197047 := by
  unfold tailWord_144699
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277606102787710466837151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3518404068525140311224767 5277606102787710466837151)
  ·
    refine ⟨7916409154181565700255727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5277606102787710466837151 7916409154181565700255727)
    ·
      refine ⟨11874613731272348550383591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7916409154181565700255727 11874613731272348550383591)
      ·
        refine ⟨17811920596908522825575387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11874613731272348550383591 17811920596908522825575387)
        ·
          refine ⟨26717880895362784238363081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17811920596908522825575387 26717880895362784238363081)
          ·
            refine ⟨20038410671522088178772311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26717880895362784238363081 20038410671522088178772311)
            ·
              refine ⟨30057616007283132268158467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20038410671522088178772311 30057616007283132268158467)
              ·
                refine ⟨45086424010924698402237701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30057616007283132268158467 45086424010924698402237701)
                ·
                  refine ⟨8453704502048380950419569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45086424010924698402237701 8453704502048380950419569)
                  ·
                    refine ⟨6340278376536285712814677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8453704502048380950419569 6340278376536285712814677)
                    ·
                      refine ⟨74300137225034598197047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 6340278376536285712814677 74300137225034598197047)
                      ·
                        rfl

theorem cell23_144699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_144699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144699 prefixEnd_144699 := by exact prefixLift 144699
  have htrace : WordTrace (prefixWord ++ tailWord_144699) baseStart_144699 baseEnd_144699 := by
    simpa [prefixWord, tailWord_144699, baseEnd_144699] using wordTrace_append hprefix tailTrace_144699
  have hstable : (prefixWord ++ tailWord_144699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144699).length < 2 ^ (prefixWord ++ tailWord_144699).sum := by decide
  have hdescent : baseEnd_144699 < baseStart_144699 := by decide
  rcases family_descends (prefixWord ++ tailWord_144699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144700 : List Nat := [2, 2, 2, 2, 1, 5, 1, 3, 5]
def baseStart_144700 : Nat := 118140960795 + 144700 * 2 ^ 59
def prefixEnd_144700 : Nat := 4983230072969 + 3 ^ 40 * 144700 * 2
def baseEnd_144700 : Nat := 8255627856187677142727

theorem tailTrace_144700 : CollatzResearch.WordTrace tailWord_144700 prefixEnd_144700 8255627856187677142727 := by
  unfold tailWord_144700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638821287892043818811777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3518428383856058425082369 2638821287892043818811777)
  ·
    refine ⟨1979115965919032864108833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2638821287892043818811777 1979115965919032864108833)
    ·
      refine ⟨1484336974439274648081625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1979115965919032864108833 1484336974439274648081625)
      ·
        refine ⟨1113252730829455986061219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1484336974439274648081625 1113252730829455986061219)
        ·
          refine ⟨1669879096244183979091829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113252730829455986061219 1669879096244183979091829)
          ·
            refine ⟨156551165272892248039859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1669879096244183979091829 156551165272892248039859)
            ·
              refine ⟨234826747909338372059789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156551165272892248039859 234826747909338372059789)
              ·
                refine ⟨88060030466001889522421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234826747909338372059789 88060030466001889522421)
                ·
                  refine ⟨8255627856187677142727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88060030466001889522421 8255627856187677142727)
                  ·
                    rfl

theorem cell23_144700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_144700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144700 prefixEnd_144700 := by exact prefixLift 144700
  have htrace : WordTrace (prefixWord ++ tailWord_144700) baseStart_144700 baseEnd_144700 := by
    simpa [prefixWord, tailWord_144700, baseEnd_144700] using wordTrace_append hprefix tailTrace_144700
  have hstable : (prefixWord ++ tailWord_144700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144700).length < 2 ^ (prefixWord ++ tailWord_144700).sum := by decide
  have hdescent : baseEnd_144700 < baseStart_144700 := by decide
  rcases family_descends (prefixWord ++ tailWord_144700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144717 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 7]
def baseStart_144717 : Nat := 118140960795 + 144717 * 2 ^ 59
def prefixEnd_144717 : Nat := 4983230072969 + 3 ^ 40 * 144717 * 2
def baseEnd_144717 : Nat := 8256597764090614196885

theorem tailTrace_144717 : CollatzResearch.WordTrace tailWord_144717 prefixEnd_144717 8256597764090614196885 := by
  unfold tailWord_144717
  simp only [CollatzResearch.WordTrace]
  refine ⟨5278262616722499540992405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3518841744481666360661603 5278262616722499540992405)
  ·
    refine ⟨247418560158867165984019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5278262616722499540992405 247418560158867165984019)
    ·
      refine ⟨371127840238300748976029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247418560158867165984019 371127840238300748976029)
      ·
        refine ⟨139172940089362780866011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371127840238300748976029 139172940089362780866011)
        ·
          refine ⟨208759410134044171299017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139172940089362780866011 208759410134044171299017)
          ·
            refine ⟨156569557600533128474263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208759410134044171299017 156569557600533128474263)
            ·
              refine ⟨234854336400799692711395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156569557600533128474263 234854336400799692711395)
              ·
                refine ⟨352281504601199539067093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234854336400799692711395 352281504601199539067093)
                ·
                  refine ⟨8256597764090614196885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 352281504601199539067093 8256597764090614196885)
                  ·
                    rfl

theorem cell23_144717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_144717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144717 prefixEnd_144717 := by exact prefixLift 144717
  have htrace : WordTrace (prefixWord ++ tailWord_144717) baseStart_144717 baseEnd_144717 := by
    simpa [prefixWord, tailWord_144717, baseEnd_144717] using wordTrace_append hprefix tailTrace_144717
  have hstable : (prefixWord ++ tailWord_144717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144717).length < 2 ^ (prefixWord ++ tailWord_144717).sum := by decide
  have hdescent : baseEnd_144717 < baseStart_144717 := by decide
  rcases family_descends (prefixWord ++ tailWord_144717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144753 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_144753 : Nat := 118140960795 + 144753 * 2 ^ 59
def prefixEnd_144753 : Nat := 4983230072969 + 3 ^ 40 * 144753 * 2
def baseEnd_144753 : Nat := 74327865180377386921799

theorem tailTrace_144753 : CollatzResearch.WordTrace tailWord_144753 prefixEnd_144753 74327865180377386921799 := by
  unfold tailWord_144753
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279575644592077689302913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3519717096394718459535275 5279575644592077689302913)
  ·
    refine ⟨3959681733444058266977185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5279575644592077689302913 3959681733444058266977185)
    ·
      refine ⟨2969761300083043700232889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3959681733444058266977185 2969761300083043700232889)
      ·
        refine ⟨2227320975062282775174667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2969761300083043700232889 2227320975062282775174667)
        ·
          refine ⟨3340981462593424162762001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227320975062282775174667 3340981462593424162762001)
          ·
            refine ⟨2505736096945068122071501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3340981462593424162762001 2505736096945068122071501)
            ·
              refine ⟨939651036354400545776813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2505736096945068122071501 939651036354400545776813)
              ·
                refine ⟨352369138632900204666305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939651036354400545776813 352369138632900204666305)
                ·
                  refine ⟨264276853974675153499729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352369138632900204666305 264276853974675153499729)
                  ·
                    refine ⟨198207640481006365124797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264276853974675153499729 198207640481006365124797)
                    ·
                      refine ⟨74327865180377386921799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198207640481006365124797 74327865180377386921799)
                      ·
                        rfl

theorem cell23_144753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_144753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144753 prefixEnd_144753 := by exact prefixLift 144753
  have htrace : WordTrace (prefixWord ++ tailWord_144753) baseStart_144753 baseEnd_144753 := by
    simpa [prefixWord, tailWord_144753, baseEnd_144753] using wordTrace_append hprefix tailTrace_144753
  have hstable : (prefixWord ++ tailWord_144753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144753).length < 2 ^ (prefixWord ++ tailWord_144753).sum := by decide
  have hdescent : baseEnd_144753 < baseStart_144753 := by decide
  rcases family_descends (prefixWord ++ tailWord_144753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144777 : List Nat := [1, 2, 1, 1, 7, 1, 1, 4, 1, 4]
def baseStart_144777 : Nat := 118140960795 + 144777 * 2 ^ 59
def prefixEnd_144777 : Nat := 4983230072969 + 3 ^ 40 * 144777 * 2
def baseEnd_144777 : Nat := 24780062905361764340563

theorem tailTrace_144777 : CollatzResearch.WordTrace tailWord_144777 prefixEnd_144777 24780062905361764340563 := by
  unfold tailWord_144777
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280450996505129788176585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3520300664336753192117723 5280450996505129788176585)
  ·
    refine ⟨3960338247378847341132439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5280450996505129788176585 3960338247378847341132439)
    ·
      refine ⟨5940507371068271011698659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3960338247378847341132439 5940507371068271011698659)
      ·
        refine ⟨8910761056602406517547989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5940507371068271011698659 8910761056602406517547989)
        ·
          refine ⟨208845962264118902755031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8910761056602406517547989 208845962264118902755031)
          ·
            refine ⟨313268943396178354132547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208845962264118902755031 313268943396178354132547)
            ·
              refine ⟨469903415094267531198821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313268943396178354132547 469903415094267531198821)
              ·
                refine ⟨88106890330175162099779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469903415094267531198821 88106890330175162099779)
                ·
                  refine ⟨132160335495262743149669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88106890330175162099779 132160335495262743149669)
                  ·
                    refine ⟨24780062905361764340563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132160335495262743149669 24780062905361764340563)
                    ·
                      rfl

theorem cell23_144777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 4].length) (baseStart_144777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144777 prefixEnd_144777 := by exact prefixLift 144777
  have htrace : WordTrace (prefixWord ++ tailWord_144777) baseStart_144777 baseEnd_144777 := by
    simpa [prefixWord, tailWord_144777, baseEnd_144777] using wordTrace_append hprefix tailTrace_144777
  have hstable : (prefixWord ++ tailWord_144777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144777).length < 2 ^ (prefixWord ++ tailWord_144777).sum := by decide
  have hdescent : baseEnd_144777 < baseStart_144777 := by decide
  rcases family_descends (prefixWord ++ tailWord_144777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144800 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 3, 1, 3]
def baseStart_144800 : Nat := 118140960795 + 144800 * 2 ^ 59
def prefixEnd_144800 : Nat := 4983230072969 + 3 ^ 40 * 144800 * 2
def baseEnd_144800 : Nat := 74351998771138703034083

theorem tailTrace_144800 : CollatzResearch.WordTrace tailWord_144800 prefixEnd_144800 74351998771138703034083 := by
  unfold tailWord_144800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640644937710902358131927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3520859916947869810842569 2640644937710902358131927)
  ·
    refine ⟨3960967406566353537197891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640644937710902358131927 3960967406566353537197891)
    ·
      refine ⟨5941451109849530305796837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3960967406566353537197891 5941451109849530305796837)
      ·
        refine ⟨1114022083096786932336907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5941451109849530305796837 1114022083096786932336907)
        ·
          refine ⟨1671033124645180398505361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114022083096786932336907 1671033124645180398505361)
          ·
            refine ⟨1253274843483885298879021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1671033124645180398505361 1253274843483885298879021)
            ·
              refine ⟨469978066306456987079633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1253274843483885298879021 469978066306456987079633)
              ·
                refine ⟨352483549729842740309725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469978066306456987079633 352483549729842740309725)
                ·
                  refine ⟨132181331148691027616147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352483549729842740309725 132181331148691027616147)
                  ·
                    refine ⟨198271996723036541424221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 132181331148691027616147 198271996723036541424221)
                    ·
                      refine ⟨74351998771138703034083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198271996723036541424221 74351998771138703034083)
                      ·
                        rfl

theorem cell23_144800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_144800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144800 prefixEnd_144800 := by exact prefixLift 144800
  have htrace : WordTrace (prefixWord ++ tailWord_144800) baseStart_144800 baseEnd_144800 := by
    simpa [prefixWord, tailWord_144800, baseEnd_144800] using wordTrace_append hprefix tailTrace_144800
  have hstable : (prefixWord ++ tailWord_144800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144800).length < 2 ^ (prefixWord ++ tailWord_144800).sum := by decide
  have hdescent : baseEnd_144800 < baseStart_144800 := by decide
  rcases family_descends (prefixWord ++ tailWord_144800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144803 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 1, 5]
def baseStart_144803 : Nat := 118140960795 + 144803 * 2 ^ 59
def prefixEnd_144803 : Nat := 4983230072969 + 3 ^ 40 * 144803 * 2
def baseEnd_144803 : Nat := 24784513071034063765523

theorem tailTrace_144803 : CollatzResearch.WordTrace tailWord_144803 prefixEnd_144803 24784513071034063765523 := by
  unfold tailWord_144803
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281399294410936228623063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3520932862940624152415375 5281399294410936228623063)
  ·
    refine ⟨7922098941616404342934595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5281399294410936228623063 7922098941616404342934595)
    ·
      refine ⟨11883148412424606514401893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7922098941616404342934595 11883148412424606514401893)
      ·
        refine ⟨2228090327329613721450355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11883148412424606514401893 2228090327329613721450355)
        ·
          refine ⟨3342135490994420582175533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228090327329613721450355 3342135490994420582175533)
          ·
            refine ⟨1253300809122907718315825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3342135490994420582175533 1253300809122907718315825)
            ·
              refine ⟨939975606842180788736869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253300809122907718315825 939975606842180788736869)
              ·
                refine ⟨176245426282908897888163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 939975606842180788736869 176245426282908897888163)
                ·
                  refine ⟨264368139424363346832245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176245426282908897888163 264368139424363346832245)
                  ·
                    refine ⟨24784513071034063765523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 264368139424363346832245 24784513071034063765523)
                    ·
                      rfl

theorem cell23_144803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 5].length) (baseStart_144803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144803 prefixEnd_144803 := by exact prefixLift 144803
  have htrace : WordTrace (prefixWord ++ tailWord_144803) baseStart_144803 baseEnd_144803 := by
    simpa [prefixWord, tailWord_144803, baseEnd_144803] using wordTrace_append hprefix tailTrace_144803
  have hstable : (prefixWord ++ tailWord_144803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144803).length < 2 ^ (prefixWord ++ tailWord_144803).sum := by decide
  have hdescent : baseEnd_144803 < baseStart_144803 := by decide
  rcases family_descends (prefixWord ++ tailWord_144803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144816 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 3, 6]
def baseStart_144816 : Nat := 118140960795 + 144816 * 2 ^ 59
def prefixEnd_144816 : Nat := 4983230072969 + 3 ^ 40 * 144816 * 2
def baseEnd_144816 : Nat := 24786738153870213478003

theorem tailTrace_144816 : CollatzResearch.WordTrace tailWord_144816 prefixEnd_144816 24786738153870213478003 := by
  unfold tailWord_144816
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640936721681919724423151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3521248962242559632564201 2640936721681919724423151)
  ·
    refine ⟨3961405082522879586634727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640936721681919724423151 3961405082522879586634727)
    ·
      refine ⟨5942107623784319379952091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3961405082522879586634727 5942107623784319379952091)
      ·
        refine ⟨8913161435676479069928137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5942107623784319379952091 8913161435676479069928137)
        ·
          refine ⟨6684871076757359302446103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8913161435676479069928137 6684871076757359302446103)
          ·
            refine ⟨10027306615136038953669155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6684871076757359302446103 10027306615136038953669155)
            ·
              refine ⟨15040959922704058430503733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10027306615136038953669155 15040959922704058430503733)
              ·
                refine ⟨1410089992753505477859725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15040959922704058430503733 1410089992753505477859725)
                ·
                  refine ⟨528783747282564554197397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1410089992753505477859725 528783747282564554197397)
                  ·
                    refine ⟨24786738153870213478003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 528783747282564554197397 24786738153870213478003)
                    ·
                      rfl

theorem cell23_144816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_144816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144816 prefixEnd_144816 := by exact prefixLift 144816
  have htrace : WordTrace (prefixWord ++ tailWord_144816) baseStart_144816 baseEnd_144816 := by
    simpa [prefixWord, tailWord_144816, baseEnd_144816] using wordTrace_append hprefix tailTrace_144816
  have hstable : (prefixWord ++ tailWord_144816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144816).length < 2 ^ (prefixWord ++ tailWord_144816).sum := by decide
  have hdescent : baseEnd_144816 < baseStart_144816 := by decide
  rcases family_descends (prefixWord ++ tailWord_144816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144843 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 3]
def baseStart_144843 : Nat := 118140960795 + 144843 * 2 ^ 59
def prefixEnd_144843 : Nat := 4983230072969 + 3 ^ 40 * 144843 * 2
def baseEnd_144843 : Nat := 74374078439282034796385

theorem tailTrace_144843 : CollatzResearch.WordTrace tailWord_144843 prefixEnd_144843 74374078439282034796385 := by
  unfold tailWord_144843
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282858214266023060079183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3521905476177348706719455 5282858214266023060079183)
  ·
    refine ⟨7924287321399034590118775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5282858214266023060079183 7924287321399034590118775)
    ·
      refine ⟨11886430982098551885178163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7924287321399034590118775 11886430982098551885178163)
      ·
        refine ⟨17829646473147827827767245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11886430982098551885178163 17829646473147827827767245)
        ·
          refine ⟨6686117427430435435412717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17829646473147827827767245 6686117427430435435412717)
          ·
            refine ⟨2507294035286413288279769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6686117427430435435412717 2507294035286413288279769)
            ·
              refine ⟨1880470526464809966209827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2507294035286413288279769 1880470526464809966209827)
              ·
                refine ⟨2820705789697214949314741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880470526464809966209827 2820705789697214949314741)
                ·
                  refine ⟨264441167784113901498257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820705789697214949314741 264441167784113901498257)
                  ·
                    refine ⟨198330875838085426123693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264441167784113901498257 198330875838085426123693)
                    ·
                      refine ⟨74374078439282034796385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198330875838085426123693 74374078439282034796385)
                      ·
                        rfl

theorem cell23_144843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 3].length) (baseStart_144843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144843 prefixEnd_144843 := by exact prefixLift 144843
  have htrace : WordTrace (prefixWord ++ tailWord_144843) baseStart_144843 baseEnd_144843 := by
    simpa [prefixWord, tailWord_144843, baseEnd_144843] using wordTrace_append hprefix tailTrace_144843
  have hstable : (prefixWord ++ tailWord_144843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144843).length < 2 ^ (prefixWord ++ tailWord_144843).sum := by decide
  have hdescent : baseEnd_144843 < baseStart_144843 := by decide
  rcases family_descends (prefixWord ++ tailWord_144843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144853 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_144853 : Nat := 118140960795 + 144853 * 2 ^ 59
def prefixEnd_144853 : Nat := 4983230072969 + 3 ^ 40 * 144853 * 2
def baseEnd_144853 : Nat := 74379213245826995671339

theorem tailTrace_144853 : CollatzResearch.WordTrace tailWord_144853 prefixEnd_144853 74379213245826995671339 := by
  unfold tailWord_144853
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283222944229794767943213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3522148629486529845295475 5283222944229794767943213)
  ·
    refine ⟨1981208604086173037978705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5283222944229794767943213 1981208604086173037978705)
    ·
      refine ⟨1485906453064629778484029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1981208604086173037978705 1485906453064629778484029)
      ·
        refine ⟨557214919899236166931511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1485906453064629778484029 557214919899236166931511)
        ·
          refine ⟨835822379848854250397267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557214919899236166931511 835822379848854250397267)
          ·
            refine ⟨1253733569773281375595901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835822379848854250397267 1253733569773281375595901)
            ·
              refine ⟨470150088664980515848463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1253733569773281375595901 470150088664980515848463)
              ·
                refine ⟨705225132997470773772695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470150088664980515848463 705225132997470773772695)
                ·
                  refine ⟨1057837699496206160659043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705225132997470773772695 1057837699496206160659043)
                  ·
                    refine ⟨1586756549244309240988565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1057837699496206160659043 1586756549244309240988565)
                    ·
                      refine ⟨74379213245826995671339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1586756549244309240988565 74379213245826995671339)
                      ·
                        rfl

theorem cell23_144853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_144853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144853 prefixEnd_144853 := by exact prefixLift 144853
  have htrace : WordTrace (prefixWord ++ tailWord_144853) baseStart_144853 baseEnd_144853 := by
    simpa [prefixWord, tailWord_144853, baseEnd_144853] using wordTrace_append hprefix tailTrace_144853
  have hstable : (prefixWord ++ tailWord_144853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144853).length < 2 ^ (prefixWord ++ tailWord_144853).sum := by decide
  have hdescent : baseEnd_144853 < baseStart_144853 := by decide
  rcases family_descends (prefixWord ++ tailWord_144853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144857 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 3, 2, 2]
def baseStart_144857 : Nat := 118140960795 + 144857 * 2 ^ 59
def prefixEnd_144857 : Nat := 4983230072969 + 3 ^ 40 * 144857 * 2
def baseEnd_144857 : Nat := 74381267168444980021321

theorem tailTrace_144857 : CollatzResearch.WordTrace tailWord_144857 prefixEnd_144857 74381267168444980021321 := by
  unfold tailWord_144857
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283368836215303451088825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3522245890810202300725883 5283368836215303451088825)
  ·
    refine ⟨3962526627161477588316619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5283368836215303451088825 3962526627161477588316619)
    ·
      refine ⟨5943789940742216382474929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962526627161477588316619 5943789940742216382474929)
      ·
        refine ⟨4457842455556662286856197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5943789940742216382474929 4457842455556662286856197)
        ·
          refine ⟨835845460416874178785537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4457842455556662286856197 835845460416874178785537)
          ·
            refine ⟨626884095312655634089153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835845460416874178785537 626884095312655634089153)
            ·
              refine ⟨470163071484491725566865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626884095312655634089153 470163071484491725566865)
              ·
                refine ⟨352622303613368794175149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470163071484491725566865 352622303613368794175149)
                ·
                  refine ⟨132233363855013297815681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352622303613368794175149 132233363855013297815681)
                  ·
                    refine ⟨99175022891259973361761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 132233363855013297815681 99175022891259973361761)
                    ·
                      refine ⟨74381267168444980021321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99175022891259973361761 74381267168444980021321)
                      ·
                        rfl

theorem cell23_144857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_144857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144857 prefixEnd_144857 := by exact prefixLift 144857
  have htrace : WordTrace (prefixWord ++ tailWord_144857) baseStart_144857 baseEnd_144857 := by
    simpa [prefixWord, tailWord_144857, baseEnd_144857] using wordTrace_append hprefix tailTrace_144857
  have hstable : (prefixWord ++ tailWord_144857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144857).length < 2 ^ (prefixWord ++ tailWord_144857).sum := by decide
  have hdescent : baseEnd_144857 < baseStart_144857 := by decide
  rcases family_descends (prefixWord ++ tailWord_144857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144877 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_144877 : Nat := 118140960795 + 144877 * 2 ^ 59
def prefixEnd_144877 : Nat := 4983230072969 + 3 ^ 40 * 144877 * 2
def baseEnd_144877 : Nat := 74391536781534901771229

theorem tailTrace_144877 : CollatzResearch.WordTrace tailWord_144877 prefixEnd_144877 74391536781534901771229 := by
  unfold tailWord_144877
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284098296142846866816885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3522732197428564577877923 5284098296142846866816885)
  ·
    refine ⟨495384215263391893764083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5284098296142846866816885 495384215263391893764083)
    ·
      refine ⟨743076322895087840646125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495384215263391893764083 743076322895087840646125)
      ·
        refine ⟨278653621085657940242297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 743076322895087840646125 278653621085657940242297)
        ·
          refine ⟨208990215814243455181723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278653621085657940242297 208990215814243455181723)
          ·
            refine ⟨313485323721365182772585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208990215814243455181723 313485323721365182772585)
            ·
              refine ⟨235113992791023887079439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313485323721365182772585 235113992791023887079439)
              ·
                refine ⟨352670989186535830619159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235113992791023887079439 352670989186535830619159)
                ·
                  refine ⟨529006483779803745928739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352670989186535830619159 529006483779803745928739)
                  ·
                    refine ⟨793509725669705618893109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 529006483779803745928739 793509725669705618893109)
                    ·
                      refine ⟨74391536781534901771229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 793509725669705618893109 74391536781534901771229)
                      ·
                        rfl

theorem cell23_144877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_144877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144877 prefixEnd_144877 := by exact prefixLift 144877
  have htrace : WordTrace (prefixWord ++ tailWord_144877) baseStart_144877 baseEnd_144877 := by
    simpa [prefixWord, tailWord_144877, baseEnd_144877] using wordTrace_append hprefix tailTrace_144877
  have hstable : (prefixWord ++ tailWord_144877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144877).length < 2 ^ (prefixWord ++ tailWord_144877).sum := by decide
  have hdescent : baseEnd_144877 < baseStart_144877 := by decide
  rcases family_descends (prefixWord ++ tailWord_144877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144890 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_144890 : Nat := 118140960795 + 144890 * 2 ^ 59
def prefixEnd_144890 : Nat := 4983230072969 + 3 ^ 40 * 144890 * 2
def baseEnd_144890 : Nat := 74398212030043350908669

theorem tailTrace_144890 : CollatzResearch.WordTrace tailWord_144890 prefixEnd_144890 74398212030043350908669 := by
  unfold tailWord_144890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321143111273937521760031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3523048296730500058026749 1321143111273937521760031)
  ·
    refine ⟨1981714666910906282640047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1321143111273937521760031 1981714666910906282640047)
    ·
      refine ⟨2972572000366359423960071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981714666910906282640047 2972572000366359423960071)
      ·
        refine ⟨4458858000549539135940107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972572000366359423960071 4458858000549539135940107)
        ·
          refine ⟨6688287000824308703910161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458858000549539135940107 6688287000824308703910161)
          ·
            refine ⟨5016215250618231527932621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6688287000824308703910161 5016215250618231527932621)
            ·
              refine ⟨1881080718981836822974733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5016215250618231527932621 1881080718981836822974733)
              ·
                refine ⟨705405269618188808615525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1881080718981836822974733 705405269618188808615525)
                ·
                  refine ⟨132263488053410401615411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705405269618188808615525 132263488053410401615411)
                  ·
                    refine ⟨198395232080115602423117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 132263488053410401615411 198395232080115602423117)
                    ·
                      refine ⟨74398212030043350908669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198395232080115602423117 74398212030043350908669)
                      ·
                        rfl

theorem cell23_144890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_144890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144890 prefixEnd_144890 := by exact prefixLift 144890
  have htrace : WordTrace (prefixWord ++ tailWord_144890) baseStart_144890 baseEnd_144890 := by
    simpa [prefixWord, tailWord_144890, baseEnd_144890] using wordTrace_append hprefix tailTrace_144890
  have hstable : (prefixWord ++ tailWord_144890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144890).length < 2 ^ (prefixWord ++ tailWord_144890).sum := by decide
  have hdescent : baseEnd_144890 < baseStart_144890 := by decide
  rcases family_descends (prefixWord ++ tailWord_144890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144917 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_144917 : Nat := 118140960795 + 144917 * 2 ^ 59
def prefixEnd_144917 : Nat := 4983230072969 + 3 ^ 40 * 144917 * 2
def baseEnd_144917 : Nat := 74412076007714745271045

theorem tailTrace_144917 : CollatzResearch.WordTrace tailWord_144917 prefixEnd_144917 74412076007714745271045 := by
  unfold tailWord_144917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5285557215997933698273005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3523704810665289132182003 5285557215997933698273005)
  ·
    refine ⟨1982083955999225136852377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5285557215997933698273005 1982083955999225136852377)
    ·
      refine ⟨1486562966999418852639283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1982083955999225136852377 1486562966999418852639283)
      ·
        refine ⟨2229844450499128278958925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486562966999418852639283 2229844450499128278958925)
        ·
          refine ⟨836191668937173104609597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2229844450499128278958925 836191668937173104609597)
          ·
            refine ⟨313571875851439914228599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 836191668937173104609597 313571875851439914228599)
            ·
              refine ⟨470357813777159871342899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313571875851439914228599 470357813777159871342899)
              ·
                refine ⟨705536720665739807014349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470357813777159871342899 705536720665739807014349)
                ·
                  refine ⟨264576270249652427630381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705536720665739807014349 264576270249652427630381)
                  ·
                    refine ⟨99216101343619660361393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264576270249652427630381 99216101343619660361393)
                    ·
                      refine ⟨74412076007714745271045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99216101343619660361393 74412076007714745271045)
                      ·
                        rfl

theorem cell23_144917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_144917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144917 prefixEnd_144917 := by exact prefixLift 144917
  have htrace : WordTrace (prefixWord ++ tailWord_144917) baseStart_144917 baseEnd_144917 := by
    simpa [prefixWord, tailWord_144917, baseEnd_144917] using wordTrace_append hprefix tailTrace_144917
  have hstable : (prefixWord ++ tailWord_144917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144917).length < 2 ^ (prefixWord ++ tailWord_144917).sum := by decide
  have hdescent : baseEnd_144917 < baseStart_144917 := by decide
  rcases family_descends (prefixWord ++ tailWord_144917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144980 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_144980 : Nat := 118140960795 + 144980 * 2 ^ 59
def prefixEnd_144980 : Nat := 4983230072969 + 3 ^ 40 * 144980 * 2
def baseEnd_144980 : Nat := 74444425288947998783255

theorem tailTrace_144980 : CollatzResearch.WordTrace tailWord_144980 prefixEnd_144980 74444425288947998783255 := by
  unfold tailWord_144980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643927507384847728908197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3525236676513130305210929 2643927507384847728908197)
  ·
    refine ⟨495736407634658949170287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2643927507384847728908197 495736407634658949170287)
    ·
      refine ⟨743604611451988423755431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495736407634658949170287 743604611451988423755431)
      ·
        refine ⟨1115406917177982635633147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743604611451988423755431 1115406917177982635633147)
        ·
          refine ⟨1673110375766973953449721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115406917177982635633147 1673110375766973953449721)
          ·
            refine ⟨1254832781825230465087291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1673110375766973953449721 1254832781825230465087291)
            ·
              refine ⟨1882249172737845697630937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254832781825230465087291 1882249172737845697630937)
              ·
                refine ⟨1411686879553384273223203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1882249172737845697630937 1411686879553384273223203)
                ·
                  refine ⟨2117530319330076409834805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411686879553384273223203 2117530319330076409834805)
                  ·
                    refine ⟨198518467437194663422013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2117530319330076409834805 198518467437194663422013)
                    ·
                      refine ⟨74444425288947998783255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198518467437194663422013 74444425288947998783255)
                      ·
                        rfl

theorem cell23_144980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_144980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_144980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_144980 prefixEnd_144980 := by exact prefixLift 144980
  have htrace : WordTrace (prefixWord ++ tailWord_144980) baseStart_144980 baseEnd_144980 := by
    simpa [prefixWord, tailWord_144980, baseEnd_144980] using wordTrace_append hprefix tailTrace_144980
  have hstable : (prefixWord ++ tailWord_144980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144980).length < 2 ^ (prefixWord ++ tailWord_144980).sum := by decide
  have hdescent : baseEnd_144980 < baseStart_144980 := by decide
  rcases family_descends (prefixWord ++ tailWord_144980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145023 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_145023 : Nat := 118140960795 + 145023 * 2 ^ 59
def prefixEnd_145023 : Nat := 4983230072969 + 3 ^ 40 * 145023 * 2
def baseEnd_145023 : Nat := 74466504957091330545557

theorem tailTrace_145023 : CollatzResearch.WordTrace tailWord_145023 prefixEnd_145023 74466504957091330545557 := by
  unfold tailWord_145023
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289423353613913801631723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3526282235742609201087815 5289423353613913801631723)
  ·
    refine ⟨7934135030420870702447585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5289423353613913801631723 7934135030420870702447585)
    ·
      refine ⟨5950601272815653026835689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7934135030420870702447585 5950601272815653026835689)
      ·
        refine ⟨4462950954611739770126767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5950601272815653026835689 4462950954611739770126767)
        ·
          refine ⟨6694426431917609655190151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4462950954611739770126767 6694426431917609655190151)
          ·
            refine ⟨10041639647876414482785227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6694426431917609655190151 10041639647876414482785227)
            ·
              refine ⟨15062459471814621724177841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10041639647876414482785227 15062459471814621724177841)
              ·
                refine ⟨11296844603860966293133381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15062459471814621724177841 11296844603860966293133381)
                ·
                  refine ⟨2118158363223931179962509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11296844603860966293133381 2118158363223931179962509)
                  ·
                    refine ⟨794309386208974192485941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118158363223931179962509 794309386208974192485941)
                    ·
                      refine ⟨74466504957091330545557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 794309386208974192485941 74466504957091330545557)
                      ·
                        rfl

theorem cell23_145023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_145023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145023 prefixEnd_145023 := by exact prefixLift 145023
  have htrace : WordTrace (prefixWord ++ tailWord_145023) baseStart_145023 baseEnd_145023 := by
    simpa [prefixWord, tailWord_145023, baseEnd_145023] using wordTrace_append hprefix tailTrace_145023
  have hstable : (prefixWord ++ tailWord_145023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145023).length < 2 ^ (prefixWord ++ tailWord_145023).sum := by decide
  have hdescent : baseEnd_145023 < baseStart_145023 := by decide
  rcases family_descends (prefixWord ++ tailWord_145023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145040 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3]
def baseStart_145040 : Nat := 118140960795 + 145040 * 2 ^ 59
def prefixEnd_145040 : Nat := 4983230072969 + 3 ^ 40 * 145040 * 2
def baseEnd_145040 : Nat := 74475234128217764032979

theorem tailTrace_145040 : CollatzResearch.WordTrace tailWord_145040 prefixEnd_145040 74475234128217764032979 := by
  unfold tailWord_145040
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645021697276162852500287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3526695596368217136667049 2645021697276162852500287)
  ·
    refine ⟨3967532545914244278750431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2645021697276162852500287 3967532545914244278750431)
    ·
      refine ⟨5951298818871366418125647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3967532545914244278750431 5951298818871366418125647)
      ·
        refine ⟨8926948228307049627188471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951298818871366418125647 8926948228307049627188471)
        ·
          refine ⟨13390422342460574440782707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8926948228307049627188471 13390422342460574440782707)
          ·
            refine ⟨20085633513690861661174061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13390422342460574440782707 20085633513690861661174061)
            ·
              refine ⟨7532112567634073122940273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20085633513690861661174061 7532112567634073122940273)
              ·
                refine ⟨5649084425725554842205205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7532112567634073122940273 5649084425725554842205205)
                ·
                  refine ⟨264800832455885383228369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5649084425725554842205205 264800832455885383228369)
                  ·
                    refine ⟨198600624341914037421277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264800832455885383228369 198600624341914037421277)
                    ·
                      refine ⟨74475234128217764032979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198600624341914037421277 74475234128217764032979)
                      ·
                        rfl

theorem cell23_145040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_145040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145040 prefixEnd_145040 := by exact prefixLift 145040
  have htrace : WordTrace (prefixWord ++ tailWord_145040) baseStart_145040 baseEnd_145040 := by
    simpa [prefixWord, tailWord_145040, baseEnd_145040] using wordTrace_append hprefix tailTrace_145040
  have hstable : (prefixWord ++ tailWord_145040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145040).length < 2 ^ (prefixWord ++ tailWord_145040).sum := by decide
  have hdescent : baseEnd_145040 < baseStart_145040 := by decide
  rcases family_descends (prefixWord ++ tailWord_145040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145054 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_145054 : Nat := 118140960795 + 145054 * 2 ^ 59
def prefixEnd_145054 : Nat := 4983230072969 + 3 ^ 40 * 145054 * 2
def baseEnd_145054 : Nat := 74482422857380709257915

theorem tailTrace_145054 : CollatzResearch.WordTrace tailWord_145054 prefixEnd_145054 74482422857380709257915 := by
  unfold tailWord_145054
  simp only [CollatzResearch.WordTrace]
  refine ⟨661319252062700762001277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3527036011001070730673477 661319252062700762001277)
  ·
    refine ⟨247994719523512785750479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 661319252062700762001277 247994719523512785750479)
    ·
      refine ⟨371992079285269178625719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247994719523512785750479 371992079285269178625719)
      ·
        refine ⟨557988118927903767938579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371992079285269178625719 557988118927903767938579)
        ·
          refine ⟨836982178391855651907869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557988118927903767938579 836982178391855651907869)
          ·
            refine ⟨313868316896945869465451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 836982178391855651907869 313868316896945869465451)
            ·
              refine ⟨470802475345418804198177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313868316896945869465451 470802475345418804198177)
              ·
                refine ⟨353101856509064103148633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470802475345418804198177 353101856509064103148633)
                ·
                  refine ⟨264826392381798077361475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353101856509064103148633 264826392381798077361475)
                  ·
                    refine ⟨397239588572697116042213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 264826392381798077361475 397239588572697116042213)
                    ·
                      refine ⟨74482422857380709257915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 397239588572697116042213 74482422857380709257915)
                      ·
                        rfl

theorem cell23_145054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_145054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145054 prefixEnd_145054 := by exact prefixLift 145054
  have htrace : WordTrace (prefixWord ++ tailWord_145054) baseStart_145054 baseEnd_145054 := by
    simpa [prefixWord, tailWord_145054, baseEnd_145054] using wordTrace_append hprefix tailTrace_145054
  have hstable : (prefixWord ++ tailWord_145054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145054).length < 2 ^ (prefixWord ++ tailWord_145054).sum := by decide
  have hdescent : baseEnd_145054 < baseStart_145054 := by decide
  rcases family_descends (prefixWord ++ tailWord_145054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145057 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_145057 : Nat := 118140960795 + 145057 * 2 ^ 59
def prefixEnd_145057 : Nat := 4983230072969 + 3 ^ 40 * 145057 * 2
def baseEnd_145057 : Nat := 74483963299344197520401

theorem tailTrace_145057 : CollatzResearch.WordTrace tailWord_145057 prefixEnd_145057 74483963299344197520401 := by
  unfold tailWord_145057
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290663435490737608369425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3527108956993825072246283 5290663435490737608369425)
  ·
    refine ⟨3967997576618053206277069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5290663435490737608369425 3967997576618053206277069)
    ·
      refine ⟨1487999091231769952353901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3967997576618053206277069 1487999091231769952353901)
      ·
        refine ⟨557999659211913732132713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1487999091231769952353901 557999659211913732132713)
        ·
          refine ⟨418499744408935299099535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557999659211913732132713 418499744408935299099535)
          ·
            refine ⟨627749616613402948649303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418499744408935299099535 627749616613402948649303)
            ·
              refine ⟨941624424920104422973955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627749616613402948649303 941624424920104422973955)
              ·
                refine ⟨1412436637380156634460933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941624424920104422973955 1412436637380156634460933)
                ·
                  refine ⟨264831869508779368961425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412436637380156634460933 264831869508779368961425)
                  ·
                    refine ⟨198623902131584526721069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264831869508779368961425 198623902131584526721069)
                    ·
                      refine ⟨74483963299344197520401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198623902131584526721069 74483963299344197520401)
                      ·
                        rfl

theorem cell23_145057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_145057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145057 prefixEnd_145057 := by exact prefixLift 145057
  have htrace : WordTrace (prefixWord ++ tailWord_145057) baseStart_145057 baseEnd_145057 := by
    simpa [prefixWord, tailWord_145057, baseEnd_145057] using wordTrace_append hprefix tailTrace_145057
  have hstable : (prefixWord ++ tailWord_145057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145057).length < 2 ^ (prefixWord ++ tailWord_145057).sum := by decide
  have hdescent : baseEnd_145057 < baseStart_145057 := by decide
  rcases family_descends (prefixWord ++ tailWord_145057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145060 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 8]
def baseStart_145060 : Nat := 118140960795 + 145060 * 2 ^ 59
def prefixEnd_145060 : Nat := 4983230072969 + 3 ^ 40 * 145060 * 2
def baseEnd_145060 : Nat := 8276167082367520642543

theorem tailTrace_145060 : CollatzResearch.WordTrace tailWord_145060 prefixEnd_145060 8276167082367520642543 := by
  unfold tailWord_145060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645386427239934560364317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3527181902986579413819089 2645386427239934560364317)
  ·
    refine ⟨992019910214975460136619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2645386427239934560364317 992019910214975460136619)
    ·
      refine ⟨1488029865322463190204929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992019910214975460136619 1488029865322463190204929)
      ·
        refine ⟨1116022398991847392653697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1488029865322463190204929 1116022398991847392653697)
        ·
          refine ⟨837016799243885544490273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1116022398991847392653697 837016799243885544490273)
          ·
            refine ⟨627762599432914158367705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837016799243885544490273 627762599432914158367705)
            ·
              refine ⟨470821949574685618775779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627762599432914158367705 470821949574685618775779)
              ·
                refine ⟨706232924362028428163669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470821949574685618775779 706232924362028428163669)
                ·
                  refine ⟨8276167082367520642543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 706232924362028428163669 8276167082367520642543)
                  ·
                    rfl

theorem cell23_145060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_145060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145060 prefixEnd_145060 := by exact prefixLift 145060
  have htrace : WordTrace (prefixWord ++ tailWord_145060) baseStart_145060 baseEnd_145060 := by
    simpa [prefixWord, tailWord_145060, baseEnd_145060] using wordTrace_append hprefix tailTrace_145060
  have hstable : (prefixWord ++ tailWord_145060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145060).length < 2 ^ (prefixWord ++ tailWord_145060).sum := by decide
  have hdescent : baseEnd_145060 < baseStart_145060 := by decide
  rcases family_descends (prefixWord ++ tailWord_145060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145087 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 3]
def baseStart_145087 : Nat := 118140960795 + 145087 * 2 ^ 59
def prefixEnd_145087 : Nat := 4983230072969 + 3 ^ 40 * 145087 * 2
def baseEnd_145087 : Nat := 74499367718979080145263

theorem tailTrace_145087 : CollatzResearch.WordTrace tailWord_145087 prefixEnd_145087 74499367718979080145263 := by
  unfold tailWord_145087
  simp only [CollatzResearch.WordTrace]
  refine ⟨5291757625382052731961515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3527838416921368487974343 5291757625382052731961515)
  ·
    refine ⟨7937636438073079097942273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5291757625382052731961515 7937636438073079097942273)
    ·
      refine ⟨5953227328554809323456705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7937636438073079097942273 5953227328554809323456705)
      ·
        refine ⟨4464920496416106992592529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5953227328554809323456705 4464920496416106992592529)
        ·
          refine ⟨3348690372312080244444397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4464920496416106992592529 3348690372312080244444397)
          ·
            refine ⟨1255758889617030091666649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3348690372312080244444397 1255758889617030091666649)
            ·
              refine ⟨941819167212772568749987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255758889617030091666649 941819167212772568749987)
              ·
                refine ⟨1412728750819158853124981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941819167212772568749987 1412728750819158853124981)
                ·
                  refine ⟨132443320389296142480467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1412728750819158853124981 132443320389296142480467)
                  ·
                    refine ⟨198664980583944213720701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 132443320389296142480467 198664980583944213720701)
                    ·
                      refine ⟨74499367718979080145263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198664980583944213720701 74499367718979080145263)
                      ·
                        rfl

theorem cell23_145087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_145087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145087 prefixEnd_145087 := by exact prefixLift 145087
  have htrace : WordTrace (prefixWord ++ tailWord_145087) baseStart_145087 baseEnd_145087 := by
    simpa [prefixWord, tailWord_145087, baseEnd_145087] using wordTrace_append hprefix tailTrace_145087
  have hstable : (prefixWord ++ tailWord_145087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145087).length < 2 ^ (prefixWord ++ tailWord_145087).sum := by decide
  have hdescent : baseEnd_145087 < baseStart_145087 := by decide
  rcases family_descends (prefixWord ++ tailWord_145087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145114 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2]
def baseStart_145114 : Nat := 118140960795 + 145114 * 2 ^ 59
def prefixEnd_145114 : Nat := 4983230072969 + 3 ^ 40 * 145114 * 2
def baseEnd_145114 : Nat := 74513231696650474507639

theorem tailTrace_145114 : CollatzResearch.WordTrace tailWord_145114 prefixEnd_145114 74513231696650474507639 := by
  unfold tailWord_145114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323185599071059085798599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3528494930856157562129597 1323185599071059085798599)
  ·
    refine ⟨1984778398606588628697899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323185599071059085798599 1984778398606588628697899)
    ·
      refine ⟨2977167597909882943046849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984778398606588628697899 2977167597909882943046849)
      ·
        refine ⟨2232875698432412207285137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2977167597909882943046849 2232875698432412207285137)
        ·
          refine ⟨1674656773824309155463853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2232875698432412207285137 1674656773824309155463853)
          ·
            refine ⟨627996290184115933298945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1674656773824309155463853 627996290184115933298945)
            ·
              refine ⟨470997217638086949974209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627996290184115933298945 470997217638086949974209)
              ·
                refine ⟨353247913228565212480657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470997217638086949974209 353247913228565212480657)
                ·
                  refine ⟨264935934921423909360493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353247913228565212480657 264935934921423909360493)
                  ·
                    refine ⟨99350975595533966010185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264935934921423909360493 99350975595533966010185)
                    ·
                      refine ⟨74513231696650474507639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99350975595533966010185 74513231696650474507639)
                      ·
                        rfl

theorem cell23_145114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_145114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145114 prefixEnd_145114 := by exact prefixLift 145114
  have htrace : WordTrace (prefixWord ++ tailWord_145114) baseStart_145114 baseEnd_145114 := by
    simpa [prefixWord, tailWord_145114, baseEnd_145114] using wordTrace_append hprefix tailTrace_145114
  have hstable : (prefixWord ++ tailWord_145114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145114).length < 2 ^ (prefixWord ++ tailWord_145114).sum := by decide
  have hdescent : baseEnd_145114 < baseStart_145114 := by decide
  rcases family_descends (prefixWord ++ tailWord_145114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145137 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 1, 6]
def baseStart_145137 : Nat := 118140960795 + 145137 * 2 ^ 59
def prefixEnd_145137 : Nat := 4983230072969 + 3 ^ 40 * 145137 * 2
def baseEnd_145137 : Nat := 24841680583901294840011

theorem tailTrace_145137 : CollatzResearch.WordTrace tailWord_145137 prefixEnd_145137 24841680583901294840011 := by
  unfold tailWord_145137
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293581275200911271281665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3529054183467274180854443 5293581275200911271281665)
  ·
    refine ⟨3970185956400683453461249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5293581275200911271281665 3970185956400683453461249)
    ·
      refine ⟨2977639467300512590095937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3970185956400683453461249 2977639467300512590095937)
      ·
        refine ⟨2233229600475384442571953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2977639467300512590095937 2233229600475384442571953)
        ·
          refine ⟨1674922200356538331928965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2233229600475384442571953 1674922200356538331928965)
          ·
            refine ⟨314047912566850937236681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1674922200356538331928965 314047912566850937236681)
            ·
              refine ⟨235535934425138202927511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314047912566850937236681 235535934425138202927511)
              ·
                refine ⟨353303901637707304391267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235535934425138202927511 353303901637707304391267)
                ·
                  refine ⟨529955852456560956586901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353303901637707304391267 529955852456560956586901)
                  ·
                    refine ⟨24841680583901294840011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 529955852456560956586901 24841680583901294840011)
                    ·
                      rfl

theorem cell23_145137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_145137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145137 prefixEnd_145137 := by exact prefixLift 145137
  have htrace : WordTrace (prefixWord ++ tailWord_145137) baseStart_145137 baseEnd_145137 := by
    simpa [prefixWord, tailWord_145137, baseEnd_145137] using wordTrace_append hprefix tailTrace_145137
  have hstable : (prefixWord ++ tailWord_145137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145137).length < 2 ^ (prefixWord ++ tailWord_145137).sum := by decide
  have hdescent : baseEnd_145137 < baseStart_145137 := by decide
  rcases family_descends (prefixWord ++ tailWord_145137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145154 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_145154 : Nat := 118140960795 + 145154 * 2 ^ 59
def prefixEnd_145154 : Nat := 4983230072969 + 3 ^ 40 * 145154 * 2
def baseEnd_145154 : Nat := 24844590307610106002485

theorem tailTrace_145154 : CollatzResearch.WordTrace tailWord_145154 prefixEnd_145154 24844590307610106002485 := by
  unfold tailWord_145154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323550329034830793662629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3529467544092882116433677 1323550329034830793662629)
  ·
    refine ⟨248165686694030773811743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1323550329034830793662629 248165686694030773811743)
    ·
      refine ⟨372248530041046160717615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248165686694030773811743 372248530041046160717615)
      ·
        refine ⟨558372795061569241076423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372248530041046160717615 558372795061569241076423)
        ·
          refine ⟨837559192592353861614635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558372795061569241076423 837559192592353861614635)
          ·
            refine ⟨1256338788888530792421953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837559192592353861614635 1256338788888530792421953)
            ·
              refine ⟨942254091666398094316465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256338788888530792421953 942254091666398094316465)
              ·
                refine ⟨706690568749798570737349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942254091666398094316465 706690568749798570737349)
                ·
                  refine ⟨132504481640587232013253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706690568749798570737349 132504481640587232013253)
                  ·
                    refine ⟨24844590307610106002485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132504481640587232013253 24844590307610106002485)
                    ·
                      rfl

theorem cell23_145154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_145154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145154 prefixEnd_145154 := by exact prefixLift 145154
  have htrace : WordTrace (prefixWord ++ tailWord_145154) baseStart_145154 baseEnd_145154 := by
    simpa [prefixWord, tailWord_145154, baseEnd_145154] using wordTrace_append hprefix tailTrace_145154
  have hstable : (prefixWord ++ tailWord_145154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145154).length < 2 ^ (prefixWord ++ tailWord_145154).sum := by decide
  have hdescent : baseEnd_145154 < baseStart_145154 := by decide
  rcases family_descends (prefixWord ++ tailWord_145154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145178 : List Nat := [3, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2]
def baseStart_145178 : Nat := 118140960795 + 145178 * 2 ^ 59
def prefixEnd_145178 : Nat := 4983230072969 + 3 ^ 40 * 145178 * 2
def baseEnd_145178 : Nat := 74546094458538224107345

theorem tailTrace_145178 : CollatzResearch.WordTrace tailWord_145178 prefixEnd_145178 74546094458538224107345 := by
  unfold tailWord_145178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323769167013093818381047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3530051112034916849016125 1323769167013093818381047)
  ·
    refine ⟨1985653750519640727571571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323769167013093818381047 1985653750519640727571571)
    ·
      refine ⟨2978480625779461091357357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1985653750519640727571571 2978480625779461091357357)
      ·
        refine ⟨1116930234667297909259009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2978480625779461091357357 1116930234667297909259009)
        ·
          refine ⟨837697676000473431944257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1116930234667297909259009 837697676000473431944257)
          ·
            refine ⟨628273257000355073958193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837697676000473431944257 628273257000355073958193)
            ·
              refine ⟨471204942750266305468645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628273257000355073958193 471204942750266305468645)
              ·
                refine ⟨88350926765674932275371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 471204942750266305468645 88350926765674932275371)
                ·
                  refine ⟨132526390148512398413057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88350926765674932275371 132526390148512398413057)
                  ·
                    refine ⟨99394792611384298809793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 132526390148512398413057 99394792611384298809793)
                    ·
                      refine ⟨74546094458538224107345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99394792611384298809793 74546094458538224107345)
                      ·
                        rfl

theorem cell23_145178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_145178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145178 prefixEnd_145178 := by exact prefixLift 145178
  have htrace : WordTrace (prefixWord ++ tailWord_145178) baseStart_145178 baseEnd_145178 := by
    simpa [prefixWord, tailWord_145178, baseEnd_145178] using wordTrace_append hprefix tailTrace_145178
  have hstable : (prefixWord ++ tailWord_145178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145178).length < 2 ^ (prefixWord ++ tailWord_145178).sum := by decide
  have hdescent : baseEnd_145178 < baseStart_145178 := by decide
  rcases family_descends (prefixWord ++ tailWord_145178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145198 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_145198 : Nat := 118140960795 + 145198 * 2 ^ 59
def prefixEnd_145198 : Nat := 4983230072969 + 3 ^ 40 * 145198 * 2
def baseEnd_145198 : Nat := 74556364071628145857253

theorem tailTrace_145198 : CollatzResearch.WordTrace tailWord_145198 prefixEnd_145198 74556364071628145857253 := by
  unfold tailWord_145198
  simp only [CollatzResearch.WordTrace]
  refine ⟨661975765997489836156531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3530537418653279126168165 661975765997489836156531)
  ·
    refine ⟨992963648996234754234797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 661975765997489836156531 992963648996234754234797)
    ·
      refine ⟨372361368373588032838049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 992963648996234754234797 372361368373588032838049)
      ·
        refine ⟨279271026280191024628537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372361368373588032838049 279271026280191024628537)
        ·
          refine ⟨209453269710143268471403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279271026280191024628537 209453269710143268471403)
          ·
            refine ⟨314179904565214902707105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209453269710143268471403 314179904565214902707105)
            ·
              refine ⟨235634928423911177030329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314179904565214902707105 235634928423911177030329)
              ·
                refine ⟨176726196317933382772747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235634928423911177030329 176726196317933382772747)
                ·
                  refine ⟨265089294476900074159121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176726196317933382772747 265089294476900074159121)
                  ·
                    refine ⟨198816970857675055619341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265089294476900074159121 198816970857675055619341)
                    ·
                      refine ⟨74556364071628145857253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198816970857675055619341 74556364071628145857253)
                      ·
                        rfl

theorem cell23_145198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_145198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145198 prefixEnd_145198 := by exact prefixLift 145198
  have htrace : WordTrace (prefixWord ++ tailWord_145198) baseStart_145198 baseEnd_145198 := by
    simpa [prefixWord, tailWord_145198, baseEnd_145198] using wordTrace_append hprefix tailTrace_145198
  have hstable : (prefixWord ++ tailWord_145198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145198).length < 2 ^ (prefixWord ++ tailWord_145198).sum := by decide
  have hdescent : baseEnd_145198 < baseStart_145198 := by decide
  rcases family_descends (prefixWord ++ tailWord_145198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145267 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 3]
def baseStart_145267 : Nat := 118140960795 + 145267 * 2 ^ 59
def prefixEnd_145267 : Nat := 4983230072969 + 3 ^ 40 * 145267 * 2
def baseEnd_145267 : Nat := 74591794236788375894435

theorem tailTrace_145267 : CollatzResearch.WordTrace tailWord_145267 prefixEnd_145267 74591794236788375894435 := by
  unfold tailWord_145267
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298322764729943473514055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3532215176486628982342703 5298322764729943473514055)
  ·
    refine ⟨7947484147094915210271083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5298322764729943473514055 7947484147094915210271083)
    ·
      refine ⟨11921226220642372815406625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7947484147094915210271083 11921226220642372815406625)
      ·
        refine ⟨8940919665481779611554969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11921226220642372815406625 8940919665481779611554969)
        ·
          refine ⟨6705689749111334708666227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8940919665481779611554969 6705689749111334708666227)
          ·
            refine ⟨10058534623667002062999341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705689749111334708666227 10058534623667002062999341)
            ·
              refine ⟨3771950483875125773624753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10058534623667002062999341 3771950483875125773624753)
              ·
                refine ⟨2828962862906344330218565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3771950483875125773624753 2828962862906344330218565)
                ·
                  refine ⟨530430536794939561915981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2828962862906344330218565 530430536794939561915981)
                  ·
                    refine ⟨198911451298102335718493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530430536794939561915981 198911451298102335718493)
                    ·
                      refine ⟨74591794236788375894435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 198911451298102335718493 74591794236788375894435)
                      ·
                        rfl

theorem cell23_145267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_145267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145267 prefixEnd_145267 := by exact prefixLift 145267
  have htrace : WordTrace (prefixWord ++ tailWord_145267) baseStart_145267 baseEnd_145267 := by
    simpa [prefixWord, tailWord_145267, baseEnd_145267] using wordTrace_append hprefix tailTrace_145267
  have hstable : (prefixWord ++ tailWord_145267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145267).length < 2 ^ (prefixWord ++ tailWord_145267).sum := by decide
  have hdescent : baseEnd_145267 < baseStart_145267 := by decide
  rcases family_descends (prefixWord ++ tailWord_145267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145297 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_145297 : Nat := 118140960795 + 145297 * 2 ^ 59
def prefixEnd_145297 : Nat := 4983230072969 + 3 ^ 40 * 145297 * 2
def baseEnd_145297 : Nat := 74607198656423258519297

theorem tailTrace_145297 : CollatzResearch.WordTrace tailWord_145297 prefixEnd_145297 74607198656423258519297 := by
  unfold tailWord_145297
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299416954621258597106145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3532944636414172398070763 5299416954621258597106145)
  ·
    refine ⟨3974562715965943947829609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5299416954621258597106145 3974562715965943947829609)
    ·
      refine ⟨2980922036974457960872207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3974562715965943947829609 2980922036974457960872207)
      ·
        refine ⟨4471383055461686941308311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2980922036974457960872207 4471383055461686941308311)
        ·
          refine ⟨6707074583192530411962467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471383055461686941308311 6707074583192530411962467)
          ·
            refine ⟨10060611874788795617943701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6707074583192530411962467 10060611874788795617943701)
            ·
              refine ⟨471591181630724794591111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10060611874788795617943701 471591181630724794591111)
              ·
                refine ⟨707386772446087191886667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471591181630724794591111 707386772446087191886667)
                ·
                  refine ⟨1061080158669130787830001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707386772446087191886667 1061080158669130787830001)
                  ·
                    refine ⟨795810119001848090872501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1061080158669130787830001 795810119001848090872501)
                    ·
                      refine ⟨74607198656423258519297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 795810119001848090872501 74607198656423258519297)
                      ·
                        rfl

theorem cell23_145297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_145297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145297 prefixEnd_145297 := by exact prefixLift 145297
  have htrace : WordTrace (prefixWord ++ tailWord_145297) baseStart_145297 baseEnd_145297 := by
    simpa [prefixWord, tailWord_145297, baseEnd_145297] using wordTrace_append hprefix tailTrace_145297
  have hstable : (prefixWord ++ tailWord_145297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145297).length < 2 ^ (prefixWord ++ tailWord_145297).sum := by decide
  have hdescent : baseEnd_145297 < baseStart_145297 := by decide
  rcases family_descends (prefixWord ++ tailWord_145297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145302 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_145302 : Nat := 118140960795 + 145302 * 2 ^ 59
def prefixEnd_145302 : Nat := 4983230072969 + 3 ^ 40 * 145302 * 2
def baseEnd_145302 : Nat := 74609766059695738956775

theorem tailTrace_145302 : CollatzResearch.WordTrace tailWord_145302 prefixEnd_145302 74609766059695738956775 := by
  unfold tailWord_145302
  simp only [CollatzResearch.WordTrace]
  refine ⟨331224957475196528189885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3533066213068762967358773 331224957475196528189885)
  ·
    refine ⟨124209359053198698071207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 331224957475196528189885 124209359053198698071207)
    ·
      refine ⟨186314038579798047106811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124209359053198698071207 186314038579798047106811)
      ·
        refine ⟨279471057869697070660217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186314038579798047106811 279471057869697070660217)
        ·
          refine ⟨209603293402272802995163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279471057869697070660217 209603293402272802995163)
          ·
            refine ⟨314404940103409204492745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209603293402272802995163 314404940103409204492745)
            ·
              refine ⟨235803705077556903369559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314404940103409204492745 235803705077556903369559)
              ·
                refine ⟨353705557616335355054339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235803705077556903369559 353705557616335355054339)
                ·
                  refine ⟨530558336424503032581509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353705557616335355054339 530558336424503032581509)
                  ·
                    refine ⟨99479688079594318609033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 530558336424503032581509 99479688079594318609033)
                    ·
                      refine ⟨74609766059695738956775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99479688079594318609033 74609766059695738956775)
                      ·
                        rfl

theorem cell23_145302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_145302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145302 prefixEnd_145302 := by exact prefixLift 145302
  have htrace : WordTrace (prefixWord ++ tailWord_145302) baseStart_145302 baseEnd_145302 := by
    simpa [prefixWord, tailWord_145302, baseEnd_145302] using wordTrace_append hprefix tailTrace_145302
  have hstable : (prefixWord ++ tailWord_145302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145302).length < 2 ^ (prefixWord ++ tailWord_145302).sum := by decide
  have hdescent : baseEnd_145302 < baseStart_145302 := by decide
  rcases family_descends (prefixWord ++ tailWord_145302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145324 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 6, 4, 2]
def baseStart_145324 : Nat := 118140960795 + 145324 * 2 ^ 59
def prefixEnd_145324 : Nat := 4983230072969 + 3 ^ 40 * 145324 * 2
def baseEnd_145324 : Nat := 74621062634094652881673

theorem tailTrace_145324 : CollatzResearch.WordTrace tailWord_145324 prefixEnd_145324 74621062634094652881673 := by
  unfold tailWord_145324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650200862761721104169513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3533601150348961472226017 2650200862761721104169513)
  ·
    refine ⟨1987650647071290828127135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2650200862761721104169513 1987650647071290828127135)
    ·
      refine ⟨2981475970606936242190703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1987650647071290828127135 2981475970606936242190703)
      ·
        refine ⟨4472213955910404363286055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981475970606936242190703 4472213955910404363286055)
        ·
          refine ⟨6708320933865606544929083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472213955910404363286055 6708320933865606544929083)
          ·
            refine ⟨10062481400798409817393625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6708320933865606544929083 10062481400798409817393625)
            ·
              refine ⟨7546861050598807363045219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10062481400798409817393625 7546861050598807363045219)
              ·
                refine ⟨11320291575898211044567829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7546861050598807363045219 11320291575898211044567829)
                ·
                  refine ⟨530638667620228642714117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11320291575898211044567829 530638667620228642714117)
                  ·
                    refine ⟨99494750178792870508897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 530638667620228642714117 99494750178792870508897)
                    ·
                      refine ⟨74621062634094652881673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99494750178792870508897 74621062634094652881673)
                      ·
                        rfl

theorem cell23_145324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_145324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145324 prefixEnd_145324 := by exact prefixLift 145324
  have htrace : WordTrace (prefixWord ++ tailWord_145324) baseStart_145324 baseEnd_145324 := by
    simpa [prefixWord, tailWord_145324, baseEnd_145324] using wordTrace_append hprefix tailTrace_145324
  have hstable : (prefixWord ++ tailWord_145324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145324).length < 2 ^ (prefixWord ++ tailWord_145324).sum := by decide
  have hdescent : baseEnd_145324 < baseStart_145324 := by decide
  rcases family_descends (prefixWord ++ tailWord_145324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145337 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_145337 : Nat := 118140960795 + 145337 * 2 ^ 59
def prefixEnd_145337 : Nat := 4983230072969 + 3 ^ 40 * 145337 * 2
def baseEnd_145337 : Nat := 74627737882603102019113

theorem tailTrace_145337 : CollatzResearch.WordTrace tailWord_145337 prefixEnd_145337 74627737882603102019113 := by
  unfold tailWord_145337
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300875874476345428562265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3533917249650896952374843 5300875874476345428562265)
  ·
    refine ⟨3975656905857259071421699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5300875874476345428562265 3975656905857259071421699)
    ·
      refine ⟨5963485358785888607132549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975656905857259071421699 5963485358785888607132549)
      ·
        refine ⟨1118153504772354113837353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5963485358785888607132549 1118153504772354113837353)
        ·
          refine ⟨838615128579265585378015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1118153504772354113837353 838615128579265585378015)
          ·
            refine ⟨1257922692868898378067023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838615128579265585378015 1257922692868898378067023)
            ·
              refine ⟨1886884039303347567100535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257922692868898378067023 1886884039303347567100535)
              ·
                refine ⟨2830326058955021350650803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886884039303347567100535 2830326058955021350650803)
                ·
                  refine ⟨4245489088432532025976205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830326058955021350650803 4245489088432532025976205)
                  ·
                    refine ⟨1592058408162199509741077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4245489088432532025976205 1592058408162199509741077)
                    ·
                      refine ⟨74627737882603102019113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1592058408162199509741077 74627737882603102019113)
                      ·
                        rfl

theorem cell23_145337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_145337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145337 prefixEnd_145337 := by exact prefixLift 145337
  have htrace : WordTrace (prefixWord ++ tailWord_145337) baseStart_145337 baseEnd_145337 := by
    simpa [prefixWord, tailWord_145337, baseEnd_145337] using wordTrace_append hprefix tailTrace_145337
  have hstable : (prefixWord ++ tailWord_145337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145337).length < 2 ^ (prefixWord ++ tailWord_145337).sum := by decide
  have hdescent : baseEnd_145337 < baseStart_145337 := by decide
  rcases family_descends (prefixWord ++ tailWord_145337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145341 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_145341 : Nat := 118140960795 + 145341 * 2 ^ 59
def prefixEnd_145341 : Nat := 4983230072969 + 3 ^ 40 * 145341 * 2
def baseEnd_145341 : Nat := 74629791805221086369095

theorem tailTrace_145341 : CollatzResearch.WordTrace tailWord_145341 prefixEnd_145341 74629791805221086369095 := by
  unfold tailWord_145341
  simp only [CollatzResearch.WordTrace]
  refine ⟨5301021766461854111707877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3534014510974569407805251 5301021766461854111707877)
  ·
    refine ⟨993941581211597645945227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5301021766461854111707877 993941581211597645945227)
    ·
      refine ⟨1490912371817396468917841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993941581211597645945227 1490912371817396468917841)
      ·
        refine ⟨1118184278863047351688381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1490912371817396468917841 1118184278863047351688381)
        ·
          refine ⟨419319104573642756883143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1118184278863047351688381 419319104573642756883143)
          ·
            refine ⟨628978656860464135324715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419319104573642756883143 628978656860464135324715)
            ·
              refine ⟨943467985290696202987073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628978656860464135324715 943467985290696202987073)
              ·
                refine ⟨707600988968022152240305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943467985290696202987073 707600988968022152240305)
                ·
                  refine ⟨530700741726016614180229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707600988968022152240305 530700741726016614180229)
                  ·
                    refine ⟨99506389073628115158793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 530700741726016614180229 99506389073628115158793)
                    ·
                      refine ⟨74629791805221086369095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99506389073628115158793 74629791805221086369095)
                      ·
                        rfl

theorem cell23_145341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_145341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145341 prefixEnd_145341 := by exact prefixLift 145341
  have htrace : WordTrace (prefixWord ++ tailWord_145341) baseStart_145341 baseEnd_145341 := by
    simpa [prefixWord, tailWord_145341, baseEnd_145341] using wordTrace_append hprefix tailTrace_145341
  have hstable : (prefixWord ++ tailWord_145341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145341).length < 2 ^ (prefixWord ++ tailWord_145341).sum := by decide
  have hdescent : baseEnd_145341 < baseStart_145341 := by decide
  rcases family_descends (prefixWord ++ tailWord_145341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145344 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3]
def baseStart_145344 : Nat := 118140960795 + 145344 * 2 ^ 59
def prefixEnd_145344 : Nat := 4983230072969 + 3 ^ 40 * 145344 * 2
def baseEnd_145344 : Nat := 74631332247184574631581

theorem tailTrace_145344 : CollatzResearch.WordTrace tailWord_145344 prefixEnd_145344 74631332247184574631581 := by
  unfold tailWord_145344
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650565592725492812033543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3534087456967323749378057 2650565592725492812033543)
  ·
    refine ⟨3975848389088239218050315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2650565592725492812033543 3975848389088239218050315)
    ·
      refine ⟨5963772583632358827075473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975848389088239218050315 5963772583632358827075473)
      ·
        refine ⟨4472829437724269120306605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5963772583632358827075473 4472829437724269120306605)
        ·
          refine ⟨1677311039146600920114977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4472829437724269120306605 1677311039146600920114977)
          ·
            refine ⟨1257983279359950690086233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1677311039146600920114977 1257983279359950690086233)
            ·
              refine ⟨943487459519963017564675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257983279359950690086233 943487459519963017564675)
              ·
                refine ⟨1415231189279944526347013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943487459519963017564675 1415231189279944526347013)
                ·
                  refine ⟨265355847989989598690065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1415231189279944526347013 265355847989989598690065)
                  ·
                    refine ⟨199016885992492199017549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265355847989989598690065 199016885992492199017549)
                    ·
                      refine ⟨74631332247184574631581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 199016885992492199017549 74631332247184574631581)
                      ·
                        rfl

theorem cell23_145344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_145344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145344 prefixEnd_145344 := by exact prefixLift 145344
  have htrace : WordTrace (prefixWord ++ tailWord_145344) baseStart_145344 baseEnd_145344 := by
    simpa [prefixWord, tailWord_145344, baseEnd_145344] using wordTrace_append hprefix tailTrace_145344
  have hstable : (prefixWord ++ tailWord_145344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145344).length < 2 ^ (prefixWord ++ tailWord_145344).sum := by decide
  have hdescent : baseEnd_145344 < baseStart_145344 := by decide
  rcases family_descends (prefixWord ++ tailWord_145344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145367 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_145367 : Nat := 118140960795 + 145367 * 2 ^ 59
def prefixEnd_145367 : Nat := 4983230072969 + 3 ^ 40 * 145367 * 2
def baseEnd_145367 : Nat := 74643142302237984643975

theorem tailTrace_145367 : CollatzResearch.WordTrace tailWord_145367 prefixEnd_145367 74643142302237984643975 := by
  unfold tailWord_145367
  simp only [CollatzResearch.WordTrace]
  refine ⟨5301970064367660552154355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3534646709578440368102903 5301970064367660552154355)
  ·
    refine ⟨7952955096551490828231533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5301970064367660552154355 7952955096551490828231533)
    ·
      refine ⟨2982358161206809060586825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7952955096551490828231533 2982358161206809060586825)
      ·
        refine ⟨2236768620905106795440119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2982358161206809060586825 2236768620905106795440119)
        ·
          refine ⟨3355152931357660193160179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236768620905106795440119 3355152931357660193160179)
          ·
            refine ⟨5032729397036490289740269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355152931357660193160179 5032729397036490289740269)
            ·
              refine ⟨1887273523888683858652601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5032729397036490289740269 1887273523888683858652601)
              ·
                refine ⟨1415455142916512893989451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887273523888683858652601 1415455142916512893989451)
                ·
                  refine ⟨2123182714374769340984177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415455142916512893989451 2123182714374769340984177)
                  ·
                    refine ⟨1592387035781077005738133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123182714374769340984177 1592387035781077005738133)
                    ·
                      refine ⟨74643142302237984643975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1592387035781077005738133 74643142302237984643975)
                      ·
                        rfl

theorem cell23_145367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_145367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145367 prefixEnd_145367 := by exact prefixLift 145367
  have htrace : WordTrace (prefixWord ++ tailWord_145367) baseStart_145367 baseEnd_145367 := by
    simpa [prefixWord, tailWord_145367, baseEnd_145367] using wordTrace_append hprefix tailTrace_145367
  have hstable : (prefixWord ++ tailWord_145367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145367).length < 2 ^ (prefixWord ++ tailWord_145367).sum := by decide
  have hdescent : baseEnd_145367 < baseStart_145367 := by decide
  rcases family_descends (prefixWord ++ tailWord_145367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145401 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 4, 3, 2]
def baseStart_145401 : Nat := 118140960795 + 145401 * 2 ^ 59
def prefixEnd_145401 : Nat := 4983230072969 + 3 ^ 40 * 145401 * 2
def baseEnd_145401 : Nat := 74660600644490851618819

theorem tailTrace_145401 : CollatzResearch.WordTrace tailWord_145401 prefixEnd_145401 74660600644490851618819 := by
  unfold tailWord_145401
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303210146244484358892057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3535473430829656239261371 5303210146244484358892057)
  ·
    refine ⟨3977407609683363269169043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5303210146244484358892057 3977407609683363269169043)
    ·
      refine ⟨5966111414525044903753565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3977407609683363269169043 5966111414525044903753565)
      ·
        refine ⟨2237291780446891838907587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5966111414525044903753565 2237291780446891838907587)
        ·
          refine ⟨3355937670670337758361381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237291780446891838907587 3355937670670337758361381)
          ·
            refine ⟨629238313250688329692759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3355937670670337758361381 629238313250688329692759)
            ·
              refine ⟨943857469876032494539139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629238313250688329692759 943857469876032494539139)
              ·
                refine ⟨1415786204814048741808709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943857469876032494539139 1415786204814048741808709)
                ·
                  refine ⟨265459913402634139089133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1415786204814048741808709 265459913402634139089133)
                  ·
                    refine ⟨99547467525987802158425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265459913402634139089133 99547467525987802158425)
                    ·
                      refine ⟨74660600644490851618819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99547467525987802158425 74660600644490851618819)
                      ·
                        rfl

theorem cell23_145401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_145401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145401 prefixEnd_145401 := by exact prefixLift 145401
  have htrace : WordTrace (prefixWord ++ tailWord_145401) baseStart_145401 baseEnd_145401 := by
    simpa [prefixWord, tailWord_145401, baseEnd_145401] using wordTrace_append hprefix tailTrace_145401
  have hstable : (prefixWord ++ tailWord_145401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145401).length < 2 ^ (prefixWord ++ tailWord_145401).sum := by decide
  have hdescent : baseEnd_145401 < baseStart_145401 := by decide
  rcases family_descends (prefixWord ++ tailWord_145401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145441 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 1, 6]
def baseStart_145441 : Nat := 118140960795 + 145441 * 2 ^ 59
def prefixEnd_145441 : Nat := 4983230072969 + 3 ^ 40 * 145441 * 2
def baseEnd_145441 : Nat := 24893713290223565039545

theorem tailTrace_145441 : CollatzResearch.WordTrace tailWord_145441 prefixEnd_145441 24893713290223565039545 := by
  unfold tailWord_145441
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304669066099571190348177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3536446044066380793565451 5304669066099571190348177)
  ·
    refine ⟨3978501799574678392761133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5304669066099571190348177 3978501799574678392761133)
    ·
      refine ⟨1491938174840504397285425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3978501799574678392761133 1491938174840504397285425)
      ·
        refine ⟨1118953631130378297964069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1491938174840504397285425 1118953631130378297964069)
        ·
          refine ⟨209803805836945930868263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1118953631130378297964069 209803805836945930868263)
          ·
            refine ⟨314705708755418896302395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209803805836945930868263 314705708755418896302395)
            ·
              refine ⟨472058563133128344453593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314705708755418896302395 472058563133128344453593)
              ·
                refine ⟨354043922349846258340195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472058563133128344453593 354043922349846258340195)
                ·
                  refine ⟨531065883524769387510293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354043922349846258340195 531065883524769387510293)
                  ·
                    refine ⟨24893713290223565039545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 531065883524769387510293 24893713290223565039545)
                    ·
                      rfl

theorem cell23_145441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_145441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145441 prefixEnd_145441 := by exact prefixLift 145441
  have htrace : WordTrace (prefixWord ++ tailWord_145441) baseStart_145441 baseEnd_145441 := by
    simpa [prefixWord, tailWord_145441, baseEnd_145441] using wordTrace_append hprefix tailTrace_145441
  have hstable : (prefixWord ++ tailWord_145441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145441).length < 2 ^ (prefixWord ++ tailWord_145441).sum := by decide
  have hdescent : baseEnd_145441 < baseStart_145441 := by decide
  rcases family_descends (prefixWord ++ tailWord_145441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145454 : List Nat := [4, 1, 3, 1, 1, 13]
def baseStart_145454 : Nat := 118140960795 + 145454 * 2 ^ 59
def prefixEnd_145454 : Nat := 4983230072969 + 3 ^ 40 * 145454 * 2
def baseEnd_145454 : Nat := 307357263864934750025

theorem tailTrace_145454 : CollatzResearch.WordTrace tailWord_145454 prefixEnd_145454 307357263864934750025 := by
  unfold tailWord_145454
  simp only [CollatzResearch.WordTrace]
  refine ⟨663142901881559301321427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3536762143368316273714277 663142901881559301321427)
  ·
    refine ⟨994714352822338951982141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 663142901881559301321427 994714352822338951982141)
    ·
      refine ⟨373017882308377106993303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 994714352822338951982141 373017882308377106993303)
      ·
        refine ⟨559526823462565660489955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373017882308377106993303 559526823462565660489955)
        ·
          refine ⟨839290235193848490734933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559526823462565660489955 839290235193848490734933)
          ·
            refine ⟨307357263864934750025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 839290235193848490734933 307357263864934750025)
            ·
              rfl

theorem cell23_145454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 13].length) (baseStart_145454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145454 prefixEnd_145454 := by exact prefixLift 145454
  have htrace : WordTrace (prefixWord ++ tailWord_145454) baseStart_145454 baseEnd_145454 := by
    simpa [prefixWord, tailWord_145454, baseEnd_145454] using wordTrace_append hprefix tailTrace_145454
  have hstable : (prefixWord ++ tailWord_145454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145454).length < 2 ^ (prefixWord ++ tailWord_145454).sum := by decide
  have hdescent : baseEnd_145454 < baseStart_145454 := by decide
  rcases family_descends (prefixWord ++ tailWord_145454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145458 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_145458 : Nat := 118140960795 + 145458 * 2 ^ 59
def prefixEnd_145458 : Nat := 4983230072969 + 3 ^ 40 * 145458 * 2
def baseEnd_145458 : Nat := 24896623013932376202019

theorem tailTrace_145458 : CollatzResearch.WordTrace tailWord_145458 prefixEnd_145458 24896623013932376202019 := by
  unfold tailWord_145458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326322276759495773429257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3536859404691988729144685 1326322276759495773429257)
  ·
    refine ⟨994741707569621830071943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1326322276759495773429257 994741707569621830071943)
    ·
      refine ⟨1492112561354432745107915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994741707569621830071943 1492112561354432745107915)
      ·
        refine ⟨2238168842031649117661873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492112561354432745107915 2238168842031649117661873)
        ·
          refine ⟨1678626631523736838246405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238168842031649117661873 1678626631523736838246405)
          ·
            refine ⟨314742493410700657171201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1678626631523736838246405 314742493410700657171201)
            ·
              refine ⟨236056870058025492878401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314742493410700657171201 236056870058025492878401)
              ·
                refine ⟨177042652543519119658801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236056870058025492878401 177042652543519119658801)
                ·
                  refine ⟨132781989407639339744101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177042652543519119658801 132781989407639339744101)
                  ·
                    refine ⟨24896623013932376202019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132781989407639339744101 24896623013932376202019)
                    ·
                      rfl

theorem cell23_145458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_145458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145458 prefixEnd_145458 := by exact prefixLift 145458
  have htrace : WordTrace (prefixWord ++ tailWord_145458) baseStart_145458 baseEnd_145458 := by
    simpa [prefixWord, tailWord_145458, baseEnd_145458] using wordTrace_append hprefix tailTrace_145458
  have hstable : (prefixWord ++ tailWord_145458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145458).length < 2 ^ (prefixWord ++ tailWord_145458).sum := by decide
  have hdescent : baseEnd_145458 < baseStart_145458 := by decide
  rcases family_descends (prefixWord ++ tailWord_145458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145481 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 3]
def baseStart_145481 : Nat := 118140960795 + 145481 * 2 ^ 59
def prefixEnd_145481 : Nat := 4983230072969 + 3 ^ 40 * 145481 * 2
def baseEnd_145481 : Nat := 74701679096850538618451

theorem tailTrace_145481 : CollatzResearch.WordTrace tailWord_145481 prefixEnd_145481 74701679096850538618451 := by
  unfold tailWord_145481
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306127985954658021804297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3537418657303105347869531 5306127985954658021804297)
  ·
    refine ⟨3979595989465993516353223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5306127985954658021804297 3979595989465993516353223)
    ·
      refine ⟨5969393984198990274529835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979595989465993516353223 5969393984198990274529835)
      ·
        refine ⟨8954090976298485411794753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5969393984198990274529835 8954090976298485411794753)
        ·
          refine ⟨6715568232223864058846065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8954090976298485411794753 6715568232223864058846065)
          ·
            refine ⟨5036676174167898044134549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6715568232223864058846065 5036676174167898044134549)
            ·
              refine ⟨236094195664120220818807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5036676174167898044134549 236094195664120220818807)
              ·
                refine ⟨354141293496180331228211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236094195664120220818807 354141293496180331228211)
                ·
                  refine ⟨531211940244270496842317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354141293496180331228211 531211940244270496842317)
                  ·
                    refine ⟨199204477591601436315869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531211940244270496842317 199204477591601436315869)
                    ·
                      refine ⟨74701679096850538618451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 199204477591601436315869 74701679096850538618451)
                      ·
                        rfl

theorem cell23_145481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_145481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145481 prefixEnd_145481 := by exact prefixLift 145481
  have htrace : WordTrace (prefixWord ++ tailWord_145481) baseStart_145481 baseEnd_145481 := by
    simpa [prefixWord, tailWord_145481, baseEnd_145481] using wordTrace_append hprefix tailTrace_145481
  have hstable : (prefixWord ++ tailWord_145481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145481).length < 2 ^ (prefixWord ++ tailWord_145481).sum := by decide
  have hdescent : baseEnd_145481 < baseStart_145481 := by decide
  rcases family_descends (prefixWord ++ tailWord_145481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145491 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 7, 3, 2]
def baseStart_145491 : Nat := 118140960795 + 145491 * 2 ^ 59
def prefixEnd_145491 : Nat := 4983230072969 + 3 ^ 40 * 145491 * 2
def baseEnd_145491 : Nat := 74706813903395499493405

theorem tailTrace_145491 : CollatzResearch.WordTrace tailWord_145491 prefixEnd_145491 74706813903395499493405 := by
  unfold tailWord_145491
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306492715918429729668327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3537661810612286486445551 5306492715918429729668327)
  ·
    refine ⟨7959739073877644594502491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5306492715918429729668327 7959739073877644594502491)
    ·
      refine ⟨11939608610816466891753737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7959739073877644594502491 11939608610816466891753737)
      ·
        refine ⟨8954706458112350168815303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11939608610816466891753737 8954706458112350168815303)
        ·
          refine ⟨13432059687168525253222955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8954706458112350168815303 13432059687168525253222955)
          ·
            refine ⟨20148089530752787879834433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13432059687168525253222955 20148089530752787879834433)
            ·
              refine ⟨15111067148064590909875825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20148089530752787879834433 15111067148064590909875825)
              ·
                refine ⟨11333300361048443182406869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15111067148064590909875825 11333300361048443182406869)
                ·
                  refine ⟨265624227212072887087661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11333300361048443182406869 265624227212072887087661)
                  ·
                    refine ⟨99609085204527332657873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 265624227212072887087661 99609085204527332657873)
                    ·
                      refine ⟨74706813903395499493405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99609085204527332657873 74706813903395499493405)
                      ·
                        rfl

theorem cell23_145491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3, 2].length) (baseStart_145491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145491 prefixEnd_145491 := by exact prefixLift 145491
  have htrace : WordTrace (prefixWord ++ tailWord_145491) baseStart_145491 baseEnd_145491 := by
    simpa [prefixWord, tailWord_145491, baseEnd_145491] using wordTrace_append hprefix tailTrace_145491
  have hstable : (prefixWord ++ tailWord_145491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145491).length < 2 ^ (prefixWord ++ tailWord_145491).sum := by decide
  have hdescent : baseEnd_145491 < baseStart_145491 := by decide
  rcases family_descends (prefixWord ++ tailWord_145491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145589 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_145589 : Nat := 118140960795 + 145589 * 2 ^ 59
def prefixEnd_145589 : Nat := 4983230072969 + 3 ^ 40 * 145589 * 2
def baseEnd_145589 : Nat := 74757135007536116067955

theorem tailTrace_145589 : CollatzResearch.WordTrace tailWord_145589 prefixEnd_145589 74757135007536116067955 := by
  unfold tailWord_145589
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310067069563392466735821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3540044713042261644490547 5310067069563392466735821)
  ·
    refine ⟨1991275151086272175025933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5310067069563392466735821 1991275151086272175025933)
    ·
      refine ⟨746728181657352065634725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1991275151086272175025933 746728181657352065634725)
      ·
        refine ⟨140011534060753512306511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 746728181657352065634725 140011534060753512306511)
        ·
          refine ⟨210017301091130268459767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140011534060753512306511 210017301091130268459767)
          ·
            refine ⟨315025951636695402689651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210017301091130268459767 315025951636695402689651)
            ·
              refine ⟨472538927455043104034477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315025951636695402689651 472538927455043104034477)
              ·
                refine ⟨177202097795641164012929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 472538927455043104034477 177202097795641164012929)
                ·
                  refine ⟨132901573346730873009697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177202097795641164012929 132901573346730873009697)
                  ·
                    refine ⟨99676180010048154757273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 132901573346730873009697 99676180010048154757273)
                    ·
                      refine ⟨74757135007536116067955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99676180010048154757273 74757135007536116067955)
                      ·
                        rfl

theorem cell23_145589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_145589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145589 prefixEnd_145589 := by exact prefixLift 145589
  have htrace : WordTrace (prefixWord ++ tailWord_145589) baseStart_145589 baseEnd_145589 := by
    simpa [prefixWord, tailWord_145589, baseEnd_145589] using wordTrace_append hprefix tailTrace_145589
  have hstable : (prefixWord ++ tailWord_145589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145589).length < 2 ^ (prefixWord ++ tailWord_145589).sum := by decide
  have hdescent : baseEnd_145589 < baseStart_145589 := by decide
  rcases family_descends (prefixWord ++ tailWord_145589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145631 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 3]
def baseStart_145631 : Nat := 118140960795 + 145631 * 2 ^ 59
def prefixEnd_145631 : Nat := 4983230072969 + 3 ^ 40 * 145631 * 2
def baseEnd_145631 : Nat := 74778701195024951742761

theorem tailTrace_145631 : CollatzResearch.WordTrace tailWord_145631 prefixEnd_145631 74778701195024951742761 := by
  unfold tailWord_145631
  simp only [CollatzResearch.WordTrace]
  refine ⟨5311598935411233639764747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3541065956940822426509831 5311598935411233639764747)
  ·
    refine ⟨7967398403116850459647121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5311598935411233639764747 7967398403116850459647121)
    ·
      refine ⟨5975548802337637844735341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7967398403116850459647121 5975548802337637844735341)
      ·
        refine ⟨2240830800876614191775753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5975548802337637844735341 2240830800876614191775753)
        ·
          refine ⟨1680623100657460643831815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2240830800876614191775753 1680623100657460643831815)
          ·
            refine ⟨2520934650986190965747723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680623100657460643831815 2520934650986190965747723)
            ·
              refine ⟨3781401976479286448621585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520934650986190965747723 3781401976479286448621585)
              ·
                refine ⟨2836051482359464836466189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3781401976479286448621585 2836051482359464836466189)
                ·
                  refine ⟨1063519305884799313674821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2836051482359464836466189 1063519305884799313674821)
                  ·
                    refine ⟨199409869853399871314029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1063519305884799313674821 199409869853399871314029)
                    ·
                      refine ⟨74778701195024951742761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 199409869853399871314029 74778701195024951742761)
                      ·
                        rfl

theorem cell23_145631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_145631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145631 prefixEnd_145631 := by exact prefixLift 145631
  have htrace : WordTrace (prefixWord ++ tailWord_145631) baseStart_145631 baseEnd_145631 := by
    simpa [prefixWord, tailWord_145631, baseEnd_145631] using wordTrace_append hprefix tailTrace_145631
  have hstable : (prefixWord ++ tailWord_145631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145631).length < 2 ^ (prefixWord ++ tailWord_145631).sum := by decide
  have hdescent : baseEnd_145631 < baseStart_145631 := by decide
  rcases family_descends (prefixWord ++ tailWord_145631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145651 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 6]
def baseStart_145651 : Nat := 118140960795 + 145651 * 2 ^ 59
def prefixEnd_145651 : Nat := 4983230072969 + 3 ^ 40 * 145651 * 2
def baseEnd_145651 : Nat := 8309885645346097054741

theorem tailTrace_145651 : CollatzResearch.WordTrace tailWord_145651 prefixEnd_145651 8309885645346097054741 := by
  unfold tailWord_145651
  simp only [CollatzResearch.WordTrace]
  refine ⟨5312328395338777055492807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3541552263559184703661871 5312328395338777055492807)
  ·
    refine ⟨7968492593008165583239211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5312328395338777055492807 7968492593008165583239211)
    ·
      refine ⟨11952738889512248374858817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7968492593008165583239211 11952738889512248374858817)
      ·
        refine ⟨8964554167134186281144113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11952738889512248374858817 8964554167134186281144113)
        ·
          refine ⟨6723415625350639710858085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8964554167134186281144113 6723415625350639710858085)
          ·
            refine ⟨1260640429753244945785891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6723415625350639710858085 1260640429753244945785891)
            ·
              refine ⟨1890960644629867418678837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260640429753244945785891 1890960644629867418678837)
              ·
                refine ⟨177277560434050070501141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1890960644629867418678837 177277560434050070501141)
                ·
                  refine ⟨8309885645346097054741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 177277560434050070501141 8309885645346097054741)
                  ·
                    rfl

theorem cell23_145651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 6].length) (baseStart_145651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145651 prefixEnd_145651 := by exact prefixLift 145651
  have htrace : WordTrace (prefixWord ++ tailWord_145651) baseStart_145651 baseEnd_145651 := by
    simpa [prefixWord, tailWord_145651, baseEnd_145651] using wordTrace_append hprefix tailTrace_145651
  have hstable : (prefixWord ++ tailWord_145651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145651).length < 2 ^ (prefixWord ++ tailWord_145651).sum := by decide
  have hdescent : baseEnd_145651 < baseStart_145651 := by decide
  rcases family_descends (prefixWord ++ tailWord_145651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145672 : List Nat := [2, 1, 3, 2, 3, 2, 2, 3, 1, 4]
def baseStart_145672 : Nat := 118140960795 + 145672 * 2 ^ 59
def prefixEnd_145672 : Nat := 4983230072969 + 3 ^ 40 * 145672 * 2
def baseEnd_145672 : Nat := 24933251300619763776691

theorem tailTrace_145672 : CollatzResearch.WordTrace tailWord_145672 prefixEnd_145672 24933251300619763776691 := by
  unfold tailWord_145672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656547164131348821003635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3542062885508465094671513 2656547164131348821003635)
  ·
    refine ⟨3984820746197023231505453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2656547164131348821003635 3984820746197023231505453)
    ·
      refine ⟨1494307779823883711814545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3984820746197023231505453 1494307779823883711814545)
      ·
        refine ⟨1120730834867912783860909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1494307779823883711814545 1120730834867912783860909)
        ·
          refine ⟨420274063075467293947841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1120730834867912783860909 420274063075467293947841)
          ·
            refine ⟨315205547306600470460881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420274063075467293947841 315205547306600470460881)
            ·
              refine ⟨236404160479950352845661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315205547306600470460881 236404160479950352845661)
              ·
                refine ⟨88651560179981382317123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236404160479950352845661 88651560179981382317123)
                ·
                  refine ⟨132977340269972073475685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88651560179981382317123 132977340269972073475685)
                  ·
                    refine ⟨24933251300619763776691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132977340269972073475685 24933251300619763776691)
                    ·
                      rfl

theorem cell23_145672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_145672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145672 prefixEnd_145672 := by exact prefixLift 145672
  have htrace : WordTrace (prefixWord ++ tailWord_145672) baseStart_145672 baseEnd_145672 := by
    simpa [prefixWord, tailWord_145672, baseEnd_145672] using wordTrace_append hprefix tailTrace_145672
  have hstable : (prefixWord ++ tailWord_145672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145672).length < 2 ^ (prefixWord ++ tailWord_145672).sum := by decide
  have hdescent : baseEnd_145672 < baseStart_145672 := by decide
  rcases family_descends (prefixWord ++ tailWord_145672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145695 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 3]
def baseStart_145695 : Nat := 118140960795 + 145695 * 2 ^ 59
def prefixEnd_145695 : Nat := 4983230072969 + 3 ^ 40 * 145695 * 2
def baseEnd_145695 : Nat := 74811563956912701342467

theorem tailTrace_145695 : CollatzResearch.WordTrace tailWord_145695 prefixEnd_145695 74811563956912701342467 := by
  unfold tailWord_145695
  simp only [CollatzResearch.WordTrace]
  refine ⟨5313933207179372570094539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3542622138119581713396359 5313933207179372570094539)
  ·
    refine ⟨7970899810769058855141809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5313933207179372570094539 7970899810769058855141809)
    ·
      refine ⟨5978174858076794141356357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7970899810769058855141809 5978174858076794141356357)
      ·
        refine ⟨1120907785889398901504317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5978174858076794141356357 1120907785889398901504317)
        ·
          refine ⟨420340419708524588064119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1120907785889398901504317 420340419708524588064119)
          ·
            refine ⟨630510629562786882096179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420340419708524588064119 630510629562786882096179)
            ·
              refine ⟨945765944344180323144269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630510629562786882096179 945765944344180323144269)
              ·
                refine ⟨354662229129067621179101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 945765944344180323144269 354662229129067621179101)
                ·
                  refine ⟨132998335923400357942163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354662229129067621179101 132998335923400357942163)
                  ·
                    refine ⟨199497503885100536913245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 132998335923400357942163 199497503885100536913245)
                    ·
                      refine ⟨74811563956912701342467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 199497503885100536913245 74811563956912701342467)
                      ·
                        rfl

theorem cell23_145695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_145695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145695 prefixEnd_145695 := by exact prefixLift 145695
  have htrace : WordTrace (prefixWord ++ tailWord_145695) baseStart_145695 baseEnd_145695 := by
    simpa [prefixWord, tailWord_145695, baseEnd_145695] using wordTrace_append hprefix tailTrace_145695
  have hstable : (prefixWord ++ tailWord_145695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145695).length < 2 ^ (prefixWord ++ tailWord_145695).sum := by decide
  have hdescent : baseEnd_145695 < baseStart_145695 := by decide
  rcases family_descends (prefixWord ++ tailWord_145695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145738 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_145738 : Nat := 118140960795 + 145738 * 2 ^ 59
def prefixEnd_145738 : Nat := 4983230072969 + 3 ^ 40 * 145738 * 2
def baseEnd_145738 : Nat := 74833643625056033104769

theorem tailTrace_145738 : CollatzResearch.WordTrace tailWord_145738 prefixEnd_145738 74833643625056033104769 := by
  unfold tailWord_145738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328875386505897728477467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3543667697349060609273245 1328875386505897728477467)
  ·
    refine ⟨1993313079758846592716201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1328875386505897728477467 1993313079758846592716201)
    ·
      refine ⟨1494984809819134944537151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1993313079758846592716201 1494984809819134944537151)
      ·
        refine ⟨2242477214728702416805727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494984809819134944537151 2242477214728702416805727)
        ·
          refine ⟨3363715822093053625208591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242477214728702416805727 3363715822093053625208591)
          ·
            refine ⟨5045573733139580437812887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363715822093053625208591 5045573733139580437812887)
            ·
              refine ⟨7568360599709370656719331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045573733139580437812887 7568360599709370656719331)
              ·
                refine ⟨11352540899564055985078997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7568360599709370656719331 11352540899564055985078997)
                ·
                  refine ⟨266075177333532562150289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11352540899564055985078997 266075177333532562150289)
                  ·
                    refine ⟨199556383000149421612717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266075177333532562150289 199556383000149421612717)
                    ·
                      refine ⟨74833643625056033104769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 199556383000149421612717 74833643625056033104769)
                      ·
                        rfl

theorem cell23_145738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_145738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145738 prefixEnd_145738 := by exact prefixLift 145738
  have htrace : WordTrace (prefixWord ++ tailWord_145738) baseStart_145738 baseEnd_145738 := by
    simpa [prefixWord, tailWord_145738, baseEnd_145738] using wordTrace_append hprefix tailTrace_145738
  have hstable : (prefixWord ++ tailWord_145738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145738).length < 2 ^ (prefixWord ++ tailWord_145738).sum := by decide
  have hdescent : baseEnd_145738 < baseStart_145738 := by decide
  rcases family_descends (prefixWord ++ tailWord_145738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145748 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_145748 : Nat := 118140960795 + 145748 * 2 ^ 59
def prefixEnd_145748 : Nat := 4983230072969 + 3 ^ 40 * 145748 * 2
def baseEnd_145748 : Nat := 74838778431600993979723

theorem tailTrace_145748 : CollatzResearch.WordTrace tailWord_145748 prefixEnd_145748 74838778431600993979723 := by
  unfold tailWord_145748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2657933137993681310886949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3543910850658241747849265 2657933137993681310886949)
  ·
    refine ⟨498362463373815245791303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2657933137993681310886949 498362463373815245791303)
    ·
      refine ⟨747543695060722868686955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 498362463373815245791303 747543695060722868686955)
      ·
        refine ⟨1121315542591084303030433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747543695060722868686955 1121315542591084303030433)
        ·
          refine ⟨840986656943313227272825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1121315542591084303030433 840986656943313227272825)
          ·
            refine ⟨630739992707484920454619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840986656943313227272825 630739992707484920454619)
            ·
              refine ⟨946109989061227380681929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630739992707484920454619 946109989061227380681929)
              ·
                refine ⟨709582491795920535511447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946109989061227380681929 709582491795920535511447)
                ·
                  refine ⟨1064373737693880803267171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709582491795920535511447 1064373737693880803267171)
                  ·
                    refine ⟨1596560606540821204900757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1064373737693880803267171 1596560606540821204900757)
                    ·
                      refine ⟨74838778431600993979723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1596560606540821204900757 74838778431600993979723)
                      ·
                        rfl

theorem cell23_145748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_145748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145748 prefixEnd_145748 := by exact prefixLift 145748
  have htrace : WordTrace (prefixWord ++ tailWord_145748) baseStart_145748 baseEnd_145748 := by
    simpa [prefixWord, tailWord_145748, baseEnd_145748] using wordTrace_append hprefix tailTrace_145748
  have hstable : (prefixWord ++ tailWord_145748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145748).length < 2 ^ (prefixWord ++ tailWord_145748).sum := by decide
  have hdescent : baseEnd_145748 < baseStart_145748 := by decide
  rcases family_descends (prefixWord ++ tailWord_145748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145762 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_145762 : Nat := 118140960795 + 145762 * 2 ^ 59
def prefixEnd_145762 : Nat := 4983230072969 + 3 ^ 40 * 145762 * 2
def baseEnd_145762 : Nat := 24948655720254646401553

theorem tailTrace_145762 : CollatzResearch.WordTrace tailWord_145762 prefixEnd_145762 24948655720254646401553 := by
  unfold tailWord_145762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329094224484160753195885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3544251265291095341855693 1329094224484160753195885)
  ·
    refine ⟨498410334181560282448457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1329094224484160753195885 498410334181560282448457)
    ·
      refine ⟨373807750636170211836343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498410334181560282448457 373807750636170211836343)
      ·
        refine ⟨560711625954255317754515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373807750636170211836343 560711625954255317754515)
        ·
          refine ⟨841067438931382976631773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560711625954255317754515 841067438931382976631773)
          ·
            refine ⟨315400289599268616236915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 841067438931382976631773 315400289599268616236915)
            ·
              refine ⟨473100434398902924355373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315400289599268616236915 473100434398902924355373)
              ·
                refine ⟨177412662899588596633265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473100434398902924355373 177412662899588596633265)
                ·
                  refine ⟨133059497174691447474949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177412662899588596633265 133059497174691447474949)
                  ·
                    refine ⟨24948655720254646401553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133059497174691447474949 24948655720254646401553)
                    ·
                      rfl

theorem cell23_145762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_145762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145762 prefixEnd_145762 := by exact prefixLift 145762
  have htrace : WordTrace (prefixWord ++ tailWord_145762) baseStart_145762 baseEnd_145762 := by
    simpa [prefixWord, tailWord_145762, baseEnd_145762] using wordTrace_append hprefix tailTrace_145762
  have hstable : (prefixWord ++ tailWord_145762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145762).length < 2 ^ (prefixWord ++ tailWord_145762).sum := by decide
  have hdescent : baseEnd_145762 < baseStart_145762 := by decide
  rcases family_descends (prefixWord ++ tailWord_145762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145771 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 2, 7]
def baseStart_145771 : Nat := 118140960795 + 145771 * 2 ^ 59
def prefixEnd_145771 : Nat := 4983230072969 + 3 ^ 40 * 145771 * 2
def baseEnd_145771 : Nat := 24950196162218134664039

theorem tailTrace_145771 : CollatzResearch.WordTrace tailWord_145771 prefixEnd_145771 24950196162218134664039 := by
  unfold tailWord_145771
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316705154904037549861167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3544470103269358366574111 5316705154904037549861167)
  ·
    refine ⟨7975057732356056324791751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5316705154904037549861167 7975057732356056324791751)
    ·
      refine ⟨11962586598534084487187627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7975057732356056324791751 11962586598534084487187627)
      ·
        refine ⟨17943879897801126730781441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11962586598534084487187627 17943879897801126730781441)
        ·
          refine ⟨13457909923350845048086081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17943879897801126730781441 13457909923350845048086081)
          ·
            refine ⟨10093432442513133786064561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13457909923350845048086081 10093432442513133786064561)
            ·
              refine ⟨7570074331884850339548421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10093432442513133786064561 7570074331884850339548421)
              ·
                refine ⟨1419388937228409438665329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7570074331884850339548421 1419388937228409438665329)
                ·
                  refine ⟨1064541702921307078998997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419388937228409438665329 1064541702921307078998997)
                  ·
                    refine ⟨24950196162218134664039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1064541702921307078998997 24950196162218134664039)
                    ·
                      rfl

theorem cell23_145771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_145771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145771 prefixEnd_145771 := by exact prefixLift 145771
  have htrace : WordTrace (prefixWord ++ tailWord_145771) baseStart_145771 baseEnd_145771 := by
    simpa [prefixWord, tailWord_145771, baseEnd_145771] using wordTrace_append hprefix tailTrace_145771
  have hstable : (prefixWord ++ tailWord_145771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145771).length < 2 ^ (prefixWord ++ tailWord_145771).sum := by decide
  have hdescent : baseEnd_145771 < baseStart_145771 := by decide
  rcases family_descends (prefixWord ++ tailWord_145771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145791 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_145791 : Nat := 118140960795 + 145791 * 2 ^ 59
def prefixEnd_145791 : Nat := 4983230072969 + 3 ^ 40 * 145791 * 2
def baseEnd_145791 : Nat := 74860858099744325742025

theorem tailTrace_145791 : CollatzResearch.WordTrace tailWord_145791 prefixEnd_145791 74860858099744325742025 := by
  unfold tailWord_145791
  simp only [CollatzResearch.WordTrace]
  refine ⟨5317434614831580965589227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3544956409887720643726151 5317434614831580965589227)
  ·
    refine ⟨7976151922247371448383841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5317434614831580965589227 7976151922247371448383841)
    ·
      refine ⟨5982113941685528586287881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7976151922247371448383841 5982113941685528586287881)
      ·
        refine ⟨4486585456264146439715911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5982113941685528586287881 4486585456264146439715911)
        ·
          refine ⟨6729878184396219659573867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4486585456264146439715911 6729878184396219659573867)
          ·
            refine ⟨10094817276594329489360801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6729878184396219659573867 10094817276594329489360801)
            ·
              refine ⟨7571112957445747117020601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10094817276594329489360801 7571112957445747117020601)
              ·
                refine ⟨5678334718084310337765451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7571112957445747117020601 5678334718084310337765451)
                ·
                  refine ⟨8517502077126465506648177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678334718084310337765451 8517502077126465506648177)
                  ·
                    refine ⟨6388126557844849129986133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8517502077126465506648177 6388126557844849129986133)
                    ·
                      refine ⟨74860858099744325742025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 6388126557844849129986133 74860858099744325742025)
                      ·
                        rfl

theorem cell23_145791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_145791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145791 prefixEnd_145791 := by exact prefixLift 145791
  have htrace : WordTrace (prefixWord ++ tailWord_145791) baseStart_145791 baseEnd_145791 := by
    simpa [prefixWord, tailWord_145791, baseEnd_145791] using wordTrace_append hprefix tailTrace_145791
  have hstable : (prefixWord ++ tailWord_145791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145791).length < 2 ^ (prefixWord ++ tailWord_145791).sum := by decide
  have hdescent : baseEnd_145791 < baseStart_145791 := by decide
  rcases family_descends (prefixWord ++ tailWord_145791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145818 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_145818 : Nat := 118140960795 + 145818 * 2 ^ 59
def prefixEnd_145818 : Nat := 4983230072969 + 3 ^ 40 * 145818 * 2
def baseEnd_145818 : Nat := 24958240692471906701467

theorem tailTrace_145818 : CollatzResearch.WordTrace tailWord_145818 prefixEnd_145818 24958240692471906701467 := by
  unfold tailWord_145818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329604846433441144205527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3545612923822509717881405 1329604846433441144205527)
  ·
    refine ⟨1994407269650161716308291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1329604846433441144205527 1994407269650161716308291)
    ·
      refine ⟨2991610904475242574462437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1994407269650161716308291 2991610904475242574462437)
      ·
        refine ⟨560927044589107982711707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2991610904475242574462437 560927044589107982711707)
        ·
          refine ⟨841390566883661974067561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560927044589107982711707 841390566883661974067561)
          ·
            refine ⟨631042925162746480550671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841390566883661974067561 631042925162746480550671)
            ·
              refine ⟨946564387744119720826007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631042925162746480550671 946564387744119720826007)
              ·
                refine ⟨1419846581616179581239011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946564387744119720826007 1419846581616179581239011)
                ·
                  refine ⟨2129769872424269371858517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419846581616179581239011 2129769872424269371858517)
                  ·
                    refine ⟨24958240692471906701467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2129769872424269371858517 24958240692471906701467)
                    ·
                      rfl

theorem cell23_145818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_145818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145818 prefixEnd_145818 := by exact prefixLift 145818
  have htrace : WordTrace (prefixWord ++ tailWord_145818) baseStart_145818 baseEnd_145818 := by
    simpa [prefixWord, tailWord_145818, baseEnd_145818] using wordTrace_append hprefix tailTrace_145818
  have hstable : (prefixWord ++ tailWord_145818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145818).length < 2 ^ (prefixWord ++ tailWord_145818).sum := by decide
  have hdescent : baseEnd_145818 < baseStart_145818 := by decide
  rcases family_descends (prefixWord ++ tailWord_145818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145828 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_145828 : Nat := 118140960795 + 145828 * 2 ^ 59
def prefixEnd_145828 : Nat := 4983230072969 + 3 ^ 40 * 145828 * 2
def baseEnd_145828 : Nat := 74879856883960680979355

theorem tailTrace_145828 : CollatzResearch.WordTrace tailWord_145828 prefixEnd_145828 74879856883960680979355 := by
  unfold tailWord_145828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2659392057848768142343069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3545856077131690856457425 2659392057848768142343069)
  ·
    refine ⟨997272021693288053378651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2659392057848768142343069 997272021693288053378651)
    ·
      refine ⟨1495908032539932080067977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997272021693288053378651 1495908032539932080067977)
      ·
        refine ⟨1121931024404949060050983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1495908032539932080067977 1121931024404949060050983)
        ·
          refine ⟨1682896536607423590076475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121931024404949060050983 1682896536607423590076475)
          ·
            refine ⟨2524344804911135385114713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682896536607423590076475 2524344804911135385114713)
            ·
              refine ⟨1893258603683351538836035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2524344804911135385114713 1893258603683351538836035)
              ·
                refine ⟨2839887905525027308254053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893258603683351538836035 2839887905525027308254053)
                ·
                  refine ⟨532478982285942620297635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2839887905525027308254053 532478982285942620297635)
                  ·
                    refine ⟨798718473428913930446453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 532478982285942620297635 798718473428913930446453)
                    ·
                      refine ⟨74879856883960680979355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 798718473428913930446453 74879856883960680979355)
                      ·
                        rfl

theorem cell23_145828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_145828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145828 prefixEnd_145828 := by exact prefixLift 145828
  have htrace : WordTrace (prefixWord ++ tailWord_145828) baseStart_145828 baseEnd_145828 := by
    simpa [prefixWord, tailWord_145828, baseEnd_145828] using wordTrace_append hprefix tailTrace_145828
  have hstable : (prefixWord ++ tailWord_145828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145828).length < 2 ^ (prefixWord ++ tailWord_145828).sum := by decide
  have hdescent : baseEnd_145828 < baseStart_145828 := by decide
  rcases family_descends (prefixWord ++ tailWord_145828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145842 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_145842 : Nat := 118140960795 + 145842 * 2 ^ 59
def prefixEnd_145842 : Nat := 4983230072969 + 3 ^ 40 * 145842 * 2
def baseEnd_145842 : Nat := 74887045613123626204291

theorem tailTrace_145842 : CollatzResearch.WordTrace tailWord_145842 prefixEnd_145842 74887045613123626204291 := by
  unfold tailWord_145842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329823684411704168923945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3546196491764544450463853 1329823684411704168923945)
  ·
    refine ⟨997367763308778126692959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1329823684411704168923945 997367763308778126692959)
    ·
      refine ⟨1496051644963167190039439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997367763308778126692959 1496051644963167190039439)
      ·
        refine ⟨2244077467444750785059159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496051644963167190039439 2244077467444750785059159)
        ·
          refine ⟨3366116201167126177588739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244077467444750785059159 3366116201167126177588739)
          ·
            refine ⟨5049174301750689266383109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3366116201167126177588739 5049174301750689266383109)
            ·
              refine ⟨946720181578254237446833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5049174301750689266383109 946720181578254237446833)
              ·
                refine ⟨710040136183690678085125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946720181578254237446833 710040136183690678085125)
                ·
                  refine ⟨133132525534442002140961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710040136183690678085125 133132525534442002140961)
                  ·
                    refine ⟨99849394150831501605721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 133132525534442002140961 99849394150831501605721)
                    ·
                      refine ⟨74887045613123626204291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99849394150831501605721 74887045613123626204291)
                      ·
                        rfl

theorem cell23_145842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_145842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145842 prefixEnd_145842 := by exact prefixLift 145842
  have htrace : WordTrace (prefixWord ++ tailWord_145842) baseStart_145842 baseEnd_145842 := by
    simpa [prefixWord, tailWord_145842, baseEnd_145842] using wordTrace_append hprefix tailTrace_145842
  have hstable : (prefixWord ++ tailWord_145842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145842).length < 2 ^ (prefixWord ++ tailWord_145842).sum := by decide
  have hdescent : baseEnd_145842 < baseStart_145842 := by decide
  rcases family_descends (prefixWord ++ tailWord_145842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145865 : List Nat := [1, 2, 1, 1, 2, 1, 6, 4, 5]
def baseStart_145865 : Nat := 118140960795 + 145865 * 2 ^ 59
def prefixEnd_145865 : Nat := 4983230072969 + 3 ^ 40 * 145865 * 2
def baseEnd_145865 : Nat := 8322095074241892912965

theorem tailTrace_145865 : CollatzResearch.WordTrace tailWord_145865 prefixEnd_145865 8322095074241892912965 := by
  unfold tailWord_145865
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320133616563491603783049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3546755744375661069188699 5320133616563491603783049)
  ·
    refine ⟨3990100212422618702837287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5320133616563491603783049 3990100212422618702837287)
    ·
      refine ⟨5985150318633928054255931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990100212422618702837287 5985150318633928054255931)
      ·
        refine ⟨8977725477950892081383897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985150318633928054255931 8977725477950892081383897)
        ·
          refine ⟨6733294108463169061037923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8977725477950892081383897 6733294108463169061037923)
          ·
            refine ⟨10099941162694753591556885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733294108463169061037923 10099941162694753591556885)
            ·
              refine ⟨473434742001316574604229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10099941162694753591556885 473434742001316574604229)
              ·
                refine ⟨88769014125246857738293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473434742001316574604229 88769014125246857738293)
                ·
                  refine ⟨8322095074241892912965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88769014125246857738293 8322095074241892912965)
                  ·
                    rfl

theorem cell23_145865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 5].length) (baseStart_145865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145865 prefixEnd_145865 := by exact prefixLift 145865
  have htrace : WordTrace (prefixWord ++ tailWord_145865) baseStart_145865 baseEnd_145865 := by
    simpa [prefixWord, tailWord_145865, baseEnd_145865] using wordTrace_append hprefix tailTrace_145865
  have hstable : (prefixWord ++ tailWord_145865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145865).length < 2 ^ (prefixWord ++ tailWord_145865).sum := by decide
  have hdescent : baseEnd_145865 < baseStart_145865 := by decide
  rcases family_descends (prefixWord ++ tailWord_145865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145895 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 2, 5]
def baseStart_145895 : Nat := 118140960795 + 145895 * 2 ^ 59
def prefixEnd_145895 : Nat := 4983230072969 + 3 ^ 40 * 145895 * 2
def baseEnd_145895 : Nat := 24971420029270639613849

theorem tailTrace_145895 : CollatzResearch.WordTrace tailWord_145895 prefixEnd_145895 24971420029270639613849 := by
  unfold tailWord_145895
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321227806454806727375139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3547485204303204484916759 5321227806454806727375139)
  ·
    refine ⟨7981841709682210091062709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5321227806454806727375139 7981841709682210091062709)
    ·
      refine ⟨748297660282707196037129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7981841709682210091062709 748297660282707196037129)
      ·
        refine ⟨561223245212030397027847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748297660282707196037129 561223245212030397027847)
        ·
          refine ⟨841834867818045595541771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561223245212030397027847 841834867818045595541771)
          ·
            refine ⟨1262752301727068393312657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841834867818045595541771 1262752301727068393312657)
            ·
              refine ⟨947064226295301294984493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262752301727068393312657 947064226295301294984493)
              ·
                refine ⟨355149084860737985619185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947064226295301294984493 355149084860737985619185)
                ·
                  refine ⟨266361813645553489214389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355149084860737985619185 266361813645553489214389)
                  ·
                    refine ⟨24971420029270639613849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 266361813645553489214389 24971420029270639613849)
                    ·
                      rfl

theorem cell23_145895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_145895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145895 prefixEnd_145895 := by exact prefixLift 145895
  have htrace : WordTrace (prefixWord ++ tailWord_145895) baseStart_145895 baseEnd_145895 := by
    simpa [prefixWord, tailWord_145895, baseEnd_145895] using wordTrace_append hprefix tailTrace_145895
  have hstable : (prefixWord ++ tailWord_145895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145895).length < 2 ^ (prefixWord ++ tailWord_145895).sum := by decide
  have hdescent : baseEnd_145895 < baseStart_145895 := by decide
  rcases family_descends (prefixWord ++ tailWord_145895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145992 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_145992 : Nat := 118140960795 + 145992 * 2 ^ 59
def prefixEnd_145992 : Nat := 4983230072969 + 3 ^ 40 * 145992 * 2
def baseEnd_145992 : Nat := 74964067711298039328601

theorem tailTrace_145992 : CollatzResearch.WordTrace tailWord_145992 prefixEnd_145992 74964067711298039328601 := by
  unfold tailWord_145992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662382843551696146828115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3549843791402261529104153 2662382843551696146828115)
  ·
    refine ⟨3993574265327544220242173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662382843551696146828115 3993574265327544220242173)
    ·
      refine ⟨1497590349497829082590815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3993574265327544220242173 1497590349497829082590815)
      ·
        refine ⟨2246385524246743623886223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497590349497829082590815 2246385524246743623886223)
        ·
          refine ⟨3369578286370115435829335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246385524246743623886223 3369578286370115435829335)
          ·
            refine ⟨5054367429555173153744003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369578286370115435829335 5054367429555173153744003)
            ·
              refine ⟨7581551144332759730616005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054367429555173153744003 7581551144332759730616005)
              ·
                refine ⟨1421540839562392449490501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7581551144332759730616005 1421540839562392449490501)
                ·
                  refine ⟨266538907417948584279469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1421540839562392449490501 266538907417948584279469)
                  ·
                    refine ⟨99952090281730719104801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266538907417948584279469 99952090281730719104801)
                    ·
                      refine ⟨74964067711298039328601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99952090281730719104801 74964067711298039328601)
                      ·
                        rfl

theorem cell23_145992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_145992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_145992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_145992 prefixEnd_145992 := by exact prefixLift 145992
  have htrace : WordTrace (prefixWord ++ tailWord_145992) baseStart_145992 baseEnd_145992 := by
    simpa [prefixWord, tailWord_145992, baseEnd_145992] using wordTrace_append hprefix tailTrace_145992
  have hstable : (prefixWord ++ tailWord_145992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145992).length < 2 ^ (prefixWord ++ tailWord_145992).sum := by decide
  have hdescent : baseEnd_145992 < baseStart_145992 := by decide
  rcases family_descends (prefixWord ++ tailWord_145992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146002 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_146002 : Nat := 118140960795 + 146002 * 2 ^ 59
def prefixEnd_146002 : Nat := 4983230072969 + 3 ^ 40 * 146002 * 2
def baseEnd_146002 : Nat := 24989734172614333401185

theorem tailTrace_146002 : CollatzResearch.WordTrace tailWord_146002 prefixEnd_146002 24989734172614333401185 := by
  unfold tailWord_146002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1331282604266791000380065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3550086944711442667680173 1331282604266791000380065)
  ·
    refine ⟨998461953200093250285049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1331282604266791000380065 998461953200093250285049)
    ·
      refine ⟨748846464900069937713787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 998461953200093250285049 748846464900069937713787)
      ·
        refine ⟨1123269697350104906570681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748846464900069937713787 1123269697350104906570681)
        ·
          refine ⟨842452273012578679928011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123269697350104906570681 842452273012578679928011)
          ·
            refine ⟨1263678409518868019892017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842452273012578679928011 1263678409518868019892017)
            ·
              refine ⟨947758807139151014919013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263678409518868019892017 947758807139151014919013)
              ·
                refine ⟨177704776338590815297315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 947758807139151014919013 177704776338590815297315)
                ·
                  refine ⟨266557164507886222945973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177704776338590815297315 266557164507886222945973)
                  ·
                    refine ⟨24989734172614333401185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 266557164507886222945973 24989734172614333401185)
                    ·
                      rfl

theorem cell23_146002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_146002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146002 prefixEnd_146002 := by exact prefixLift 146002
  have htrace : WordTrace (prefixWord ++ tailWord_146002) baseStart_146002 baseEnd_146002 := by
    simpa [prefixWord, tailWord_146002, baseEnd_146002] using wordTrace_append hprefix tailTrace_146002
  have hstable : (prefixWord ++ tailWord_146002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146002).length < 2 ^ (prefixWord ++ tailWord_146002).sum := by decide
  have hdescent : baseEnd_146002 < baseStart_146002 := by decide
  rcases family_descends (prefixWord ++ tailWord_146002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146025 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_146025 : Nat := 118140960795 + 146025 * 2 ^ 59
def prefixEnd_146025 : Nat := 4983230072969 + 3 ^ 40 * 146025 * 2
def baseEnd_146025 : Nat := 74981012572896410215949

theorem tailTrace_146025 : CollatzResearch.WordTrace tailWord_146025 prefixEnd_146025 74981012572896410215949 := by
  unfold tailWord_146025
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325969295983838929607529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3550646197322559286405019 5325969295983838929607529)
  ·
    refine ⟨3994476971987879197205647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5325969295983838929607529 3994476971987879197205647)
    ·
      refine ⟨5991715457981818795808471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3994476971987879197205647 5991715457981818795808471)
      ·
        refine ⟨8987573186972728193712707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991715457981818795808471 8987573186972728193712707)
        ·
          refine ⟨13481359780459092290569061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8987573186972728193712707 13481359780459092290569061)
          ·
            refine ⟨2527754958836079804481699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13481359780459092290569061 2527754958836079804481699)
            ·
              refine ⟨3791632438254119706722549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527754958836079804481699 3791632438254119706722549)
              ·
                refine ⟨355465541086323722505239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3791632438254119706722549 355465541086323722505239)
                ·
                  refine ⟨533198311629485583757859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355465541086323722505239 533198311629485583757859)
                  ·
                    refine ⟨799797467444228375636789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 533198311629485583757859 799797467444228375636789)
                    ·
                      refine ⟨74981012572896410215949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 799797467444228375636789 74981012572896410215949)
                      ·
                        rfl

theorem cell23_146025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_146025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146025 prefixEnd_146025 := by exact prefixLift 146025
  have htrace : WordTrace (prefixWord ++ tailWord_146025) baseStart_146025 baseEnd_146025 := by
    simpa [prefixWord, tailWord_146025, baseEnd_146025] using wordTrace_append hprefix tailTrace_146025
  have hstable : (prefixWord ++ tailWord_146025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146025).length < 2 ^ (prefixWord ++ tailWord_146025).sum := by decide
  have hdescent : baseEnd_146025 < baseStart_146025 := by decide
  rcases family_descends (prefixWord ++ tailWord_146025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146039 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 3, 2, 2]
def baseStart_146039 : Nat := 118140960795 + 146039 * 2 ^ 59
def prefixEnd_146039 : Nat := 4983230072969 + 3 ^ 40 * 146039 * 2
def baseEnd_146039 : Nat := 74988201302059355440885

theorem tailTrace_146039 : CollatzResearch.WordTrace tailWord_146039 prefixEnd_146039 74988201302059355440885 := by
  unfold tailWord_146039
  simp only [CollatzResearch.WordTrace]
  refine ⟨5326479917933119320617171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3550986611955412880411447 5326479917933119320617171)
  ·
    refine ⟨7989719876899678980925757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5326479917933119320617171 7989719876899678980925757)
    ·
      refine ⟨2996144953837379617847159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7989719876899678980925757 2996144953837379617847159)
      ·
        refine ⟨4494217430756069426770739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996144953837379617847159 4494217430756069426770739)
        ·
          refine ⟨6741326146134104140156109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4494217430756069426770739 6741326146134104140156109)
          ·
            refine ⟨2527997304800289052558541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6741326146134104140156109 2527997304800289052558541)
            ·
              refine ⟨947998989300108394709453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527997304800289052558541 947998989300108394709453)
              ·
                refine ⟨355499620987540648016045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947998989300108394709453 355499620987540648016045)
                ·
                  refine ⟨133312357870327743006017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355499620987540648016045 133312357870327743006017)
                  ·
                    refine ⟨99984268402745807254513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 133312357870327743006017 99984268402745807254513)
                    ·
                      refine ⟨74988201302059355440885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 99984268402745807254513 74988201302059355440885)
                      ·
                        rfl

theorem cell23_146039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_146039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146039 prefixEnd_146039 := by exact prefixLift 146039
  have htrace : WordTrace (prefixWord ++ tailWord_146039) baseStart_146039 baseEnd_146039 := by
    simpa [prefixWord, tailWord_146039, baseEnd_146039] using wordTrace_append hprefix tailTrace_146039
  have hstable : (prefixWord ++ tailWord_146039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146039).length < 2 ^ (prefixWord ++ tailWord_146039).sum := by decide
  have hdescent : baseEnd_146039 < baseStart_146039 := by decide
  rcases family_descends (prefixWord ++ tailWord_146039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146052 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_146052 : Nat := 118140960795 + 146052 * 2 ^ 59
def prefixEnd_146052 : Nat := 4983230072969 + 3 ^ 40 * 146052 * 2
def baseEnd_146052 : Nat := 74994876550567804578325

theorem tailTrace_146052 : CollatzResearch.WordTrace tailWord_146052 prefixEnd_146052 74994876550567804578325 := by
  unfold tailWord_146052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663477033443011270420205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3551302711257348360560273 2663477033443011270420205)
  ·
    refine ⟨998803887541129226407577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2663477033443011270420205 998803887541129226407577)
    ·
      refine ⟨749102915655846919805683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 998803887541129226407577 749102915655846919805683)
      ·
        refine ⟨1123654373483770379708525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749102915655846919805683 1123654373483770379708525)
        ·
          refine ⟨421370390056413892390697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1123654373483770379708525 421370390056413892390697)
          ·
            refine ⟨316027792542310419293023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421370390056413892390697 316027792542310419293023)
            ·
              refine ⟨474041688813465628939535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316027792542310419293023 474041688813465628939535)
              ·
                refine ⟨711062533220198443409303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474041688813465628939535 711062533220198443409303)
                ·
                  refine ⟨1066593799830297665113955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711062533220198443409303 1066593799830297665113955)
                  ·
                    refine ⟨1599890699745446497670933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1066593799830297665113955 1599890699745446497670933)
                    ·
                      refine ⟨74994876550567804578325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1599890699745446497670933 74994876550567804578325)
                      ·
                        rfl

theorem cell23_146052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_146052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146052 prefixEnd_146052 := by exact prefixLift 146052
  have htrace : WordTrace (prefixWord ++ tailWord_146052) baseStart_146052 baseEnd_146052 := by
    simpa [prefixWord, tailWord_146052, baseEnd_146052] using wordTrace_append hprefix tailTrace_146052
  have hstable : (prefixWord ++ tailWord_146052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146052).length < 2 ^ (prefixWord ++ tailWord_146052).sum := by decide
  have hdescent : baseEnd_146052 < baseStart_146052 := by decide
  rcases family_descends (prefixWord ++ tailWord_146052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146072 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_146072 : Nat := 118140960795 + 146072 * 2 ^ 59
def prefixEnd_146072 : Nat := 4983230072969 + 3 ^ 40 * 146072 * 2
def baseEnd_146072 : Nat := 75005146163657726328233

theorem tailTrace_146072 : CollatzResearch.WordTrace tailWord_146072 prefixEnd_146072 75005146163657726328233 := by
  unfold tailWord_146072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663841763406782978284235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3551789017875710637712313 2663841763406782978284235)
  ·
    refine ⟨3995762645110174467426353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663841763406782978284235 3995762645110174467426353)
    ·
      refine ⟨2996821983832630850569765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3995762645110174467426353 2996821983832630850569765)
      ·
        refine ⟨561904121968618284481831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2996821983832630850569765 561904121968618284481831)
        ·
          refine ⟨842856182952927426722747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561904121968618284481831 842856182952927426722747)
          ·
            refine ⟨1264284274429391140084121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842856182952927426722747 1264284274429391140084121)
            ·
              refine ⟨948213205822043355063091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264284274429391140084121 948213205822043355063091)
              ·
                refine ⟨1422319808733065032594637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948213205822043355063091 1422319808733065032594637)
                ·
                  refine ⟨533369928274899387222989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1422319808733065032594637 533369928274899387222989)
                  ·
                    refine ⟨200013723103087270208621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533369928274899387222989 200013723103087270208621)
                    ·
                      refine ⟨75005146163657726328233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 200013723103087270208621 75005146163657726328233)
                      ·
                        rfl

theorem cell23_146072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_146072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146072 prefixEnd_146072 := by exact prefixLift 146072
  have htrace : WordTrace (prefixWord ++ tailWord_146072) baseStart_146072 baseEnd_146072 := by
    simpa [prefixWord, tailWord_146072, baseEnd_146072] using wordTrace_append hprefix tailTrace_146072
  have hstable : (prefixWord ++ tailWord_146072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146072).length < 2 ^ (prefixWord ++ tailWord_146072).sum := by decide
  have hdescent : baseEnd_146072 < baseStart_146072 := by decide
  rcases family_descends (prefixWord ++ tailWord_146072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146085 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_146085 : Nat := 118140960795 + 146085 * 2 ^ 59
def prefixEnd_146085 : Nat := 4983230072969 + 3 ^ 40 * 146085 * 2
def baseEnd_146085 : Nat := 75011821412166175465673

theorem tailTrace_146085 : CollatzResearch.WordTrace tailWord_146085 prefixEnd_146085 75011821412166175465673 := by
  unfold tailWord_146085
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328157675766469176791709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3552105117177646117861139 5328157675766469176791709)
  ·
    refine ⟨1998059128412425941296891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5328157675766469176791709 1998059128412425941296891)
    ·
      refine ⟨2997088692618638911945337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1998059128412425941296891 2997088692618638911945337)
      ·
        refine ⟨2247816519463979183959003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2997088692618638911945337 2247816519463979183959003)
        ·
          refine ⟨3371724779195968775938505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247816519463979183959003 3371724779195968775938505)
          ·
            refine ⟨2528793584396976581953879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3371724779195968775938505 2528793584396976581953879)
            ·
              refine ⟨3793190376595464872930819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528793584396976581953879 3793190376595464872930819)
              ·
                refine ⟨5689785564893197309396229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793190376595464872930819 5689785564893197309396229)
                ·
                  refine ⟨1066834793417474495511793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5689785564893197309396229 1066834793417474495511793)
                  ·
                    refine ⟨800126095063105871633845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1066834793417474495511793 800126095063105871633845)
                    ·
                      refine ⟨75011821412166175465673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 800126095063105871633845 75011821412166175465673)
                      ·
                        rfl

theorem cell23_146085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_146085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146085 prefixEnd_146085 := by exact prefixLift 146085
  have htrace : WordTrace (prefixWord ++ tailWord_146085) baseStart_146085 baseEnd_146085 := by
    simpa [prefixWord, tailWord_146085, baseEnd_146085] using wordTrace_append hprefix tailTrace_146085
  have hstable : (prefixWord ++ tailWord_146085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146085).length < 2 ^ (prefixWord ++ tailWord_146085).sum := by decide
  have hdescent : baseEnd_146085 < baseStart_146085 := by decide
  rcases family_descends (prefixWord ++ tailWord_146085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146105 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 1, 8]
def baseStart_146105 : Nat := 118140960795 + 146105 * 2 ^ 59
def prefixEnd_146105 : Nat := 4983230072969 + 3 ^ 40 * 146105 * 2
def baseEnd_146105 : Nat := 25007363675085365738527

theorem tailTrace_146105 : CollatzResearch.WordTrace tailWord_146105 prefixEnd_146105 25007363675085365738527 := by
  unfold tailWord_146105
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328887135694012592519769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3552591423796008395013179 5328887135694012592519769)
  ·
    refine ⟨3996665351770509444389827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5328887135694012592519769 3996665351770509444389827)
    ·
      refine ⟨5994998027655764166584741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3996665351770509444389827 5994998027655764166584741)
      ·
        refine ⟨1124062130185455781234639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5994998027655764166584741 1124062130185455781234639)
        ·
          refine ⟨1686093195278183671851959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124062130185455781234639 1686093195278183671851959)
          ·
            refine ⟨2529139792917275507777939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686093195278183671851959 2529139792917275507777939)
            ·
              refine ⟨3793709689375913261666909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529139792917275507777939 3793709689375913261666909)
              ·
                refine ⟨1422641133515967473125091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3793709689375913261666909 1422641133515967473125091)
                ·
                  refine ⟨2133961700273951209687637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422641133515967473125091 2133961700273951209687637)
                  ·
                    refine ⟨25007363675085365738527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2133961700273951209687637 25007363675085365738527)
                    ·
                      rfl

theorem cell23_146105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_146105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146105 prefixEnd_146105 := by exact prefixLift 146105
  have htrace : WordTrace (prefixWord ++ tailWord_146105) baseStart_146105 baseEnd_146105 := by
    simpa [prefixWord, tailWord_146105, baseEnd_146105] using wordTrace_append hprefix tailTrace_146105
  have hstable : (prefixWord ++ tailWord_146105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146105).length < 2 ^ (prefixWord ++ tailWord_146105).sum := by decide
  have hdescent : baseEnd_146105 < baseStart_146105 := by decide
  rcases family_descends (prefixWord ++ tailWord_146105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146116 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_146116 : Nat := 118140960795 + 146116 * 2 ^ 59
def prefixEnd_146116 : Nat := 4983230072969 + 3 ^ 40 * 146116 * 2
def baseEnd_146116 : Nat := 75027739312455554178031

theorem tailTrace_146116 : CollatzResearch.WordTrace tailWord_146116 prefixEnd_146116 75027739312455554178031 := by
  unfold tailWord_146116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664644169327080735585101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3552858892436107647446801 2664644169327080735585101)
  ·
    refine ⟨999241563497655275844413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2664644169327080735585101 999241563497655275844413)
    ·
      refine ⟨374715586311620728441655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 999241563497655275844413 374715586311620728441655)
      ·
        refine ⟨562073379467431092662483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374715586311620728441655 562073379467431092662483)
        ·
          refine ⟨843110069201146638993725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562073379467431092662483 843110069201146638993725)
          ·
            refine ⟨316166275950429989622647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 843110069201146638993725 316166275950429989622647)
            ·
              refine ⟨474249413925644984433971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316166275950429989622647 474249413925644984433971)
              ·
                refine ⟨711374120888467476650957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474249413925644984433971 711374120888467476650957)
                ·
                  refine ⟨266765295333175303744109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711374120888467476650957 266765295333175303744109)
                  ·
                    refine ⟨100036985749940738904041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266765295333175303744109 100036985749940738904041)
                    ·
                      refine ⟨75027739312455554178031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100036985749940738904041 75027739312455554178031)
                      ·
                        rfl

theorem cell23_146116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_146116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146116 prefixEnd_146116 := by exact prefixLift 146116
  have htrace : WordTrace (prefixWord ++ tailWord_146116) baseStart_146116 baseEnd_146116 := by
    simpa [prefixWord, tailWord_146116, baseEnd_146116] using wordTrace_append hprefix tailTrace_146116
  have hstable : (prefixWord ++ tailWord_146116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146116).length < 2 ^ (prefixWord ++ tailWord_146116).sum := by decide
  have hdescent : baseEnd_146116 < baseStart_146116 := by decide
  rcases family_descends (prefixWord ++ tailWord_146116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146129 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 1, 4, 2]
def baseStart_146129 : Nat := 118140960795 + 146129 * 2 ^ 59
def prefixEnd_146129 : Nat := 4983230072969 + 3 ^ 40 * 146129 * 2
def baseEnd_146129 : Nat := 75034414560964003315471

theorem tailTrace_146129 : CollatzResearch.WordTrace tailWord_146129 prefixEnd_146129 75034414560964003315471 := by
  unfold tailWord_146129
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329762487607064691393441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3553174991738043127595627 5329762487607064691393441)
  ·
    refine ⟨3997321865705298518545081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5329762487607064691393441 3997321865705298518545081)
    ·
      refine ⟨2997991399278973888908811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3997321865705298518545081 2997991399278973888908811)
      ·
        refine ⟨4496987098918460833363217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997991399278973888908811 4496987098918460833363217)
        ·
          refine ⟨3372740324188845625022413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4496987098918460833363217 3372740324188845625022413)
          ·
            refine ⟨1264777621570817109383405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3372740324188845625022413 1264777621570817109383405)
            ·
              refine ⟨474291608089056416018777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264777621570817109383405 474291608089056416018777)
              ·
                refine ⟨355718706066792312014083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474291608089056416018777 355718706066792312014083)
                ·
                  refine ⟨533578059100188468021125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355718706066792312014083 533578059100188468021125)
                  ·
                    refine ⟨100045886081285337753961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 533578059100188468021125 100045886081285337753961)
                    ·
                      refine ⟨75034414560964003315471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100045886081285337753961 75034414560964003315471)
                      ·
                        rfl

theorem cell23_146129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_146129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146129 prefixEnd_146129 := by exact prefixLift 146129
  have htrace : WordTrace (prefixWord ++ tailWord_146129) baseStart_146129 baseEnd_146129 := by
    simpa [prefixWord, tailWord_146129, baseEnd_146129] using wordTrace_append hprefix tailTrace_146129
  have hstable : (prefixWord ++ tailWord_146129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146129).length < 2 ^ (prefixWord ++ tailWord_146129).sum := by decide
  have hdescent : baseEnd_146129 < baseStart_146129 := by decide
  rcases family_descends (prefixWord ++ tailWord_146129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146155 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8]
def baseStart_146155 : Nat := 118140960795 + 146155 * 2 ^ 59
def prefixEnd_146155 : Nat := 4983230072969 + 3 ^ 40 * 146155 * 2
def baseEnd_146155 : Nat := 75047765057980901590351

theorem tailTrace_146155 : CollatzResearch.WordTrace tailWord_146155 prefixEnd_146155 75047765057980901590351 := by
  unfold tailWord_146155
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330710785512871131839919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3553807190341914087893279 5330710785512871131839919)
  ·
    refine ⟨7996066178269306697759879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5330710785512871131839919 7996066178269306697759879)
    ·
      refine ⟨11994099267403960046639819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7996066178269306697759879 11994099267403960046639819)
      ·
        refine ⟨17991148901105940069959729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11994099267403960046639819 17991148901105940069959729)
        ·
          refine ⟨13493361675829455052469797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17991148901105940069959729 13493361675829455052469797)
          ·
            refine ⟨2530005314218022822338087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13493361675829455052469797 2530005314218022822338087)
            ·
              refine ⟨3795007971327034233507131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530005314218022822338087 3795007971327034233507131)
              ·
                refine ⟨5692511956990551350260697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795007971327034233507131 5692511956990551350260697)
                ·
                  refine ⟨4269383967742913512695523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692511956990551350260697 4269383967742913512695523)
                  ·
                    refine ⟨6404075951614370269043285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269383967742913512695523 6404075951614370269043285)
                    ·
                      refine ⟨75047765057980901590351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 6404075951614370269043285 75047765057980901590351)
                      ·
                        rfl

theorem cell23_146155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_146155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146155 prefixEnd_146155 := by exact prefixLift 146155
  have htrace : WordTrace (prefixWord ++ tailWord_146155) baseStart_146155 baseEnd_146155 := by
    simpa [prefixWord, tailWord_146155, baseEnd_146155] using wordTrace_append hprefix tailTrace_146155
  have hstable : (prefixWord ++ tailWord_146155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146155).length < 2 ^ (prefixWord ++ tailWord_146155).sum := by decide
  have hdescent : baseEnd_146155 < baseStart_146155 := by decide
  rcases family_descends (prefixWord ++ tailWord_146155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146232 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_146232 : Nat := 118140960795 + 146232 * 2 ^ 59
def prefixEnd_146232 : Nat := 4983230072969 + 3 ^ 40 * 146232 * 2
def baseEnd_146232 : Nat := 75087303068377100327497

theorem tailTrace_146232 : CollatzResearch.WordTrace tailWord_146232 prefixEnd_146232 75087303068377100327497 := by
  unfold tailWord_146232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2666759603116956641196475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3555679470822608854928633 2666759603116956641196475)
  ·
    refine ⟨4000139404675434961794713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2666759603116956641196475 4000139404675434961794713)
    ·
      refine ⟨3000104553506576221346035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4000139404675434961794713 3000104553506576221346035)
      ·
        refine ⟨4500156830259864332019053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000104553506576221346035 4500156830259864332019053)
        ·
          refine ⟨1687558811347449124507145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4500156830259864332019053 1687558811347449124507145)
          ·
            refine ⟨1265669108510586843380359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687558811347449124507145 1265669108510586843380359)
            ·
              refine ⟨1898503662765880265070539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265669108510586843380359 1898503662765880265070539)
              ·
                refine ⟨2847755494148820397605809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898503662765880265070539 2847755494148820397605809)
                ·
                  refine ⟨2135816620611615298204357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2847755494148820397605809 2135816620611615298204357)
                  ·
                    refine ⟨400465616364677868413317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2135816620611615298204357 400465616364677868413317)
                    ·
                      refine ⟨75087303068377100327497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 400465616364677868413317 75087303068377100327497)
                      ·
                        rfl

theorem cell23_146232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_146232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146232 prefixEnd_146232 := by exact prefixLift 146232
  have htrace : WordTrace (prefixWord ++ tailWord_146232) baseStart_146232 baseEnd_146232 := by
    simpa [prefixWord, tailWord_146232, baseEnd_146232] using wordTrace_append hprefix tailTrace_146232
  have hstable : (prefixWord ++ tailWord_146232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146232).length < 2 ^ (prefixWord ++ tailWord_146232).sum := by decide
  have hdescent : baseEnd_146232 < baseStart_146232 := by decide
  rcases family_descends (prefixWord ++ tailWord_146232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146239 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 3]
def baseStart_146239 : Nat := 118140960795 + 146239 * 2 ^ 59
def prefixEnd_146239 : Nat := 4983230072969 + 3 ^ 40 * 146239 * 2
def baseEnd_146239 : Nat := 75090897432958572939965

theorem tailTrace_146239 : CollatzResearch.WordTrace tailWord_146239 prefixEnd_146239 75090897432958572939965 := by
  unfold tailWord_146239
  simp only [CollatzResearch.WordTrace]
  refine ⟨5333774517208553477897771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3555849678139035651931847 5333774517208553477897771)
  ·
    refine ⟨8000661775812830216846657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5333774517208553477897771 8000661775812830216846657)
    ·
      refine ⟨6000496331859622662634993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8000661775812830216846657 6000496331859622662634993)
      ·
        refine ⟨4500372248894716996976245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6000496331859622662634993 4500372248894716996976245)
        ·
          refine ⟨421909898333879718466523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4500372248894716996976245 421909898333879718466523)
          ·
            refine ⟨632864847500819577699785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421909898333879718466523 632864847500819577699785)
            ·
              refine ⟨474648635625614683274839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632864847500819577699785 474648635625614683274839)
              ·
                refine ⟨711972953438422024912259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474648635625614683274839 711972953438422024912259)
                ·
                  refine ⟨1067959430157633037368389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711972953438422024912259 1067959430157633037368389)
                  ·
                    refine ⟨200242393154556194506573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1067959430157633037368389 200242393154556194506573)
                    ·
                      refine ⟨75090897432958572939965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 200242393154556194506573 75090897432958572939965)
                      ·
                        rfl

theorem cell23_146239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_146239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146239 prefixEnd_146239 := by exact prefixLift 146239
  have htrace : WordTrace (prefixWord ++ tailWord_146239) baseStart_146239 baseEnd_146239 := by
    simpa [prefixWord, tailWord_146239, baseEnd_146239] using wordTrace_append hprefix tailTrace_146239
  have hstable : (prefixWord ++ tailWord_146239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146239).length < 2 ^ (prefixWord ++ tailWord_146239).sum := by decide
  have hdescent : baseEnd_146239 < baseStart_146239 := by decide
  rcases family_descends (prefixWord ++ tailWord_146239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146253 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_146253 : Nat := 118140960795 + 146253 * 2 ^ 59
def prefixEnd_146253 : Nat := 4983230072969 + 3 ^ 40 * 146253 * 2
def baseEnd_146253 : Nat := 75098086162121518164901

theorem tailTrace_146253 : CollatzResearch.WordTrace tailWord_146253 prefixEnd_146253 75098086162121518164901 := by
  unfold tailWord_146253
  simp only [CollatzResearch.WordTrace]
  refine ⟨5334285139157833868907413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3556190092771889245938275 5334285139157833868907413)
  ·
    refine ⟨250044615898023462605035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5334285139157833868907413 250044615898023462605035)
    ·
      refine ⟨375066923847035193907553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250044615898023462605035 375066923847035193907553)
      ·
        refine ⟨281300192885276395430665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375066923847035193907553 281300192885276395430665)
        ·
          refine ⟨210975144663957296572999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281300192885276395430665 210975144663957296572999)
          ·
            refine ⟨316462716995935944859499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210975144663957296572999 316462716995935944859499)
            ·
              refine ⟨474694075493903917289249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316462716995935944859499 474694075493903917289249)
              ·
                refine ⟨356020556620427937966937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474694075493903917289249 356020556620427937966937)
                ·
                  refine ⟨267015417465320953475203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356020556620427937966937 267015417465320953475203)
                  ·
                    refine ⟨400523126197981430212805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267015417465320953475203 400523126197981430212805)
                    ·
                      refine ⟨75098086162121518164901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 400523126197981430212805 75098086162121518164901)
                      ·
                        rfl

theorem cell23_146253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_146253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146253 prefixEnd_146253 := by exact prefixLift 146253
  have htrace : WordTrace (prefixWord ++ tailWord_146253) baseStart_146253 baseEnd_146253 := by
    simpa [prefixWord, tailWord_146253, baseEnd_146253] using wordTrace_append hprefix tailTrace_146253
  have hstable : (prefixWord ++ tailWord_146253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146253).length < 2 ^ (prefixWord ++ tailWord_146253).sum := by decide
  have hdescent : baseEnd_146253 < baseStart_146253 := by decide
  rcases family_descends (prefixWord ++ tailWord_146253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146276 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 6]
def baseStart_146276 : Nat := 118140960795 + 146276 * 2 ^ 59
def prefixEnd_146276 : Nat := 4983230072969 + 3 ^ 40 * 146276 * 2
def baseEnd_146276 : Nat := 8345544024130547575255

theorem tailTrace_146276 : CollatzResearch.WordTrace tailWord_146276 prefixEnd_146276 8345544024130547575255 := by
  unfold tailWord_146276
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667562009037254398497341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3556749345383005864663121 2667562009037254398497341)
  ·
    refine ⟨1000335753388970399436503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2667562009037254398497341 1000335753388970399436503)
    ·
      refine ⟨1500503630083455599154755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000335753388970399436503 1500503630083455599154755)
      ·
        refine ⟨2250755445125183398732133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500503630083455599154755 2250755445125183398732133)
        ·
          refine ⟨422016645960971887262275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2250755445125183398732133 422016645960971887262275)
          ·
            refine ⟨633024968941457830893413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422016645960971887262275 633024968941457830893413)
            ·
              refine ⟨118692181676523343292515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 633024968941457830893413 118692181676523343292515)
              ·
                refine ⟨178038272514785014938773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118692181676523343292515 178038272514785014938773)
                ·
                  refine ⟨8345544024130547575255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178038272514785014938773 8345544024130547575255)
                  ·
                    rfl

theorem cell23_146276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_146276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146276 prefixEnd_146276 := by exact prefixLift 146276
  have htrace : WordTrace (prefixWord ++ tailWord_146276) baseStart_146276 baseEnd_146276 := by
    simpa [prefixWord, tailWord_146276, baseEnd_146276] using wordTrace_append hprefix tailTrace_146276
  have hstable : (prefixWord ++ tailWord_146276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146276).length < 2 ^ (prefixWord ++ tailWord_146276).sum := by decide
  have hdescent : baseEnd_146276 < baseStart_146276 := by decide
  rcases family_descends (prefixWord ++ tailWord_146276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146289 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 3, 5]
def baseStart_146289 : Nat := 118140960795 + 146289 * 2 ^ 59
def prefixEnd_146289 : Nat := 4983230072969 + 3 ^ 40 * 146289 * 2
def baseEnd_146289 : Nat := 25038857155227792438245

theorem tailTrace_146289 : CollatzResearch.WordTrace tailWord_146289 prefixEnd_146289 25038857155227792438245 := by
  unfold tailWord_146289
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335598167027412017217921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3557065444684941344811947 5335598167027412017217921)
  ·
    refine ⟨4001698625270559012913441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5335598167027412017217921 4001698625270559012913441)
    ·
      refine ⟨3001273968952919259685081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4001698625270559012913441 3001273968952919259685081)
      ·
        refine ⟨2250955476714689444763811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3001273968952919259685081 2250955476714689444763811)
        ·
          refine ⟨3376433215072034167145717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250955476714689444763811 3376433215072034167145717)
          ·
            refine ⟨316540613913003203169911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3376433215072034167145717 316540613913003203169911)
            ·
              refine ⟨474810920869504804754867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316540613913003203169911 474810920869504804754867)
              ·
                refine ⟨712216381304257207132301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474810920869504804754867 712216381304257207132301)
                ·
                  refine ⟨267081142989096452674613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712216381304257207132301 267081142989096452674613)
                  ·
                    refine ⟨25038857155227792438245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 267081142989096452674613 25038857155227792438245)
                    ·
                      rfl

theorem cell23_146289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_146289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146289 prefixEnd_146289 := by exact prefixLift 146289
  have htrace : WordTrace (prefixWord ++ tailWord_146289) baseStart_146289 baseEnd_146289 := by
    simpa [prefixWord, tailWord_146289, baseEnd_146289] using wordTrace_append hprefix tailTrace_146289
  have hstable : (prefixWord ++ tailWord_146289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146289).length < 2 ^ (prefixWord ++ tailWord_146289).sum := by decide
  have hdescent : baseEnd_146289 < baseStart_146289 := by decide
  rcases family_descends (prefixWord ++ tailWord_146289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146336 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 2, 4]
def baseStart_146336 : Nat := 118140960795 + 146336 * 2 ^ 59
def prefixEnd_146336 : Nat := 4983230072969 + 3 ^ 40 * 146336 * 2
def baseEnd_146336 : Nat := 25046901685481564475673

theorem tailTrace_146336 : CollatzResearch.WordTrace tailWord_146336 prefixEnd_146336 25046901685481564475673 := by
  unfold tailWord_146336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668656198928569522089431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3558208265238092696119241 2668656198928569522089431)
  ·
    refine ⟨4002984298392854283134147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2668656198928569522089431 4002984298392854283134147)
    ·
      refine ⟨6004476447589281424701221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002984298392854283134147 6004476447589281424701221)
      ·
        refine ⟨1125839333922990267131479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6004476447589281424701221 1125839333922990267131479)
        ·
          refine ⟨1688759000884485400697219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125839333922990267131479 1688759000884485400697219)
          ·
            refine ⟨2533138501326728101045829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688759000884485400697219 2533138501326728101045829)
            ·
              refine ⟨474963468998761518946093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2533138501326728101045829 474963468998761518946093)
              ·
                refine ⟨178111300874535569604785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 474963468998761518946093 178111300874535569604785)
                ·
                  refine ⟨133583475655901677203589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178111300874535569604785 133583475655901677203589)
                  ·
                    refine ⟨25046901685481564475673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133583475655901677203589 25046901685481564475673)
                    ·
                      rfl

theorem cell23_146336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_146336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146336 prefixEnd_146336 := by exact prefixLift 146336
  have htrace : WordTrace (prefixWord ++ tailWord_146336) baseStart_146336 baseEnd_146336 := by
    simpa [prefixWord, tailWord_146336, baseEnd_146336] using wordTrace_append hprefix tailTrace_146336
  have hstable : (prefixWord ++ tailWord_146336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146336).length < 2 ^ (prefixWord ++ tailWord_146336).sum := by decide
  have hdescent : baseEnd_146336 < baseStart_146336 := by decide
  rcases family_descends (prefixWord ++ tailWord_146336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146339 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4]
def baseStart_146339 : Nat := 118140960795 + 146339 * 2 ^ 59
def prefixEnd_146339 : Nat := 4983230072969 + 3 ^ 40 * 146339 * 2
def baseEnd_146339 : Nat := 75142245498408181689505

theorem tailTrace_146339 : CollatzResearch.WordTrace tailWord_146339 prefixEnd_146339 75142245498408181689505 := by
  unfold tailWord_146339
  simp only [CollatzResearch.WordTrace]
  refine ⟨5337421816846270556538071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3558281211230847037692047 5337421816846270556538071)
  ·
    refine ⟨8006132725269405834807107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5337421816846270556538071 8006132725269405834807107)
    ·
      refine ⟨12009199087904108752210661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8006132725269405834807107 12009199087904108752210661)
      ·
        refine ⟨2251724828982020391039499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12009199087904108752210661 2251724828982020391039499)
        ·
          refine ⟨3377587243473030586559249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251724828982020391039499 3377587243473030586559249)
          ·
            refine ⟨2533190432604772939919437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377587243473030586559249 2533190432604772939919437)
            ·
              refine ⟨949946412226789852469789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2533190432604772939919437 949946412226789852469789)
              ·
                refine ⟨356229904585046194676171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 949946412226789852469789 356229904585046194676171)
                ·
                  refine ⟨534344856877569292014257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356229904585046194676171 534344856877569292014257)
                  ·
                    refine ⟨400758642658176969010693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 534344856877569292014257 400758642658176969010693)
                    ·
                      refine ⟨75142245498408181689505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 400758642658176969010693 75142245498408181689505)
                      ·
                        rfl

theorem cell23_146339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_146339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146339 prefixEnd_146339 := by exact prefixLift 146339
  have htrace : WordTrace (prefixWord ++ tailWord_146339) baseStart_146339 baseEnd_146339 := by
    simpa [prefixWord, tailWord_146339, baseEnd_146339] using wordTrace_append hprefix tailTrace_146339
  have hstable : (prefixWord ++ tailWord_146339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146339).length < 2 ^ (prefixWord ++ tailWord_146339).sum := by decide
  have hdescent : baseEnd_146339 < baseStart_146339 := by decide
  rcases family_descends (prefixWord ++ tailWord_146339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146360 : List Nat := [2, 1, 2, 1, 2, 4, 1, 5, 1, 2, 2]
def baseStart_146360 : Nat := 118140960795 + 146360 * 2 ^ 59
def prefixEnd_146360 : Nat := 4983230072969 + 3 ^ 40 * 146360 * 2
def baseEnd_146360 : Nat := 75153028592152599526909

theorem tailTrace_146360 : CollatzResearch.WordTrace tailWord_146360 prefixEnd_146360 75153028592152599526909 := by
  unfold tailWord_146360
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669093874885095571526267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3558791833180127428701689 2669093874885095571526267)
  ·
    refine ⟨4003640812327643357289401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2669093874885095571526267 4003640812327643357289401)
    ·
      refine ⟨3002730609245732517967051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4003640812327643357289401 3002730609245732517967051)
      ·
        refine ⟨4504095913868598776950577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3002730609245732517967051 4504095913868598776950577)
        ·
          refine ⟨3378071935401449082712933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4504095913868598776950577 3378071935401449082712933)
          ·
            refine ⟨633388487887771703008675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3378071935401449082712933 633388487887771703008675)
            ·
              refine ⟨950082731831657554513013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633388487887771703008675 950082731831657554513013)
              ·
                refine ⟨89070256109217895735595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 950082731831657554513013 89070256109217895735595)
                ·
                  refine ⟨133605384163826843603393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89070256109217895735595 133605384163826843603393)
                  ·
                    refine ⟨100204038122870132702545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 133605384163826843603393 100204038122870132702545)
                    ·
                      refine ⟨75153028592152599526909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100204038122870132702545 75153028592152599526909)
                      ·
                        rfl

theorem cell23_146360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_146360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146360 prefixEnd_146360 := by exact prefixLift 146360
  have htrace : WordTrace (prefixWord ++ tailWord_146360) baseStart_146360 baseEnd_146360 := by
    simpa [prefixWord, tailWord_146360, baseEnd_146360] using wordTrace_append hprefix tailTrace_146360
  have hstable : (prefixWord ++ tailWord_146360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146360).length < 2 ^ (prefixWord ++ tailWord_146360).sum := by decide
  have hdescent : baseEnd_146360 < baseStart_146360 := by decide
  rcases family_descends (prefixWord ++ tailWord_146360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146390 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_146390 : Nat := 118140960795 + 146390 * 2 ^ 59
def prefixEnd_146390 : Nat := 4983230072969 + 3 ^ 40 * 146390 * 2
def baseEnd_146390 : Nat := 75168433011787482151771

theorem tailTrace_146390 : CollatzResearch.WordTrace tailWord_146390 prefixEnd_146390 75168433011787482151771 := by
  unfold tailWord_146390
  simp only [CollatzResearch.WordTrace]
  refine ⟨333705121228844141665289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3559521293107670844429749 333705121228844141665289)
  ·
    refine ⟨250278840921633106248967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 333705121228844141665289 250278840921633106248967)
    ·
      refine ⟨375418261382449659373451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250278840921633106248967 375418261382449659373451)
      ·
        refine ⟨563127392073674489060177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375418261382449659373451 563127392073674489060177)
        ·
          refine ⟨422345544055255866795133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563127392073674489060177 422345544055255866795133)
          ·
            refine ⟨158379579020720950048175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422345544055255866795133 158379579020720950048175)
            ·
              refine ⟨237569368531081425072263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158379579020720950048175 237569368531081425072263)
              ·
                refine ⟨356354052796622137608395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237569368531081425072263 356354052796622137608395)
                ·
                  refine ⟨534531079194933206412593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356354052796622137608395 534531079194933206412593)
                  ·
                    refine ⟨400898309396199904809445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 534531079194933206412593 400898309396199904809445)
                    ·
                      refine ⟨75168433011787482151771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 400898309396199904809445 75168433011787482151771)
                      ·
                        rfl

theorem cell23_146390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_146390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146390 prefixEnd_146390 := by exact prefixLift 146390
  have htrace : WordTrace (prefixWord ++ tailWord_146390) baseStart_146390 baseEnd_146390 := by
    simpa [prefixWord, tailWord_146390, baseEnd_146390] using wordTrace_append hprefix tailTrace_146390
  have hstable : (prefixWord ++ tailWord_146390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146390).length < 2 ^ (prefixWord ++ tailWord_146390).sum := by decide
  have hdescent : baseEnd_146390 < baseStart_146390 := by decide
  rcases family_descends (prefixWord ++ tailWord_146390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146393 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 3]
def baseStart_146393 : Nat := 118140960795 + 146393 * 2 ^ 59
def prefixEnd_146393 : Nat := 4983230072969 + 3 ^ 40 * 146393 * 2
def baseEnd_146393 : Nat := 75169973453750970414257

theorem tailTrace_146393 : CollatzResearch.WordTrace tailWord_146393 prefixEnd_146393 75169973453750970414257 := by
  unfold tailWord_146393
  simp only [CollatzResearch.WordTrace]
  refine ⟨5339391358650637779003833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3559594239100425186002555 5339391358650637779003833)
  ·
    refine ⟨4004543518987978334252875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5339391358650637779003833 4004543518987978334252875)
    ·
      refine ⟨6006815278481967501379313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4004543518987978334252875 6006815278481967501379313)
      ·
        refine ⟨4505111458861475626034485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6006815278481967501379313 4505111458861475626034485)
        ·
          refine ⟨422354199268263339940733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4505111458861475626034485 422354199268263339940733)
          ·
            refine ⟨158382824725598752477775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422354199268263339940733 158382824725598752477775)
            ·
              refine ⟨237574237088398128716663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158382824725598752477775 237574237088398128716663)
              ·
                refine ⟨356361355632597193074995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237574237088398128716663 356361355632597193074995)
                ·
                  refine ⟨534542033448895789612493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356361355632597193074995 534542033448895789612493)
                  ·
                    refine ⟨200453262543335921104685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 534542033448895789612493 200453262543335921104685)
                    ·
                      refine ⟨75169973453750970414257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 200453262543335921104685 75169973453750970414257)
                      ·
                        rfl

theorem cell23_146393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_146393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146393 prefixEnd_146393 := by exact prefixLift 146393
  have htrace : WordTrace (prefixWord ++ tailWord_146393) baseStart_146393 baseEnd_146393 := by
    simpa [prefixWord, tailWord_146393, baseEnd_146393] using wordTrace_append hprefix tailTrace_146393
  have hstable : (prefixWord ++ tailWord_146393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146393).length < 2 ^ (prefixWord ++ tailWord_146393).sum := by decide
  have hdescent : baseEnd_146393 < baseStart_146393 := by decide
  rcases family_descends (prefixWord ++ tailWord_146393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146416 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 3, 4, 2]
def baseStart_146416 : Nat := 118140960795 + 146416 * 2 ^ 59
def prefixEnd_146416 : Nat := 4983230072969 + 3 ^ 40 * 146416 * 2
def baseEnd_146416 : Nat := 75181783508804380426651

theorem tailTrace_146416 : CollatzResearch.WordTrace tailWord_146416 prefixEnd_146416 75181783508804380426651 := by
  unfold tailWord_146416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670115118783656353545551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3560153491711541804727401 2670115118783656353545551)
  ·
    refine ⟨4005172678175484530318327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2670115118783656353545551 4005172678175484530318327)
    ·
      refine ⟨6007759017263226795477491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4005172678175484530318327 6007759017263226795477491)
      ·
        refine ⟨9011638525894840193216237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007759017263226795477491 9011638525894840193216237)
        ·
          refine ⟨3379364447210565072456089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9011638525894840193216237 3379364447210565072456089)
          ·
            refine ⟨2534523335407923804342067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3379364447210565072456089 2534523335407923804342067)
            ·
              refine ⟨3801785003111885706513101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2534523335407923804342067 3801785003111885706513101)
              ·
                refine ⟨1425669376166957139942413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3801785003111885706513101 1425669376166957139942413)
                ·
                  refine ⟨534626016062608927478405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1425669376166957139942413 534626016062608927478405)
                  ·
                    refine ⟨100242378011739173902201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 534626016062608927478405 100242378011739173902201)
                    ·
                      refine ⟨75181783508804380426651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100242378011739173902201 75181783508804380426651)
                      ·
                        rfl

theorem cell23_146416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 4, 2].length) (baseStart_146416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146416 prefixEnd_146416 := by exact prefixLift 146416
  have htrace : WordTrace (prefixWord ++ tailWord_146416) baseStart_146416 baseEnd_146416 := by
    simpa [prefixWord, tailWord_146416, baseEnd_146416] using wordTrace_append hprefix tailTrace_146416
  have hstable : (prefixWord ++ tailWord_146416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146416).length < 2 ^ (prefixWord ++ tailWord_146416).sum := by decide
  have hdescent : baseEnd_146416 < baseStart_146416 := by decide
  rcases family_descends (prefixWord ++ tailWord_146416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146419 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 3]
def baseStart_146419 : Nat := 118140960795 + 146419 * 2 ^ 59
def prefixEnd_146419 : Nat := 4983230072969 + 3 ^ 40 * 146419 * 2
def baseEnd_146419 : Nat := 75183323950767868689137

theorem tailTrace_146419 : CollatzResearch.WordTrace tailWord_146419 prefixEnd_146419 75183323950767868689137 := by
  unfold tailWord_146419
  simp only [CollatzResearch.WordTrace]
  refine ⟨5340339656556444219450311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3560226437704296146300207 5340339656556444219450311)
  ·
    refine ⟨8010509484834666329175467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5340339656556444219450311 8010509484834666329175467)
    ·
      refine ⟨12015764227251999493763201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8010509484834666329175467 12015764227251999493763201)
      ·
        refine ⟨9011823170438999620322401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12015764227251999493763201 9011823170438999620322401)
        ·
          refine ⟨6758867377829249715241801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9011823170438999620322401 6758867377829249715241801)
          ·
            refine ⟨5069150533371937286431351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6758867377829249715241801 5069150533371937286431351)
            ·
              refine ⟨7603725800057905929647027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069150533371937286431351 7603725800057905929647027)
              ·
                refine ⟨11405588700086858894470541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603725800057905929647027 11405588700086858894470541)
                ·
                  refine ⟨4277095762532572085426453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11405588700086858894470541 4277095762532572085426453)
                  ·
                    refine ⟨200488863868714316504365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4277095762532572085426453 200488863868714316504365)
                    ·
                      refine ⟨75183323950767868689137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 200488863868714316504365 75183323950767868689137)
                      ·
                        rfl

theorem cell23_146419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_146419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146419 prefixEnd_146419 := by exact prefixLift 146419
  have htrace : WordTrace (prefixWord ++ tailWord_146419) baseStart_146419 baseEnd_146419 := by
    simpa [prefixWord, tailWord_146419, baseEnd_146419] using wordTrace_append hprefix tailTrace_146419
  have hstable : (prefixWord ++ tailWord_146419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146419).length < 2 ^ (prefixWord ++ tailWord_146419).sum := by decide
  have hdescent : baseEnd_146419 < baseStart_146419 := by decide
  rcases family_descends (prefixWord ++ tailWord_146419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146484 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_146484 : Nat := 118140960795 + 146484 * 2 ^ 59
def prefixEnd_146484 : Nat := 4983230072969 + 3 ^ 40 * 146484 * 2
def baseEnd_146484 : Nat := 75216700193310114376339

theorem tailTrace_146484 : CollatzResearch.WordTrace tailWord_146484 prefixEnd_146484 75216700193310114376339 := by
  unfold tailWord_146484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671355200660480160283253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3561806934213973547044337 2671355200660480160283253)
  ·
    refine ⟨250439550061920015026555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2671355200660480160283253 250439550061920015026555)
    ·
      refine ⟨375659325092880022539833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250439550061920015026555 375659325092880022539833)
      ·
        refine ⟨281744493819660016904875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375659325092880022539833 281744493819660016904875)
        ·
          refine ⟨422616740729490025357313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281744493819660016904875 422616740729490025357313)
          ·
            refine ⟨316962555547117519017985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422616740729490025357313 316962555547117519017985)
            ·
              refine ⟨237721916660338139263489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316962555547117519017985 237721916660338139263489)
              ·
                refine ⟨178291437495253604447617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237721916660338139263489 178291437495253604447617)
                ·
                  refine ⟨133718578121440203335713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178291437495253604447617 133718578121440203335713)
                  ·
                    refine ⟨100288933591080152501785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 133718578121440203335713 100288933591080152501785)
                    ·
                      refine ⟨75216700193310114376339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100288933591080152501785 75216700193310114376339)
                      ·
                        rfl

theorem cell23_146484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_146484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146484 prefixEnd_146484 := by exact prefixLift 146484
  have htrace : WordTrace (prefixWord ++ tailWord_146484) baseStart_146484 baseEnd_146484 := by
    simpa [prefixWord, tailWord_146484, baseEnd_146484] using wordTrace_append hprefix tailTrace_146484
  have hstable : (prefixWord ++ tailWord_146484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146484).length < 2 ^ (prefixWord ++ tailWord_146484).sum := by decide
  have hdescent : baseEnd_146484 < baseStart_146484 := by decide
  rcases family_descends (prefixWord ++ tailWord_146484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146493 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_146493 : Nat := 118140960795 + 146493 * 2 ^ 59
def prefixEnd_146493 : Nat := 4983230072969 + 3 ^ 40 * 146493 * 2
def baseEnd_146493 : Nat := 75221321519200579163797

theorem tailTrace_146493 : CollatzResearch.WordTrace tailWord_146493 prefixEnd_146493 75221321519200579163797 := by
  unfold tailWord_146493
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343038658288354857644133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3562025772192236571762755 5343038658288354857644133)
  ·
    refine ⟨1001819748429066535808275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5343038658288354857644133 1001819748429066535808275)
    ·
      refine ⟨1502729622643599803712413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1001819748429066535808275 1502729622643599803712413)
      ·
        refine ⟨563523608491349926392155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1502729622643599803712413 563523608491349926392155)
        ·
          refine ⟨845285412737024889588233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563523608491349926392155 845285412737024889588233)
          ·
            refine ⟨633964059552768667191175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 845285412737024889588233 633964059552768667191175)
            ·
              refine ⟨950946089329153000786763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633964059552768667191175 950946089329153000786763)
              ·
                refine ⟨1426419133993729501180145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950946089329153000786763 1426419133993729501180145)
                ·
                  refine ⟨1069814350495297125885109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426419133993729501180145 1069814350495297125885109)
                  ·
                    refine ⟨100295095358934105551729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1069814350495297125885109 100295095358934105551729)
                    ·
                      refine ⟨75221321519200579163797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100295095358934105551729 75221321519200579163797)
                      ·
                        rfl

theorem cell23_146493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_146493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146493 prefixEnd_146493 := by exact prefixLift 146493
  have htrace : WordTrace (prefixWord ++ tailWord_146493) baseStart_146493 baseEnd_146493 := by
    simpa [prefixWord, tailWord_146493, baseEnd_146493] using wordTrace_append hprefix tailTrace_146493
  have hstable : (prefixWord ++ tailWord_146493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146493).length < 2 ^ (prefixWord ++ tailWord_146493).sum := by decide
  have hdescent : baseEnd_146493 < baseStart_146493 := by decide
  rcases family_descends (prefixWord ++ tailWord_146493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146506 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_146506 : Nat := 118140960795 + 146506 * 2 ^ 59
def prefixEnd_146506 : Nat := 4983230072969 + 3 ^ 40 * 146506 * 2
def baseEnd_146506 : Nat := 75227996767709028301237

theorem tailTrace_146506 : CollatzResearch.WordTrace tailWord_146506 prefixEnd_146506 75227996767709028301237 := by
  unfold tailWord_146506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335878201810314519466843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3562341871494172051911581 1335878201810314519466843)
  ·
    refine ⟨2003817302715471779200265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1335878201810314519466843 2003817302715471779200265)
    ·
      refine ⟨1502862977036603834400199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2003817302715471779200265 1502862977036603834400199)
      ·
        refine ⟨2254294465554905751600299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502862977036603834400199 2254294465554905751600299)
        ·
          refine ⟨3381441698332358627400449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254294465554905751600299 3381441698332358627400449)
          ·
            refine ⟨2536081273749268970550337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381441698332358627400449 2536081273749268970550337)
            ·
              refine ⟨1902060955311951727912753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2536081273749268970550337 1902060955311951727912753)
              ·
                refine ⟨1426545716483963795934565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902060955311951727912753 1426545716483963795934565)
                ·
                  refine ⟨267477321840743211737731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1426545716483963795934565 267477321840743211737731)
                  ·
                    refine ⟨401215982761114817606597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267477321840743211737731 401215982761114817606597)
                    ·
                      refine ⟨75227996767709028301237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 401215982761114817606597 75227996767709028301237)
                      ·
                        rfl

theorem cell23_146506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_146506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146506 prefixEnd_146506 := by exact prefixLift 146506
  have htrace : WordTrace (prefixWord ++ tailWord_146506) baseStart_146506 baseEnd_146506 := by
    simpa [prefixWord, tailWord_146506, baseEnd_146506] using wordTrace_append hprefix tailTrace_146506
  have hstable : (prefixWord ++ tailWord_146506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146506).length < 2 ^ (prefixWord ++ tailWord_146506).sum := by decide
  have hdescent : baseEnd_146506 < baseStart_146506 := by decide
  rcases family_descends (prefixWord ++ tailWord_146506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146539 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7]
def baseStart_146539 : Nat := 118140960795 + 146539 * 2 ^ 59
def prefixEnd_146539 : Nat := 4983230072969 + 3 ^ 40 * 146539 * 2
def baseEnd_146539 : Nat := 75244941629307399188585

theorem tailTrace_146539 : CollatzResearch.WordTrace tailWord_146539 prefixEnd_146539 75244941629307399188585 := by
  unfold tailWord_146539
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344716416121704713818671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3563144277414469809212447 5344716416121704713818671)
  ·
    refine ⟨8017074624182557070728007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5344716416121704713818671 8017074624182557070728007)
    ·
      refine ⟨12025611936273835606092011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017074624182557070728007 12025611936273835606092011)
      ·
        refine ⟨18038417904410753409138017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12025611936273835606092011 18038417904410753409138017)
        ·
          refine ⟨13528813428308065056853513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18038417904410753409138017 13528813428308065056853513)
          ·
            refine ⟨10146610071231048792640135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13528813428308065056853513 10146610071231048792640135)
            ·
              refine ⟨15219915106846573188960203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10146610071231048792640135 15219915106846573188960203)
              ·
                refine ⟨22829872660269859783440305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15219915106846573188960203 22829872660269859783440305)
                ·
                  refine ⟨17122404495202394837580229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22829872660269859783440305 17122404495202394837580229)
                  ·
                    refine ⟨3210450842850449032046293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17122404495202394837580229 3210450842850449032046293)
                    ·
                      refine ⟨75244941629307399188585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3210450842850449032046293 75244941629307399188585)
                      ·
                        rfl

theorem cell23_146539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_146539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146539 prefixEnd_146539 := by exact prefixLift 146539
  have htrace : WordTrace (prefixWord ++ tailWord_146539) baseStart_146539 baseEnd_146539 := by
    simpa [prefixWord, tailWord_146539, baseEnd_146539] using wordTrace_append hprefix tailTrace_146539
  have hstable : (prefixWord ++ tailWord_146539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146539).length < 2 ^ (prefixWord ++ tailWord_146539).sum := by decide
  have hdescent : baseEnd_146539 < baseStart_146539 := by decide
  rcases family_descends (prefixWord ++ tailWord_146539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146546 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 8]
def baseStart_146546 : Nat := 118140960795 + 146546 * 2 ^ 59
def prefixEnd_146546 : Nat := 4983230072969 + 3 ^ 40 * 146546 * 2
def baseEnd_146546 : Nat := 8360948443765430200117

theorem tailTrace_146546 : CollatzResearch.WordTrace tailWord_146546 prefixEnd_146546 8360948443765430200117 := by
  unfold tailWord_146546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336242931774086227330873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3563314484730896606215661 1336242931774086227330873)
  ·
    refine ⟨1002182198830564670498155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1336242931774086227330873 1002182198830564670498155)
    ·
      refine ⟨1503273298245847005747233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002182198830564670498155 1503273298245847005747233)
      ·
        refine ⟨1127454973684385254310425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1503273298245847005747233 1127454973684385254310425)
        ·
          refine ⟨845591230263288940732819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127454973684385254310425 845591230263288940732819)
          ·
            refine ⟨1268386845394933411099229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845591230263288940732819 1268386845394933411099229)
            ·
              refine ⟨475645067023100029162211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1268386845394933411099229 475645067023100029162211)
              ·
                refine ⟨713467600534650043743317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475645067023100029162211 713467600534650043743317)
                ·
                  refine ⟨8360948443765430200117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 713467600534650043743317 8360948443765430200117)
                  ·
                    rfl

theorem cell23_146546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_146546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146546 prefixEnd_146546 := by exact prefixLift 146546
  have htrace : WordTrace (prefixWord ++ tailWord_146546) baseStart_146546 baseEnd_146546 := by
    simpa [prefixWord, tailWord_146546, baseEnd_146546] using wordTrace_append hprefix tailTrace_146546
  have hstable : (prefixWord ++ tailWord_146546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146546).length < 2 ^ (prefixWord ++ tailWord_146546).sum := by decide
  have hdescent : baseEnd_146546 < baseStart_146546 := by decide
  rcases family_descends (prefixWord ++ tailWord_146546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146550 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_146550 : Nat := 118140960795 + 146550 * 2 ^ 59
def prefixEnd_146550 : Nat := 4983230072969 + 3 ^ 40 * 146550 * 2
def baseEnd_146550 : Nat := 25083529972168952050345

theorem tailTrace_146550 : CollatzResearch.WordTrace tailWord_146550 prefixEnd_146550 25083529972168952050345 := by
  unfold tailWord_146550
  simp only [CollatzResearch.WordTrace]
  refine ⟨334069851192615849529319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3563411746054569061646069 334069851192615849529319)
  ·
    refine ⟨501104776788923774293979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334069851192615849529319 501104776788923774293979)
    ·
      refine ⟨751657165183385661440969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501104776788923774293979 751657165183385661440969)
      ·
        refine ⟨563742873887539246080727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751657165183385661440969 563742873887539246080727)
        ·
          refine ⟨845614310831308869121091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563742873887539246080727 845614310831308869121091)
          ·
            refine ⟨1268421466246963303681637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845614310831308869121091 1268421466246963303681637)
            ·
              refine ⟨237829024921305619440307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1268421466246963303681637 237829024921305619440307)
              ·
                refine ⟨356743537381958429160461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237829024921305619440307 356743537381958429160461)
                ·
                  refine ⟨133778826518234410935173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356743537381958429160461 133778826518234410935173)
                  ·
                    refine ⟨25083529972168952050345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133778826518234410935173 25083529972168952050345)
                    ·
                      rfl

theorem cell23_146550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_146550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146550 prefixEnd_146550 := by exact prefixLift 146550
  have htrace : WordTrace (prefixWord ++ tailWord_146550) baseStart_146550 baseEnd_146550 := by
    simpa [prefixWord, tailWord_146550, baseEnd_146550] using wordTrace_append hprefix tailTrace_146550
  have hstable : (prefixWord ++ tailWord_146550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146550).length < 2 ^ (prefixWord ++ tailWord_146550).sum := by decide
  have hdescent : baseEnd_146550 < baseStart_146550 := by decide
  rcases family_descends (prefixWord ++ tailWord_146550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146563 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 6]
def baseStart_146563 : Nat := 118140960795 + 146563 * 2 ^ 59
def prefixEnd_146563 : Nat := 4983230072969 + 3 ^ 40 * 146563 * 2
def baseEnd_146563 : Nat := 8361918351668367254275

theorem tailTrace_146563 : CollatzResearch.WordTrace tailWord_146563 prefixEnd_146563 8361918351668367254275 := by
  unfold tailWord_146563
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345591768034756812692343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3563727845356504541794895 5345591768034756812692343)
  ·
    refine ⟨8018387652052135219038515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345591768034756812692343 8018387652052135219038515)
    ·
      refine ⟨12027581478078202828557773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8018387652052135219038515 12027581478078202828557773)
      ·
        refine ⟨4510343054279326060709165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12027581478078202828557773 4510343054279326060709165)
        ·
          refine ⟨1691378645354747272765937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4510343054279326060709165 1691378645354747272765937)
          ·
            refine ⟨1268533984016060454574453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691378645354747272765937 1268533984016060454574453)
            ·
              refine ⟨118925061001505667616355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1268533984016060454574453 118925061001505667616355)
              ·
                refine ⟨178387591502258501424533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118925061001505667616355 178387591502258501424533)
                ·
                  refine ⟨8361918351668367254275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178387591502258501424533 8361918351668367254275)
                  ·
                    rfl

theorem cell23_146563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 6].length) (baseStart_146563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146563 prefixEnd_146563 := by exact prefixLift 146563
  have htrace : WordTrace (prefixWord ++ tailWord_146563) baseStart_146563 baseEnd_146563 := by
    simpa [prefixWord, tailWord_146563, baseEnd_146563] using wordTrace_append hprefix tailTrace_146563
  have hstable : (prefixWord ++ tailWord_146563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146563).length < 2 ^ (prefixWord ++ tailWord_146563).sum := by decide
  have hdescent : baseEnd_146563 < baseStart_146563 := by decide
  rcases family_descends (prefixWord ++ tailWord_146563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146593 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 1, 5]
def baseStart_146593 : Nat := 118140960795 + 146593 * 2 ^ 59
def prefixEnd_146593 : Nat := 4983230072969 + 3 ^ 40 * 146593 * 2
def baseEnd_146593 : Nat := 25090889861550062637779

theorem tailTrace_146593 : CollatzResearch.WordTrace tailWord_146593 prefixEnd_146593 25090889861550062637779 := by
  unfold tailWord_146593
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346685957926071936284433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3564457305284047957522955 5346685957926071936284433)
  ·
    refine ⟨4010014468444553952213325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5346685957926071936284433 4010014468444553952213325)
    ·
      refine ⟨1503755425666707732079997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4010014468444553952213325 1503755425666707732079997)
      ·
        refine ⟨563908284625015399529999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1503755425666707732079997 563908284625015399529999)
        ·
          refine ⟨845862426937523099294999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563908284625015399529999 845862426937523099294999)
          ·
            refine ⟨1268793640406284648942499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845862426937523099294999 1268793640406284648942499)
            ·
              refine ⟨1903190460609426973413749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268793640406284648942499 1903190460609426973413749)
              ·
                refine ⟨178424105682133778757539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1903190460609426973413749 178424105682133778757539)
                ·
                  refine ⟨267636158523200668136309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178424105682133778757539 267636158523200668136309)
                  ·
                    refine ⟨25090889861550062637779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 267636158523200668136309 25090889861550062637779)
                    ·
                      rfl

theorem cell23_146593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_146593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146593 prefixEnd_146593 := by exact prefixLift 146593
  have htrace : WordTrace (prefixWord ++ tailWord_146593) baseStart_146593 baseEnd_146593 := by
    simpa [prefixWord, tailWord_146593, baseEnd_146593] using wordTrace_append hprefix tailTrace_146593
  have hstable : (prefixWord ++ tailWord_146593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146593).length < 2 ^ (prefixWord ++ tailWord_146593).sum := by decide
  have hdescent : baseEnd_146593 < baseStart_146593 := by decide
  rcases family_descends (prefixWord ++ tailWord_146593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146616 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_146616 : Nat := 118140960795 + 146616 * 2 ^ 59
def prefixEnd_146616 : Nat := 4983230072969 + 3 ^ 40 * 146616 * 2
def baseEnd_146616 : Nat := 75284479639703597925731

theorem tailTrace_146616 : CollatzResearch.WordTrace tailWord_146616 prefixEnd_146616 75284479639703597925731 := by
  unfold tailWord_146616
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673762418421373432185851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3565016557895164576247801 2673762418421373432185851)
  ·
    refine ⟨4010643627632060148278777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2673762418421373432185851 4010643627632060148278777)
    ·
      refine ⟨3007982720724045111209083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4010643627632060148278777 3007982720724045111209083)
      ·
        refine ⟨4511974081086067666813625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007982720724045111209083 4511974081086067666813625)
        ·
          refine ⟨3383980560814550750110219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4511974081086067666813625 3383980560814550750110219)
          ·
            refine ⟨5075970841221826125165329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383980560814550750110219 5075970841221826125165329)
            ·
              refine ⟨3806978130916369593873997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075970841221826125165329 3806978130916369593873997)
              ·
                refine ⟨1427616799093638597702749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3806978130916369593873997 1427616799093638597702749)
                ·
                  refine ⟨535356299660114474138531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1427616799093638597702749 535356299660114474138531)
                  ·
                    refine ⟨803034449490171711207797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535356299660114474138531 803034449490171711207797)
                    ·
                      refine ⟨75284479639703597925731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 803034449490171711207797 75284479639703597925731)
                      ·
                        rfl

theorem cell23_146616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_146616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146616 prefixEnd_146616 := by exact prefixLift 146616
  have htrace : WordTrace (prefixWord ++ tailWord_146616) baseStart_146616 baseEnd_146616 := by
    simpa [prefixWord, tailWord_146616, baseEnd_146616] using wordTrace_append hprefix tailTrace_146616
  have hstable : (prefixWord ++ tailWord_146616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146616).length < 2 ^ (prefixWord ++ tailWord_146616).sum := by decide
  have hdescent : baseEnd_146616 < baseStart_146616 := by decide
  rcases family_descends (prefixWord ++ tailWord_146616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146644 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_146644 : Nat := 118140960795 + 146644 * 2 ^ 59
def prefixEnd_146644 : Nat := 4983230072969 + 3 ^ 40 * 146644 * 2
def baseEnd_146644 : Nat := 25099619032676496125201

theorem tailTrace_146644 : CollatzResearch.WordTrace tailWord_146644 prefixEnd_146644 25099619032676496125201 := by
  unfold tailWord_146644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674273040370653823195493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3565697387160871764260657 2674273040370653823195493)
  ·
    refine ⟨501426195069497591849155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2674273040370653823195493 501426195069497591849155)
    ·
      refine ⟨752139292604246387773733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501426195069497591849155 752139292604246387773733)
      ·
        refine ⟨141026117363296197707575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 752139292604246387773733 141026117363296197707575)
        ·
          refine ⟨211539176044944296561363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141026117363296197707575 211539176044944296561363)
          ·
            refine ⟨317308764067416444842045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211539176044944296561363 317308764067416444842045)
            ·
              refine ⟨118990786525281166815767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317308764067416444842045 118990786525281166815767)
              ·
                refine ⟨178486179787921750223651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118990786525281166815767 178486179787921750223651)
                ·
                  refine ⟨267729269681882625335477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178486179787921750223651 267729269681882625335477)
                  ·
                    refine ⟨25099619032676496125201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 267729269681882625335477 25099619032676496125201)
                    ·
                      rfl

theorem cell23_146644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_146644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146644 prefixEnd_146644 := by exact prefixLift 146644
  have htrace : WordTrace (prefixWord ++ tailWord_146644) baseStart_146644 baseEnd_146644 := by
    simpa [prefixWord, tailWord_146644, baseEnd_146644] using wordTrace_append hprefix tailTrace_146644
  have hstable : (prefixWord ++ tailWord_146644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146644).length < 2 ^ (prefixWord ++ tailWord_146644).sum := by decide
  have hdescent : baseEnd_146644 < baseStart_146644 := by decide
  rcases family_descends (prefixWord ++ tailWord_146644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146653 : List Nat := [1, 4, 3, 2, 2, 11]
def baseStart_146653 : Nat := 118140960795 + 146653 * 2 ^ 59
def prefixEnd_146653 : Nat := 4983230072969 + 3 ^ 40 * 146653 * 2
def baseEnd_146653 : Nat := 309890857711604745527

theorem tailTrace_146653 : CollatzResearch.WordTrace tailWord_146653 prefixEnd_146653 309890857711604745527 := by
  unfold tailWord_146653
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348874337708702183468613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3565916225139134788979075 5348874337708702183468613)
  ·
    refine ⟨1002913938320381659400365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5348874337708702183468613 1002913938320381659400365)
    ·
      refine ⟨376092726870143122275137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1002913938320381659400365 376092726870143122275137)
      ·
        refine ⟨282069545152607341706353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376092726870143122275137 282069545152607341706353)
        ·
          refine ⟨211552158864455506279765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282069545152607341706353 211552158864455506279765)
          ·
            refine ⟨309890857711604745527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 211552158864455506279765 309890857711604745527)
            ·
              rfl

theorem cell23_146653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 11].length) (baseStart_146653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146653 prefixEnd_146653 := by exact prefixLift 146653
  have htrace : WordTrace (prefixWord ++ tailWord_146653) baseStart_146653 baseEnd_146653 := by
    simpa [prefixWord, tailWord_146653, baseEnd_146653] using wordTrace_append hprefix tailTrace_146653
  have hstable : (prefixWord ++ tailWord_146653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146653).length < 2 ^ (prefixWord ++ tailWord_146653).sum := by decide
  have hdescent : baseEnd_146653 < baseStart_146653 := by decide
  rcases family_descends (prefixWord ++ tailWord_146653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146664 : List Nat := [2, 1, 4, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_146664 : Nat := 118140960795 + 146664 * 2 ^ 59
def prefixEnd_146664 : Nat := 4983230072969 + 3 ^ 40 * 146664 * 2
def baseEnd_146664 : Nat := 75309126711119410125511

theorem tailTrace_146664 : CollatzResearch.WordTrace tailWord_146664 prefixEnd_146664 75309126711119410125511 := by
  unfold tailWord_146664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674637770334425531059523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3566183693779234041412697 2674637770334425531059523)
  ·
    refine ⟨4011956655501638296589285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2674637770334425531059523 4011956655501638296589285)
    ·
      refine ⟨752241872906557180610491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4011956655501638296589285 752241872906557180610491)
      ·
        refine ⟨1128362809359835770915737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752241872906557180610491 1128362809359835770915737)
        ·
          refine ⟨846272107019876828186803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1128362809359835770915737 846272107019876828186803)
          ·
            refine ⟨1269408160529815242280205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846272107019876828186803 1269408160529815242280205)
            ·
              refine ⟨476028060198680715855077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1269408160529815242280205 476028060198680715855077)
              ·
                refine ⟨89255261287252634222827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476028060198680715855077 89255261287252634222827)
                ·
                  refine ⟨133882891930878951334241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89255261287252634222827 133882891930878951334241)
                  ·
                    refine ⟨100412168948159213500681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 133882891930878951334241 100412168948159213500681)
                    ·
                      refine ⟨75309126711119410125511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100412168948159213500681 75309126711119410125511)
                      ·
                        rfl

theorem cell23_146664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_146664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146664 prefixEnd_146664 := by exact prefixLift 146664
  have htrace : WordTrace (prefixWord ++ tailWord_146664) baseStart_146664 baseEnd_146664 := by
    simpa [prefixWord, tailWord_146664, baseEnd_146664] using wordTrace_append hprefix tailTrace_146664
  have hstable : (prefixWord ++ tailWord_146664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146664).length < 2 ^ (prefixWord ++ tailWord_146664).sum := by decide
  have hdescent : baseEnd_146664 < baseStart_146664 := by decide
  rcases family_descends (prefixWord ++ tailWord_146664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146714 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_146714 : Nat := 118140960795 + 146714 * 2 ^ 59
def prefixEnd_146714 : Nat := 4983230072969 + 3 ^ 40 * 146714 * 2
def baseEnd_146714 : Nat := 75334800743844214500281

theorem tailTrace_146714 : CollatzResearch.WordTrace tailWord_146714 prefixEnd_146714 75334800743844214500281 := by
  unfold tailWord_146714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337774797621927400359799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3567399460325139734292797 1337774797621927400359799)
  ·
    refine ⟨2006662196432891100539699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337774797621927400359799 2006662196432891100539699)
    ·
      refine ⟨3009993294649336650809549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006662196432891100539699 3009993294649336650809549)
      ·
        refine ⟨1128747485493501244053581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3009993294649336650809549 1128747485493501244053581)
        ·
          refine ⟨423280307060062966520093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1128747485493501244053581 423280307060062966520093)
          ·
            refine ⟨158730115147523612445035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423280307060062966520093 158730115147523612445035)
            ·
              refine ⟨238095172721285418667553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158730115147523612445035 238095172721285418667553)
              ·
                refine ⟨178571379540964064000665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238095172721285418667553 178571379540964064000665)
                ·
                  refine ⟨133928534655723048000499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178571379540964064000665 133928534655723048000499)
                  ·
                    refine ⟨200892801983584572000749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133928534655723048000499 200892801983584572000749)
                    ·
                      refine ⟨75334800743844214500281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 200892801983584572000749 75334800743844214500281)
                      ·
                        rfl

theorem cell23_146714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_146714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146714 prefixEnd_146714 := by exact prefixLift 146714
  have htrace : WordTrace (prefixWord ++ tailWord_146714) baseStart_146714 baseEnd_146714 := by
    simpa [prefixWord, tailWord_146714, baseEnd_146714] using wordTrace_append hprefix tailTrace_146714
  have hstable : (prefixWord ++ tailWord_146714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146714).length < 2 ^ (prefixWord ++ tailWord_146714).sum := by decide
  have hdescent : baseEnd_146714 < baseStart_146714 := by decide
  rcases family_descends (prefixWord ++ tailWord_146714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146730 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_146730 : Nat := 118140960795 + 146730 * 2 ^ 59
def prefixEnd_146730 : Nat := 4983230072969 + 3 ^ 40 * 146730 * 2
def baseEnd_146730 : Nat := 25114338811438717300069

theorem tailTrace_146730 : CollatzResearch.WordTrace tailWord_146730 prefixEnd_146730 25114338811438717300069 := by
  unfold tailWord_146730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337920689607436083505411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3567788505619829556014429 1337920689607436083505411)
  ·
    refine ⟨2006881034411154125258117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337920689607436083505411 2006881034411154125258117)
    ·
      refine ⟨376290193952091398485897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2006881034411154125258117 376290193952091398485897)
      ·
        refine ⟨282217645464068548864423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376290193952091398485897 282217645464068548864423)
        ·
          refine ⟨423326468196102823296635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282217645464068548864423 423326468196102823296635)
          ·
            refine ⟨634989702294154234944953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423326468196102823296635 634989702294154234944953)
            ·
              refine ⟨476242276720615676208715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634989702294154234944953 476242276720615676208715)
              ·
                refine ⟨714363415080923514313073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476242276720615676208715 714363415080923514313073)
                ·
                  refine ⟨535772561310692635734805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714363415080923514313073 535772561310692635734805)
                  ·
                    refine ⟨25114338811438717300069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 535772561310692635734805 25114338811438717300069)
                    ·
                      rfl

theorem cell23_146730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_146730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146730 prefixEnd_146730 := by exact prefixLift 146730
  have htrace : WordTrace (prefixWord ++ tailWord_146730) baseStart_146730 baseEnd_146730 := by
    simpa [prefixWord, tailWord_146730, baseEnd_146730] using wordTrace_append hprefix tailTrace_146730
  have hstable : (prefixWord ++ tailWord_146730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146730).length < 2 ^ (prefixWord ++ tailWord_146730).sum := by decide
  have hdescent : baseEnd_146730 < baseStart_146730 := by decide
  rcases family_descends (prefixWord ++ tailWord_146730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146737 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 1, 4, 2]
def baseStart_146737 : Nat := 118140960795 + 146737 * 2 ^ 59
def prefixEnd_146737 : Nat := 4983230072969 + 3 ^ 40 * 146737 * 2
def baseEnd_146737 : Nat := 75346610798897624512675

theorem tailTrace_146737 : CollatzResearch.WordTrace tailWord_146737 prefixEnd_146737 75346610798897624512675 := by
  unfold tailWord_146737
  simp only [CollatzResearch.WordTrace]
  refine ⟨5351938069404384529526465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3567958712936256353017643 5351938069404384529526465)
  ·
    refine ⟨4013953552053288397144849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5351938069404384529526465 4013953552053288397144849)
    ·
      refine ⟨3010465164039966297858637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4013953552053288397144849 3010465164039966297858637)
      ·
        refine ⟨1128924436514987361696989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3010465164039966297858637 1128924436514987361696989)
        ·
          refine ⟨423346663693120260636371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1128924436514987361696989 423346663693120260636371)
          ·
            refine ⟨635019995539680390954557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423346663693120260636371 635019995539680390954557)
            ·
              refine ⟨238132498327380146607959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 635019995539680390954557 238132498327380146607959)
              ·
                refine ⟨357198747491070219911939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238132498327380146607959 357198747491070219911939)
                ·
                  refine ⟨535798121236605329867909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357198747491070219911939 535798121236605329867909)
                  ·
                    refine ⟨100462147731863499350233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 535798121236605329867909 100462147731863499350233)
                    ·
                      refine ⟨75346610798897624512675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100462147731863499350233 75346610798897624512675)
                      ·
                        rfl

theorem cell23_146737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_146737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146737 prefixEnd_146737 := by exact prefixLift 146737
  have htrace : WordTrace (prefixWord ++ tailWord_146737) baseStart_146737 baseEnd_146737 := by
    simpa [prefixWord, tailWord_146737, baseEnd_146737] using wordTrace_append hprefix tailTrace_146737
  have hstable : (prefixWord ++ tailWord_146737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146737).length < 2 ^ (prefixWord ++ tailWord_146737).sum := by decide
  have hdescent : baseEnd_146737 < baseStart_146737 := by decide
  rcases family_descends (prefixWord ++ tailWord_146737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146740 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_146740 : Nat := 118140960795 + 146740 * 2 ^ 59
def prefixEnd_146740 : Nat := 4983230072969 + 3 ^ 40 * 146740 * 2
def baseEnd_146740 : Nat := 75348151240861112775161

theorem tailTrace_146740 : CollatzResearch.WordTrace tailWord_146740 prefixEnd_146740 75348151240861112775161 := by
  unfold tailWord_146740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676023744196758020942837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3568031658929010694590449 2676023744196758020942837)
  ·
    refine ⟨250877226018446064463391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2676023744196758020942837 250877226018446064463391)
    ·
      refine ⟨376315839027669096695087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250877226018446064463391 376315839027669096695087)
      ·
        refine ⟨564473758541503645042631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376315839027669096695087 564473758541503645042631)
        ·
          refine ⟨846710637812255467563947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564473758541503645042631 846710637812255467563947)
          ·
            refine ⟨1270065956718383201345921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846710637812255467563947 1270065956718383201345921)
            ·
              refine ⟨952549467538787401009441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270065956718383201345921 952549467538787401009441)
              ·
                refine ⟨714412100654090550757081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952549467538787401009441 714412100654090550757081)
                ·
                  refine ⟨535809075490567913067811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714412100654090550757081 535809075490567913067811)
                  ·
                    refine ⟨803713613235851869601717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535809075490567913067811 803713613235851869601717)
                    ·
                      refine ⟨75348151240861112775161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 803713613235851869601717 75348151240861112775161)
                      ·
                        rfl

theorem cell23_146740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_146740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146740 prefixEnd_146740 := by exact prefixLift 146740
  have htrace : WordTrace (prefixWord ++ tailWord_146740) baseStart_146740 baseEnd_146740 := by
    simpa [prefixWord, tailWord_146740, baseEnd_146740] using wordTrace_append hprefix tailTrace_146740
  have hstable : (prefixWord ++ tailWord_146740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146740).length < 2 ^ (prefixWord ++ tailWord_146740).sum := by decide
  have hdescent : baseEnd_146740 < baseStart_146740 := by decide
  rcases family_descends (prefixWord ++ tailWord_146740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146793 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_146793 : Nat := 118140960795 + 146793 * 2 ^ 59
def prefixEnd_146793 : Nat := 4983230072969 + 3 ^ 40 * 146793 * 2
def baseEnd_146793 : Nat := 75375365715549405412417

theorem tailTrace_146793 : CollatzResearch.WordTrace tailWord_146793 prefixEnd_146793 75375365715549405412417 := by
  unfold tailWord_146793
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353980557201506093565033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3569320371467670729043355 5353980557201506093565033)
  ·
    refine ⟨4015485417901129570173775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5353980557201506093565033 4015485417901129570173775)
    ·
      refine ⟨6023228126851694355260663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015485417901129570173775 6023228126851694355260663)
      ·
        refine ⟨9034842190277541532890995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6023228126851694355260663 9034842190277541532890995)
        ·
          refine ⟨13552263285416312299336493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9034842190277541532890995 13552263285416312299336493)
          ·
            refine ⟨5082098732031117112251185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13552263285416312299336493 5082098732031117112251185)
            ·
              refine ⟨3811574049023337834188389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5082098732031117112251185 3811574049023337834188389)
              ·
                refine ⟨714670134191875843910323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3811574049023337834188389 714670134191875843910323)
                ·
                  refine ⟨1072005201287813765865485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714670134191875843910323 1072005201287813765865485)
                  ·
                    refine ⟨402001950482930162199557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072005201287813765865485 402001950482930162199557)
                    ·
                      refine ⟨75375365715549405412417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 402001950482930162199557 75375365715549405412417)
                      ·
                        rfl

theorem cell23_146793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_146793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146793 prefixEnd_146793 := by exact prefixLift 146793
  have htrace : WordTrace (prefixWord ++ tailWord_146793) baseStart_146793 baseEnd_146793 := by
    simpa [prefixWord, tailWord_146793, baseEnd_146793] using wordTrace_append hprefix tailTrace_146793
  have hstable : (prefixWord ++ tailWord_146793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146793).length < 2 ^ (prefixWord ++ tailWord_146793).sum := by decide
  have hdescent : baseEnd_146793 < baseStart_146793 := by decide
  rcases family_descends (prefixWord ++ tailWord_146793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146810 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2]
def baseStart_146810 : Nat := 118140960795 + 146810 * 2 ^ 59
def prefixEnd_146810 : Nat := 4983230072969 + 3 ^ 40 * 146810 * 2
def baseEnd_146810 : Nat := 75384094886675838899839

theorem tailTrace_146810 : CollatzResearch.WordTrace tailWord_146810 prefixEnd_146810 75384094886675838899839 := by
  unfold tailWord_146810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338650149534979499233471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3569733732093278664622589 1338650149534979499233471)
  ·
    refine ⟨2007975224302469248850207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1338650149534979499233471 2007975224302469248850207)
    ·
      refine ⟨3011962836453703873275311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2007975224302469248850207 3011962836453703873275311)
      ·
        refine ⟨4517944254680555809912967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011962836453703873275311 4517944254680555809912967)
        ·
          refine ⟨6776916382020833714869451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517944254680555809912967 6776916382020833714869451)
          ·
            refine ⟨10165374573031250572304177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6776916382020833714869451 10165374573031250572304177)
            ·
              refine ⟨7624030929773437929228133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10165374573031250572304177 7624030929773437929228133)
              ·
                refine ⟨1429505799332519611730275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7624030929773437929228133 1429505799332519611730275)
                ·
                  refine ⟨2144258698998779417595413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429505799332519611730275 2144258698998779417595413)
                  ·
                    refine ⟨100512126515567785199785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2144258698998779417595413 100512126515567785199785)
                    ·
                      refine ⟨75384094886675838899839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100512126515567785199785 75384094886675838899839)
                      ·
                        rfl

theorem cell23_146810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_146810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146810 prefixEnd_146810 := by exact prefixLift 146810
  have htrace : WordTrace (prefixWord ++ tailWord_146810) baseStart_146810 baseEnd_146810 := by
    simpa [prefixWord, tailWord_146810, baseEnd_146810] using wordTrace_append hprefix tailTrace_146810
  have hstable : (prefixWord ++ tailWord_146810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146810).length < 2 ^ (prefixWord ++ tailWord_146810).sum := by decide
  have hdescent : baseEnd_146810 < baseStart_146810 := by decide
  rcases family_descends (prefixWord ++ tailWord_146810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146853 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_146853 : Nat := 118140960795 + 146853 * 2 ^ 59
def prefixEnd_146853 : Nat := 4983230072969 + 3 ^ 40 * 146853 * 2
def baseEnd_146853 : Nat := 75406174554819170662141

theorem tailTrace_146853 : CollatzResearch.WordTrace tailWord_146853 prefixEnd_146853 75406174554819170662141 := by
  unfold tailWord_146853
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356168936984136340749213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3570779291322757560499475 5356168936984136340749213)
  ·
    refine ⟨2008563351369051127780955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5356168936984136340749213 2008563351369051127780955)
    ·
      refine ⟨3012845027053576691671433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008563351369051127780955 3012845027053576691671433)
      ·
        refine ⟨2259633770290182518753575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3012845027053576691671433 2259633770290182518753575)
        ·
          refine ⟨3389450655435273778130363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259633770290182518753575 3389450655435273778130363)
          ·
            refine ⟨5084175983152910667195545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389450655435273778130363 5084175983152910667195545)
            ·
              refine ⟨3813131987364683000396659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5084175983152910667195545 3813131987364683000396659)
              ·
                refine ⟨5719697981047024500594989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3813131987364683000396659 5719697981047024500594989)
                ·
                  refine ⟨2144886742892634187723121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5719697981047024500594989 2144886742892634187723121)
                  ·
                    refine ⟨1608665057169475640792341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144886742892634187723121 1608665057169475640792341)
                    ·
                      refine ⟨75406174554819170662141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1608665057169475640792341 75406174554819170662141)
                      ·
                        rfl

theorem cell23_146853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_146853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146853 prefixEnd_146853 := by exact prefixLift 146853
  have htrace : WordTrace (prefixWord ++ tailWord_146853) baseStart_146853 baseEnd_146853 := by
    simpa [prefixWord, tailWord_146853, baseEnd_146853] using wordTrace_append hprefix tailTrace_146853
  have hstable : (prefixWord ++ tailWord_146853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146853).length < 2 ^ (prefixWord ++ tailWord_146853).sum := by decide
  have hdescent : baseEnd_146853 < baseStart_146853 := by decide
  rcases family_descends (prefixWord ++ tailWord_146853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146877 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_146877 : Nat := 118140960795 + 146877 * 2 ^ 59
def prefixEnd_146877 : Nat := 4983230072969 + 3 ^ 40 * 146877 * 2
def baseEnd_146877 : Nat := 75418498090527076762031

theorem tailTrace_146877 : CollatzResearch.WordTrace tailWord_146877 prefixEnd_146877 75418498090527076762031 := by
  unfold tailWord_146877
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357044288897188439622885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3571362859264792293081923 5357044288897188439622885)
  ·
    refine ⟨1004445804168222832429291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5357044288897188439622885 1004445804168222832429291)
    ·
      refine ⟨1506668706252334248643937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004445804168222832429291 1506668706252334248643937)
      ·
        refine ⟨1130001529689250686482953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1506668706252334248643937 1130001529689250686482953)
        ·
          refine ⟨847501147266938014862215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130001529689250686482953 847501147266938014862215)
          ·
            refine ⟨1271251720900407022293323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847501147266938014862215 1271251720900407022293323)
            ·
              refine ⟨1906877581350610533439985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271251720900407022293323 1906877581350610533439985)
              ·
                refine ⟨1430158186012957900079989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906877581350610533439985 1430158186012957900079989)
                ·
                  refine ⟨134077329938714803132499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1430158186012957900079989 134077329938714803132499)
                  ·
                    refine ⟨201115994908072204698749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134077329938714803132499 201115994908072204698749)
                    ·
                      refine ⟨75418498090527076762031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 201115994908072204698749 75418498090527076762031)
                      ·
                        rfl

theorem cell23_146877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_146877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146877 prefixEnd_146877 := by exact prefixLift 146877
  have htrace : WordTrace (prefixWord ++ tailWord_146877) baseStart_146877 baseEnd_146877 := by
    simpa [prefixWord, tailWord_146877, baseEnd_146877] using wordTrace_append hprefix tailTrace_146877
  have hstable : (prefixWord ++ tailWord_146877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146877).length < 2 ^ (prefixWord ++ tailWord_146877).sum := by decide
  have hdescent : baseEnd_146877 < baseStart_146877 := by decide
  rcases family_descends (prefixWord ++ tailWord_146877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146884 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 6]
def baseStart_146884 : Nat := 118140960795 + 146884 * 2 ^ 59
def prefixEnd_146884 : Nat := 4983230072969 + 3 ^ 40 * 146884 * 2
def baseEnd_146884 : Nat := 8380232495012061041611

theorem tailTrace_146884 : CollatzResearch.WordTrace tailWord_146884 prefixEnd_146884 8380232495012061041611 := by
  unfold tailWord_146884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678649799935914317563853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3571533066581219090085137 2678649799935914317563853)
  ·
    refine ⟨1004493674975967869086445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2678649799935914317563853 1004493674975967869086445)
    ·
      refine ⟨376685128115987950907417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1004493674975967869086445 376685128115987950907417)
      ·
        refine ⟨282513846086990963180563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376685128115987950907417 282513846086990963180563)
        ·
          refine ⟨423770769130486444770845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282513846086990963180563 423770769130486444770845)
          ·
            refine ⟨158914038423932416789067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423770769130486444770845 158914038423932416789067)
            ·
              refine ⟨238371057635898625183601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158914038423932416789067 238371057635898625183601)
              ·
                refine ⟨178778293226923968887701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238371057635898625183601 178778293226923968887701)
                ·
                  refine ⟨8380232495012061041611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178778293226923968887701 8380232495012061041611)
                  ·
                    rfl

theorem cell23_146884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_146884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146884 prefixEnd_146884 := by exact prefixLift 146884
  have htrace : WordTrace (prefixWord ++ tailWord_146884) baseStart_146884 baseEnd_146884 := by
    simpa [prefixWord, tailWord_146884, baseEnd_146884] using wordTrace_append hprefix tailTrace_146884
  have hstable : (prefixWord ++ tailWord_146884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146884).length < 2 ^ (prefixWord ++ tailWord_146884).sum := by decide
  have hdescent : baseEnd_146884 < baseStart_146884 := by decide
  rcases family_descends (prefixWord ++ tailWord_146884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146887 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_146887 : Nat := 118140960795 + 146887 * 2 ^ 59
def prefixEnd_146887 : Nat := 4983230072969 + 3 ^ 40 * 146887 * 2
def baseEnd_146887 : Nat := 75423632897072037636985

theorem tailTrace_146887 : CollatzResearch.WordTrace tailWord_146887 prefixEnd_146887 75423632897072037636985 := by
  unfold tailWord_146887
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357409018860960147486915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3571606012573973431657943 5357409018860960147486915)
  ·
    refine ⟨8036113528291440221230373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5357409018860960147486915 8036113528291440221230373)
    ·
      refine ⟨1506771286554645041480695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8036113528291440221230373 1506771286554645041480695)
      ·
        refine ⟨2260156929831967562221043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506771286554645041480695 2260156929831967562221043)
        ·
          refine ⟨3390235394747951343331565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260156929831967562221043 3390235394747951343331565)
          ·
            refine ⟨1271338273030481753749337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3390235394747951343331565 1271338273030481753749337)
            ·
              refine ⟨953503704772861315312003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271338273030481753749337 953503704772861315312003)
              ·
                refine ⟨1430255557159291972968005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953503704772861315312003 1430255557159291972968005)
                ·
                  refine ⟨268172916967367244931501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430255557159291972968005 268172916967367244931501)
                  ·
                    refine ⟨100564843862762716849313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268172916967367244931501 100564843862762716849313)
                    ·
                      refine ⟨75423632897072037636985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100564843862762716849313 75423632897072037636985)
                      ·
                        rfl

theorem cell23_146887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_146887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146887 prefixEnd_146887 := by exact prefixLift 146887
  have htrace : WordTrace (prefixWord ++ tailWord_146887) baseStart_146887 baseEnd_146887 := by
    simpa [prefixWord, tailWord_146887, baseEnd_146887] using wordTrace_append hprefix tailTrace_146887
  have hstable : (prefixWord ++ tailWord_146887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146887).length < 2 ^ (prefixWord ++ tailWord_146887).sum := by decide
  have hdescent : baseEnd_146887 < baseStart_146887 := by decide
  rcases family_descends (prefixWord ++ tailWord_146887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146920 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_146920 : Nat := 118140960795 + 146920 * 2 ^ 59
def prefixEnd_146920 : Nat := 4983230072969 + 3 ^ 40 * 146920 * 2
def baseEnd_146920 : Nat := 75440577758670408524333

theorem tailTrace_146920 : CollatzResearch.WordTrace tailWord_146920 prefixEnd_146920 75440577758670408524333 := by
  unfold tailWord_146920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679306313870703391719107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3572408418494271188958809 2679306313870703391719107)
  ·
    refine ⟨4018959470806055087578661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679306313870703391719107 4018959470806055087578661)
    ·
      refine ⟨753554900776135328920999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4018959470806055087578661 753554900776135328920999)
      ·
        refine ⟨1130332351164202993381499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753554900776135328920999 1130332351164202993381499)
        ·
          refine ⟨1695498526746304490072249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130332351164202993381499 1695498526746304490072249)
          ·
            refine ⟨1271623895059728367554187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1695498526746304490072249 1271623895059728367554187)
            ·
              refine ⟨1907435842589592551331281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271623895059728367554187 1907435842589592551331281)
              ·
                refine ⟨1430576881942194413498461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907435842589592551331281 1430576881942194413498461)
                ·
                  refine ⟨536466330728322905061923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1430576881942194413498461 536466330728322905061923)
                  ·
                    refine ⟨804699496092484357592885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536466330728322905061923 804699496092484357592885)
                    ·
                      refine ⟨75440577758670408524333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 804699496092484357592885 75440577758670408524333)
                      ·
                        rfl

theorem cell23_146920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_146920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146920 prefixEnd_146920 := by exact prefixLift 146920
  have htrace : WordTrace (prefixWord ++ tailWord_146920) baseStart_146920 baseEnd_146920 := by
    simpa [prefixWord, tailWord_146920, baseEnd_146920] using wordTrace_append hprefix tailTrace_146920
  have hstable : (prefixWord ++ tailWord_146920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146920).length < 2 ^ (prefixWord ++ tailWord_146920).sum := by decide
  have hdescent : baseEnd_146920 < baseStart_146920 := by decide
  rcases family_descends (prefixWord ++ tailWord_146920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146934 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_146934 : Nat := 118140960795 + 146934 * 2 ^ 59
def prefixEnd_146934 : Nat := 4983230072969 + 3 ^ 40 * 146934 * 2
def baseEnd_146934 : Nat := 75447766487833353749269

theorem tailTrace_146934 : CollatzResearch.WordTrace tailWord_146934 prefixEnd_146934 75447766487833353749269 := by
  unfold tailWord_146934
  simp only [CollatzResearch.WordTrace]
  refine ⟨334945203105667948402991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3572748833127124782965237 334945203105667948402991)
  ·
    refine ⟨502417804658501922604487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334945203105667948402991 502417804658501922604487)
    ·
      refine ⟨753626706987752883906731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502417804658501922604487 753626706987752883906731)
      ·
        refine ⟨1130440060481629325860097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753626706987752883906731 1130440060481629325860097)
        ·
          refine ⟨847830045361221994395073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130440060481629325860097 847830045361221994395073)
          ·
            refine ⟨635872534020916495796305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847830045361221994395073 635872534020916495796305)
            ·
              refine ⟨476904400515687371847229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635872534020916495796305 476904400515687371847229)
              ·
                refine ⟨178839150193382764442711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 476904400515687371847229 178839150193382764442711)
                ·
                  refine ⟨268258725290074146664067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178839150193382764442711 268258725290074146664067)
                  ·
                    refine ⟨402388087935111219996101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 268258725290074146664067 402388087935111219996101)
                    ·
                      refine ⟨75447766487833353749269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 402388087935111219996101 75447766487833353749269)
                      ·
                        rfl

theorem cell23_146934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_146934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146934 prefixEnd_146934 := by exact prefixLift 146934
  have htrace : WordTrace (prefixWord ++ tailWord_146934) baseStart_146934 baseEnd_146934 := by
    simpa [prefixWord, tailWord_146934, baseEnd_146934] using wordTrace_append hprefix tailTrace_146934
  have hstable : (prefixWord ++ tailWord_146934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146934).length < 2 ^ (prefixWord ++ tailWord_146934).sum := by decide
  have hdescent : baseEnd_146934 < baseStart_146934 := by decide
  rcases family_descends (prefixWord ++ tailWord_146934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146951 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_146951 : Nat := 118140960795 + 146951 * 2 ^ 59
def prefixEnd_146951 : Nat := 4983230072969 + 3 ^ 40 * 146951 * 2
def baseEnd_146951 : Nat := 75456495658959787236691

theorem tailTrace_146951 : CollatzResearch.WordTrace tailWord_146951 prefixEnd_146951 75456495658959787236691 := by
  unfold tailWord_146951
  simp only [CollatzResearch.WordTrace]
  refine ⟨5359743290629099077816707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3573162193752732718544471 5359743290629099077816707)
  ·
    refine ⟨8039614935943648616725061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5359743290629099077816707 8039614935943648616725061)
    ·
      refine ⟨1507427800489434115635949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8039614935943648616725061 1507427800489434115635949)
      ·
        refine ⟨565285425183537793363481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1507427800489434115635949 565285425183537793363481)
        ·
          refine ⟨423964068887653345022611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565285425183537793363481 423964068887653345022611)
          ·
            refine ⟨635946103331480017533917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423964068887653345022611 635946103331480017533917)
            ·
              refine ⟨238479788749305006575219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 635946103331480017533917 238479788749305006575219)
              ·
                refine ⟨357719683123957509862829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238479788749305006575219 357719683123957509862829)
                ·
                  refine ⟨134144881171484066198561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357719683123957509862829 134144881171484066198561)
                  ·
                    refine ⟨100608660878613049648921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134144881171484066198561 100608660878613049648921)
                    ·
                      refine ⟨75456495658959787236691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100608660878613049648921 75456495658959787236691)
                      ·
                        rfl

theorem cell23_146951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_146951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_146951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_146951 prefixEnd_146951 := by exact prefixLift 146951
  have htrace : WordTrace (prefixWord ++ tailWord_146951) baseStart_146951 baseEnd_146951 := by
    simpa [prefixWord, tailWord_146951, baseEnd_146951] using wordTrace_append hprefix tailTrace_146951
  have hstable : (prefixWord ++ tailWord_146951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146951).length < 2 ^ (prefixWord ++ tailWord_146951).sum := by decide
  have hdescent : baseEnd_146951 < baseStart_146951 := by decide
  rcases family_descends (prefixWord ++ tailWord_146951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147001 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 3]
def baseStart_147001 : Nat := 118140960795 + 147001 * 2 ^ 59
def prefixEnd_147001 : Nat := 4983230072969 + 3 ^ 40 * 147001 * 2
def baseEnd_147001 : Nat := 75482169691684591611461

theorem tailTrace_147001 : CollatzResearch.WordTrace tailWord_147001 prefixEnd_147001 75482169691684591611461 := by
  unfold tailWord_147001
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361566940447957617136857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3574377960298638411424571 5361566940447957617136857)
  ·
    refine ⟨4021175205335968212852643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5361566940447957617136857 4021175205335968212852643)
    ·
      refine ⟨6031762808003952319278965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4021175205335968212852643 6031762808003952319278965)
      ·
        refine ⟨565477763250370529932403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6031762808003952319278965 565477763250370529932403)
        ·
          refine ⟨848216644875555794898605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565477763250370529932403 848216644875555794898605)
          ·
            refine ⟨318081241828333423086977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 848216644875555794898605 318081241828333423086977)
            ·
              refine ⟨238560931371250067315233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318081241828333423086977 238560931371250067315233)
              ·
                refine ⟨178920698528437550486425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238560931371250067315233 178920698528437550486425)
                ·
                  refine ⟨134190523896328162864819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178920698528437550486425 134190523896328162864819)
                  ·
                    refine ⟨201285785844492244297229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134190523896328162864819 201285785844492244297229)
                    ·
                      refine ⟨75482169691684591611461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 201285785844492244297229 75482169691684591611461)
                      ·
                        rfl

theorem cell23_147001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_147001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147001 prefixEnd_147001 := by exact prefixLift 147001
  have htrace : WordTrace (prefixWord ++ tailWord_147001) baseStart_147001 baseEnd_147001 := by
    simpa [prefixWord, tailWord_147001, baseEnd_147001] using wordTrace_append hprefix tailTrace_147001
  have hstable : (prefixWord ++ tailWord_147001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147001).length < 2 ^ (prefixWord ++ tailWord_147001).sum := by decide
  have hdescent : baseEnd_147001 < baseStart_147001 := by decide
  rcases family_descends (prefixWord ++ tailWord_147001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147024 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 1, 4, 2]
def baseStart_147024 : Nat := 118140960795 + 147024 * 2 ^ 59
def prefixEnd_147024 : Nat := 4983230072969 + 3 ^ 40 * 147024 * 2
def baseEnd_147024 : Nat := 75493979746738001623855

theorem tailTrace_147024 : CollatzResearch.WordTrace tailWord_147024 prefixEnd_147024 75493979746738001623855 := by
  unfold tailWord_147024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681202909682316272612063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3574937212909755030149417 2681202909682316272612063)
  ·
    refine ⟨4021804364523474408918095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2681202909682316272612063 4021804364523474408918095)
    ·
      refine ⟨6032706546785211613377143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4021804364523474408918095 6032706546785211613377143)
      ·
        refine ⟨9049059820177817420065715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6032706546785211613377143 9049059820177817420065715)
        ·
          refine ⟨13573589730266726130098573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9049059820177817420065715 13573589730266726130098573)
          ·
            refine ⟨5090096148850022298786965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13573589730266726130098573 5090096148850022298786965)
            ·
              refine ⟨238598256977344795255639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5090096148850022298786965 238598256977344795255639)
              ·
                refine ⟨357897385466017192883459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238598256977344795255639 357897385466017192883459)
                ·
                  refine ⟨536846078199025789325189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357897385466017192883459 536846078199025789325189)
                  ·
                    refine ⟨100658639662317335498473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 536846078199025789325189 100658639662317335498473)
                    ·
                      refine ⟨75493979746738001623855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100658639662317335498473 75493979746738001623855)
                      ·
                        rfl

theorem cell23_147024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 4, 2].length) (baseStart_147024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147024 prefixEnd_147024 := by exact prefixLift 147024
  have htrace : WordTrace (prefixWord ++ tailWord_147024) baseStart_147024 baseEnd_147024 := by
    simpa [prefixWord, tailWord_147024, baseEnd_147024] using wordTrace_append hprefix tailTrace_147024
  have hstable : (prefixWord ++ tailWord_147024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147024).length < 2 ^ (prefixWord ++ tailWord_147024).sum := by decide
  have hdescent : baseEnd_147024 < baseStart_147024 := by decide
  rcases family_descends (prefixWord ++ tailWord_147024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147040 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_147040 : Nat := 118140960795 + 147040 * 2 ^ 59
def prefixEnd_147040 : Nat := 4983230072969 + 3 ^ 40 * 147040 * 2
def baseEnd_147040 : Nat := 75502195437209939023781

theorem tailTrace_147040 : CollatzResearch.WordTrace tailWord_147040 prefixEnd_147040 75502195437209939023781 := by
  unfold tailWord_147040
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681494693653333638903287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3575326258204444851871049 2681494693653333638903287)
  ·
    refine ⟨4022242040480000458354931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2681494693653333638903287 4022242040480000458354931)
    ·
      refine ⟨6033363060720000687532397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4022242040480000458354931 6033363060720000687532397)
      ·
        refine ⟨2262511147770000257824649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6033363060720000687532397 2262511147770000257824649)
        ·
          refine ⟨1696883360827500193368487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2262511147770000257824649 1696883360827500193368487)
          ·
            refine ⟨2545325041241250290052731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696883360827500193368487 2545325041241250290052731)
            ·
              refine ⟨3817987561861875435079097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545325041241250290052731 3817987561861875435079097)
              ·
                refine ⟨2863490671396406576309323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3817987561861875435079097 2863490671396406576309323)
                ·
                  refine ⟨4295236007094609864463985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863490671396406576309323 4295236007094609864463985)
                  ·
                    refine ⟨3221427005320957398347989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4295236007094609864463985 3221427005320957398347989)
                    ·
                      refine ⟨75502195437209939023781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3221427005320957398347989 75502195437209939023781)
                      ·
                        rfl

theorem cell23_147040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_147040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147040 prefixEnd_147040 := by exact prefixLift 147040
  have htrace : WordTrace (prefixWord ++ tailWord_147040) baseStart_147040 baseEnd_147040 := by
    simpa [prefixWord, tailWord_147040, baseEnd_147040] using wordTrace_append hprefix tailTrace_147040
  have hstable : (prefixWord ++ tailWord_147040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147040).length < 2 ^ (prefixWord ++ tailWord_147040).sum := by decide
  have hdescent : baseEnd_147040 < baseStart_147040 := by decide
  rcases family_descends (prefixWord ++ tailWord_147040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147058 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_147058 : Nat := 118140960795 + 147058 * 2 ^ 59
def prefixEnd_147058 : Nat := 4983230072969 + 3 ^ 40 * 147058 * 2
def baseEnd_147058 : Nat := 75511438088990868598699

theorem tailTrace_147058 : CollatzResearch.WordTrace tailWord_147058 prefixEnd_147058 75511438088990868598699 := by
  unfold tailWord_147058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340911475310364087990457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3575763934160970901307885 1340911475310364087990457)
  ·
    refine ⟨1005683606482773065992843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1340911475310364087990457 1005683606482773065992843)
    ·
      refine ⟨1508525409724159598989265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005683606482773065992843 1508525409724159598989265)
      ·
        refine ⟨1131394057293119699241949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1508525409724159598989265 1131394057293119699241949)
        ·
          refine ⟨424272771484919887215731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1131394057293119699241949 424272771484919887215731)
          ·
            refine ⟨636409157227379830823597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424272771484919887215731 636409157227379830823597)
            ·
              refine ⟨238653433960267436558849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 636409157227379830823597 238653433960267436558849)
              ·
                refine ⟨178990075470200577419137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238653433960267436558849 178990075470200577419137)
                ·
                  refine ⟨134242556602650433064353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178990075470200577419137 134242556602650433064353)
                  ·
                    refine ⟨100681917451987824798265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134242556602650433064353 100681917451987824798265)
                    ·
                      refine ⟨75511438088990868598699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100681917451987824798265 75511438088990868598699)
                      ·
                        rfl

theorem cell23_147058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_147058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147058 prefixEnd_147058 := by exact prefixLift 147058
  have htrace : WordTrace (prefixWord ++ tailWord_147058) baseStart_147058 baseEnd_147058 := by
    simpa [prefixWord, tailWord_147058, baseEnd_147058] using wordTrace_append hprefix tailTrace_147058
  have hstable : (prefixWord ++ tailWord_147058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147058).length < 2 ^ (prefixWord ++ tailWord_147058).sum := by decide
  have hdescent : baseEnd_147058 < baseStart_147058 := by decide
  rcases family_descends (prefixWord ++ tailWord_147058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147147 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 3]
def baseStart_147147 : Nat := 118140960795 + 147147 * 2 ^ 59
def prefixEnd_147147 : Nat := 4983230072969 + 3 ^ 40 * 147147 * 2
def baseEnd_147147 : Nat := 75557137867241020385789

theorem tailTrace_147147 : CollatzResearch.WordTrace tailWord_147147 prefixEnd_147147 75557137867241020385789 := by
  unfold tailWord_147147
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366891997919024551951695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3577927998612683034634463 5366891997919024551951695)
  ·
    refine ⟨8050337996878536827927543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5366891997919024551951695 8050337996878536827927543)
    ·
      refine ⟨12075506995317805241891315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8050337996878536827927543 12075506995317805241891315)
      ·
        refine ⟨18113260492976707862836973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12075506995317805241891315 18113260492976707862836973)
        ·
          refine ⟨6792472684866265448563865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18113260492976707862836973 6792472684866265448563865)
          ·
            refine ⟨5094354513649699086422899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6792472684866265448563865 5094354513649699086422899)
            ·
              refine ⟨7641531770474548629634349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094354513649699086422899 7641531770474548629634349)
              ·
                refine ⟨2865574413927955736112881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7641531770474548629634349 2865574413927955736112881)
                ·
                  refine ⟨2149180810445966802084661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2865574413927955736112881 2149180810445966802084661)
                  ·
                    refine ⟨201485700979309387695437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2149180810445966802084661 201485700979309387695437)
                    ·
                      refine ⟨75557137867241020385789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 201485700979309387695437 75557137867241020385789)
                      ·
                        rfl

theorem cell23_147147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 3].length) (baseStart_147147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147147 prefixEnd_147147 := by exact prefixLift 147147
  have htrace : WordTrace (prefixWord ++ tailWord_147147) baseStart_147147 baseEnd_147147 := by
    simpa [prefixWord, tailWord_147147, baseEnd_147147] using wordTrace_append hprefix tailTrace_147147
  have hstable : (prefixWord ++ tailWord_147147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147147).length < 2 ^ (prefixWord ++ tailWord_147147).sum := by decide
  have hdescent : baseEnd_147147 < baseStart_147147 := by decide
  rcases family_descends (prefixWord ++ tailWord_147147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147171 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 6]
def baseStart_147171 : Nat := 118140960795 + 147171 * 2 ^ 59
def prefixEnd_147171 : Nat := 4983230072969 + 3 ^ 40 * 147171 * 2
def baseEnd_147171 : Nat := 8396606822549880720631

theorem tailTrace_147171 : CollatzResearch.WordTrace tailWord_147171 prefixEnd_147171 8396606822549880720631 := by
  unfold tailWord_147171
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367767349832076650825367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3578511566554717767216911 5367767349832076650825367)
  ·
    refine ⟨8051651024748114976238051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5367767349832076650825367 8051651024748114976238051)
    ·
      refine ⟨12077476537122172464357077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8051651024748114976238051 12077476537122172464357077)
      ·
        refine ⟨283065856338800917133369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12077476537122172464357077 283065856338800917133369)
        ·
          refine ⟨212299392254100687850027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283065856338800917133369 212299392254100687850027)
          ·
            refine ⟨318449088381151031775041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212299392254100687850027 318449088381151031775041)
            ·
              refine ⟨238836816285863273831281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318449088381151031775041 238836816285863273831281)
              ·
                refine ⟨179127612214397455373461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238836816285863273831281 179127612214397455373461)
                ·
                  refine ⟨8396606822549880720631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179127612214397455373461 8396606822549880720631)
                  ·
                    rfl

theorem cell23_147171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 6].length) (baseStart_147171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147171 prefixEnd_147171 := by exact prefixLift 147171
  have htrace : WordTrace (prefixWord ++ tailWord_147171) baseStart_147171 baseEnd_147171 := by
    simpa [prefixWord, tailWord_147171, baseEnd_147171] using wordTrace_append hprefix tailTrace_147171
  have hstable : (prefixWord ++ tailWord_147171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147171).length < 2 ^ (prefixWord ++ tailWord_147171).sum := by decide
  have hdescent : baseEnd_147171 < baseStart_147171 := by decide
  rcases family_descends (prefixWord ++ tailWord_147171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147175 : List Nat := [1, 1, 5, 4, 1, 1, 1, 4, 1, 4]
def baseStart_147175 : Nat := 118140960795 + 147175 * 2 ^ 59
def prefixEnd_147175 : Nat := 4983230072969 + 3 ^ 40 * 147175 * 2
def baseEnd_147175 : Nat := 25190505108522303611887

theorem tailTrace_147175 : CollatzResearch.WordTrace tailWord_147175 prefixEnd_147175 25190505108522303611887 := by
  unfold tailWord_147175
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367913241817585333970979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3578608827878390222647319 5367913241817585333970979)
  ·
    refine ⟨8051869862726378000956469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5367913241817585333970979 8051869862726378000956469)
    ·
      refine ⟨754862799630597937589669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8051869862726378000956469 754862799630597937589669)
      ·
        refine ⟨141536774930737113298063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 754862799630597937589669 141536774930737113298063)
        ·
          refine ⟨212305162396105669947095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141536774930737113298063 212305162396105669947095)
          ·
            refine ⟨318457743594158504920643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212305162396105669947095 318457743594158504920643)
            ·
              refine ⟨477686615391237757380965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318457743594158504920643 477686615391237757380965)
              ·
                refine ⟨89566240385857079508931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477686615391237757380965 89566240385857079508931)
                ·
                  refine ⟨134349360578785619263397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89566240385857079508931 134349360578785619263397)
                  ·
                    refine ⟨25190505108522303611887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134349360578785619263397 25190505108522303611887)
                    ·
                      rfl

theorem cell23_147175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_147175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147175 prefixEnd_147175 := by exact prefixLift 147175
  have htrace : WordTrace (prefixWord ++ tailWord_147175) baseStart_147175 baseEnd_147175 := by
    simpa [prefixWord, tailWord_147175, baseEnd_147175] using wordTrace_append hprefix tailTrace_147175
  have hstable : (prefixWord ++ tailWord_147175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147175).length < 2 ^ (prefixWord ++ tailWord_147175).sum := by decide
  have hdescent : baseEnd_147175 < baseStart_147175 := by decide
  rcases family_descends (prefixWord ++ tailWord_147175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147188 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 6]
def baseStart_147188 : Nat := 118140960795 + 147188 * 2 ^ 59
def prefixEnd_147188 : Nat := 4983230072969 + 3 ^ 40 * 147188 * 2
def baseEnd_147188 : Nat := 8397576730452817774789

theorem tailTrace_147188 : CollatzResearch.WordTrace tailWord_147188 prefixEnd_147188 8397576730452817774789 := by
  unfold tailWord_147188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684193695385244277097109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3578924927180325702796145 2684193695385244277097109)
  ·
    refine ⟨125821579471183325488927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2684193695385244277097109 125821579471183325488927)
    ·
      refine ⟨188732369206774988233391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125821579471183325488927 188732369206774988233391)
      ·
        refine ⟨283098553810162482350087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188732369206774988233391 283098553810162482350087)
        ·
          refine ⟨424647830715243723525131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283098553810162482350087 424647830715243723525131)
          ·
            refine ⟨636971746072865585287697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424647830715243723525131 636971746072865585287697)
            ·
              refine ⟨477728809554649188965773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636971746072865585287697 477728809554649188965773)
              ·
                refine ⟨179148303582993445862165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477728809554649188965773 179148303582993445862165)
                ·
                  refine ⟨8397576730452817774789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179148303582993445862165 8397576730452817774789)
                  ·
                    rfl

theorem cell23_147188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_147188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147188 prefixEnd_147188 := by exact prefixLift 147188
  have htrace : WordTrace (prefixWord ++ tailWord_147188) baseStart_147188 baseEnd_147188 := by
    simpa [prefixWord, tailWord_147188, baseEnd_147188] using wordTrace_append hprefix tailTrace_147188
  have hstable : (prefixWord ++ tailWord_147188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147188).length < 2 ^ (prefixWord ++ tailWord_147188).sum := by decide
  have hdescent : baseEnd_147188 < baseStart_147188 := by decide
  rcases family_descends (prefixWord ++ tailWord_147188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147214 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_147214 : Nat := 118140960795 + 147214 * 2 ^ 59
def prefixEnd_147214 : Nat := 4983230072969 + 3 ^ 40 * 147214 * 2
def baseEnd_147214 : Nat := 25197180357030752749327

theorem tailTrace_147214 : CollatzResearch.WordTrace tailWord_147214 prefixEnd_147214 25197180357030752749327 := by
  unfold tailWord_147214
  simp only [CollatzResearch.WordTrace]
  refine ⟨671166961084536874330087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3579557125784196663093797 671166961084536874330087)
  ·
    refine ⟨1006750441626805311495131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 671166961084536874330087 1006750441626805311495131)
    ·
      refine ⟨1510125662440207967242697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006750441626805311495131 1510125662440207967242697)
      ·
        refine ⟨1132594246830155975432023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1510125662440207967242697 1132594246830155975432023)
        ·
          refine ⟨1698891370245233963148035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132594246830155975432023 1698891370245233963148035)
          ·
            refine ⟨2548337055367850944722053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698891370245233963148035 2548337055367850944722053)
            ·
              refine ⟨477813197881472052135385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2548337055367850944722053 477813197881472052135385)
              ·
                refine ⟨358359898411104039101539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477813197881472052135385 358359898411104039101539)
                ·
                  refine ⟨537539847616656058652309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358359898411104039101539 537539847616656058652309)
                  ·
                    refine ⟨25197180357030752749327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 537539847616656058652309 25197180357030752749327)
                    ·
                      rfl

theorem cell23_147214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_147214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147214 prefixEnd_147214 := by exact prefixLift 147214
  have htrace : WordTrace (prefixWord ++ tailWord_147214) baseStart_147214 baseEnd_147214 := by
    simpa [prefixWord, tailWord_147214, baseEnd_147214] using wordTrace_append hprefix tailTrace_147214
  have hstable : (prefixWord ++ tailWord_147214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147214).length < 2 ^ (prefixWord ++ tailWord_147214).sum := by decide
  have hdescent : baseEnd_147214 < baseStart_147214 := by decide
  rcases family_descends (prefixWord ++ tailWord_147214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147217 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_147217 : Nat := 118140960795 + 147217 * 2 ^ 59
def prefixEnd_147217 : Nat := 4983230072969 + 3 ^ 40 * 147217 * 2
def baseEnd_147217 : Nat := 75593081513055746510467

theorem tailTrace_147217 : CollatzResearch.WordTrace tailWord_147217 prefixEnd_147217 75593081513055746510467 := by
  unfold tailWord_147217
  simp only [CollatzResearch.WordTrace]
  refine ⟨5369445107665426506999905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3579630071776951004666603 5369445107665426506999905)
  ·
    refine ⟨4027083830749069880249929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5369445107665426506999905 4027083830749069880249929)
    ·
      refine ⟨3020312873061802410187447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4027083830749069880249929 3020312873061802410187447)
      ·
        refine ⟨4530469309592703615281171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3020312873061802410187447 4530469309592703615281171)
        ·
          refine ⟨6795703964389055422921757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4530469309592703615281171 6795703964389055422921757)
          ·
            refine ⟨2548388986645895783595659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6795703964389055422921757 2548388986645895783595659)
            ·
              refine ⟨3822583479968843675393489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548388986645895783595659 3822583479968843675393489)
              ·
                refine ⟨2866937609976632756545117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822583479968843675393489 2866937609976632756545117)
                ·
                  refine ⟨1075101603741237283704419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2866937609976632756545117 1075101603741237283704419)
                  ·
                    refine ⟨1612652405611855925556629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1075101603741237283704419 1612652405611855925556629)
                    ·
                      refine ⟨75593081513055746510467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1612652405611855925556629 75593081513055746510467)
                      ·
                        rfl

theorem cell23_147217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_147217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147217 prefixEnd_147217 := by exact prefixLift 147217
  have htrace : WordTrace (prefixWord ++ tailWord_147217) baseStart_147217 baseEnd_147217 := by
    simpa [prefixWord, tailWord_147217, baseEnd_147217] using wordTrace_append hprefix tailTrace_147217
  have hstable : (prefixWord ++ tailWord_147217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147217).length < 2 ^ (prefixWord ++ tailWord_147217).sum := by decide
  have hdescent : baseEnd_147217 < baseStart_147217 := by decide
  rcases family_descends (prefixWord ++ tailWord_147217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147218 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_147218 : Nat := 118140960795 + 147218 * 2 ^ 59
def prefixEnd_147218 : Nat := 4983230072969 + 3 ^ 40 * 147218 * 2
def baseEnd_147218 : Nat := 25197864997903414199321

theorem tailTrace_147218 : CollatzResearch.WordTrace tailWord_147218 prefixEnd_147218 25197864997903414199321 := by
  unfold tailWord_147218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342370395165450919446577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3579654387107869118524205 1342370395165450919446577)
  ·
    refine ⟨1006777796374088189584933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1342370395165450919446577 1006777796374088189584933)
    ·
      refine ⟨188770836820141535547175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1006777796374088189584933 188770836820141535547175)
      ·
        refine ⟨283156255230212303320763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188770836820141535547175 283156255230212303320763)
        ·
          refine ⟨424734382845318454981145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283156255230212303320763 424734382845318454981145)
          ·
            refine ⟨318550787133988841235859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424734382845318454981145 318550787133988841235859)
            ·
              refine ⟨477826180700983261853789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318550787133988841235859 477826180700983261853789)
              ·
                refine ⟨179184817762868723195171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477826180700983261853789 179184817762868723195171)
                ·
                  refine ⟨268777226644303084792757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179184817762868723195171 268777226644303084792757)
                  ·
                    refine ⟨25197864997903414199321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 268777226644303084792757 25197864997903414199321)
                    ·
                      rfl

theorem cell23_147218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_147218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147218 prefixEnd_147218 := by exact prefixLift 147218
  have htrace : WordTrace (prefixWord ++ tailWord_147218) baseStart_147218 baseEnd_147218 := by
    simpa [prefixWord, tailWord_147218, baseEnd_147218] using wordTrace_append hprefix tailTrace_147218
  have hstable : (prefixWord ++ tailWord_147218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147218).length < 2 ^ (prefixWord ++ tailWord_147218).sum := by decide
  have hdescent : baseEnd_147218 < baseStart_147218 := by decide
  rcases family_descends (prefixWord ++ tailWord_147218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147221 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_147221 : Nat := 118140960795 + 147221 * 2 ^ 59
def prefixEnd_147221 : Nat := 4983230072969 + 3 ^ 40 * 147221 * 2
def baseEnd_147221 : Nat := 75595135435673730860449

theorem tailTrace_147221 : CollatzResearch.WordTrace tailWord_147221 prefixEnd_147221 75595135435673730860449 := by
  unfold tailWord_147221
  simp only [CollatzResearch.WordTrace]
  refine ⟨5369590999650935190145517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3579727333100623460097011 5369590999650935190145517)
  ·
    refine ⟨2013596624869100696304569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5369590999650935190145517 2013596624869100696304569)
    ·
      refine ⟨1510197468651825522228427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2013596624869100696304569 1510197468651825522228427)
      ·
        refine ⟨2265296202977738283342641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510197468651825522228427 2265296202977738283342641)
        ·
          refine ⟨1698972152233303712506981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2265296202977738283342641 1698972152233303712506981)
          ·
            refine ⟨318557278543744446095059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1698972152233303712506981 318557278543744446095059)
            ·
              refine ⟨477835917815616669142589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318557278543744446095059 477835917815616669142589)
              ·
                refine ⟨179188469180856250928471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477835917815616669142589 179188469180856250928471)
                ·
                  refine ⟨268782703771284376392707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179188469180856250928471 268782703771284376392707)
                  ·
                    refine ⟨403174055656926564589061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 268782703771284376392707 403174055656926564589061)
                    ·
                      refine ⟨75595135435673730860449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 403174055656926564589061 75595135435673730860449)
                      ·
                        rfl

theorem cell23_147221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_147221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147221 prefixEnd_147221 := by exact prefixLift 147221
  have htrace : WordTrace (prefixWord ++ tailWord_147221) baseStart_147221 baseEnd_147221 := by
    simpa [prefixWord, tailWord_147221, baseEnd_147221] using wordTrace_append hprefix tailTrace_147221
  have hstable : (prefixWord ++ tailWord_147221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147221).length < 2 ^ (prefixWord ++ tailWord_147221).sum := by decide
  have hdescent : baseEnd_147221 < baseStart_147221 := by decide
  rcases family_descends (prefixWord ++ tailWord_147221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147234 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_147234 : Nat := 118140960795 + 147234 * 2 ^ 59
def prefixEnd_147234 : Nat := 4983230072969 + 3 ^ 40 * 147234 * 2
def baseEnd_147234 : Nat := 75601810684182179997889

theorem tailTrace_147234 : CollatzResearch.WordTrace tailWord_147234 prefixEnd_147234 75601810684182179997889 := by
  unfold tailWord_147234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342516287150959602592189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3580043432402558940245837 1342516287150959602592189)
  ·
    refine ⟨503443607681609850972071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1342516287150959602592189 503443607681609850972071)
    ·
      refine ⟨755165411522414776458107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503443607681609850972071 755165411522414776458107)
      ·
        refine ⟨1132748117283622164687161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755165411522414776458107 1132748117283622164687161)
        ·
          refine ⟨849561087962716623515371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1132748117283622164687161 849561087962716623515371)
          ·
            refine ⟨1274341631944074935273057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849561087962716623515371 1274341631944074935273057)
            ·
              refine ⟨955756223958056201454793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274341631944074935273057 955756223958056201454793)
              ·
                refine ⟨716817167968542151091095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955756223958056201454793 716817167968542151091095)
                ·
                  refine ⟨1075225751952813226636643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716817167968542151091095 1075225751952813226636643)
                  ·
                    refine ⟨1612838627929219839954965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1075225751952813226636643 1612838627929219839954965)
                    ·
                      refine ⟨75601810684182179997889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1612838627929219839954965 75601810684182179997889)
                      ·
                        rfl

theorem cell23_147234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_147234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147234 prefixEnd_147234 := by exact prefixLift 147234
  have htrace : WordTrace (prefixWord ++ tailWord_147234) baseStart_147234 baseEnd_147234 := by
    simpa [prefixWord, tailWord_147234, baseEnd_147234] using wordTrace_append hprefix tailTrace_147234
  have hstable : (prefixWord ++ tailWord_147234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147234).length < 2 ^ (prefixWord ++ tailWord_147234).sum := by decide
  have hdescent : baseEnd_147234 < baseStart_147234 := by decide
  rcases family_descends (prefixWord ++ tailWord_147234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147247 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_147247 : Nat := 118140960795 + 147247 * 2 ^ 59
def prefixEnd_147247 : Nat := 4983230072969 + 3 ^ 40 * 147247 * 2
def baseEnd_147247 : Nat := 75608485932690629135329

theorem tailTrace_147247 : CollatzResearch.WordTrace tailWord_147247 prefixEnd_147247 75608485932690629135329 := by
  unfold tailWord_147247
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370539297556741630591995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3580359531704494420394663 5370539297556741630591995)
  ·
    refine ⟨8055808946335112445887993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5370539297556741630591995 8055808946335112445887993)
    ·
      refine ⟨6041856709751334334415995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8055808946335112445887993 6041856709751334334415995)
      ·
        refine ⟨9062785064627001501623993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6041856709751334334415995 9062785064627001501623993)
        ·
          refine ⟨6797088798470251126217995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9062785064627001501623993 6797088798470251126217995)
          ·
            refine ⟨10195633197705376689326993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797088798470251126217995 10195633197705376689326993)
            ·
              refine ⟨7646724898279032516995245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10195633197705376689326993 7646724898279032516995245)
              ·
                refine ⟨2867521836854637193873217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7646724898279032516995245 2867521836854637193873217)
                ·
                  refine ⟨2150641377640977895404913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2867521836854637193873217 2150641377640977895404913)
                  ·
                    refine ⟨1612981033230733421553685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2150641377640977895404913 1612981033230733421553685)
                    ·
                      refine ⟨75608485932690629135329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1612981033230733421553685 75608485932690629135329)
                      ·
                        rfl

theorem cell23_147247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_147247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147247 prefixEnd_147247 := by exact prefixLift 147247
  have htrace : WordTrace (prefixWord ++ tailWord_147247) baseStart_147247 baseEnd_147247 := by
    simpa [prefixWord, tailWord_147247, baseEnd_147247] using wordTrace_append hprefix tailTrace_147247
  have hstable : (prefixWord ++ tailWord_147247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147247).length < 2 ^ (prefixWord ++ tailWord_147247).sum := by decide
  have hdescent : baseEnd_147247 < baseStart_147247 := by decide
  rcases family_descends (prefixWord ++ tailWord_147247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147258 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_147258 : Nat := 118140960795 + 147258 * 2 ^ 59
def prefixEnd_147258 : Nat := 4983230072969 + 3 ^ 40 * 147258 * 2
def baseEnd_147258 : Nat := 75614134219890086097779

theorem tailTrace_147258 : CollatzResearch.WordTrace tailWord_147258 prefixEnd_147258 75614134219890086097779 := by
  unfold tailWord_147258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342735125129222627310607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3580627000344593672828285 1342735125129222627310607)
  ·
    refine ⟨2014102687693833940965911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1342735125129222627310607 2014102687693833940965911)
    ·
      refine ⟨3021154031540750911448867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014102687693833940965911 3021154031540750911448867)
      ·
        refine ⟨4531731047311126367173301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021154031540750911448867 4531731047311126367173301)
        ·
          refine ⟨424849785685418096922497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4531731047311126367173301 424849785685418096922497)
          ·
            refine ⟨318637339264063572691873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424849785685418096922497 318637339264063572691873)
            ·
              refine ⟨238978004448047679518905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318637339264063572691873 238978004448047679518905)
              ·
                refine ⟨179233503336035759639179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238978004448047679518905 179233503336035759639179)
                ·
                  refine ⟨268850255004053639458769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179233503336035759639179 268850255004053639458769)
                  ·
                    refine ⟨201637691253040229594077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 268850255004053639458769 201637691253040229594077)
                    ·
                      refine ⟨75614134219890086097779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 201637691253040229594077 75614134219890086097779)
                      ·
                        rfl

theorem cell23_147258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_147258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147258 prefixEnd_147258 := by exact prefixLift 147258
  have htrace : WordTrace (prefixWord ++ tailWord_147258) baseStart_147258 baseEnd_147258 := by
    simpa [prefixWord, tailWord_147258, baseEnd_147258] using wordTrace_append hprefix tailTrace_147258
  have hstable : (prefixWord ++ tailWord_147258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147258).length < 2 ^ (prefixWord ++ tailWord_147258).sum := by decide
  have hdescent : baseEnd_147258 < baseStart_147258 := by decide
  rcases family_descends (prefixWord ++ tailWord_147258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147261 : List Nat := [1, 4, 1, 4, 1, 1, 4, 7]
def baseStart_147261 : Nat := 118140960795 + 147261 * 2 ^ 59
def prefixEnd_147261 : Nat := 4983230072969 + 3 ^ 40 * 147261 * 2
def baseEnd_147261 : Nat := 2800580543031613865195

theorem tailTrace_147261 : CollatzResearch.WordTrace tailWord_147261 prefixEnd_147261 2800580543031613865195 := by
  unfold tailWord_147261
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371049919506022021601637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3580699946337348014401091 5371049919506022021601637)
  ·
    refine ⟨1007071859907379129050307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5371049919506022021601637 1007071859907379129050307)
    ·
      refine ⟨1510607789861068693575461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1007071859907379129050307 1510607789861068693575461)
      ·
        refine ⟨283238960598950380045399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1510607789861068693575461 283238960598950380045399)
        ·
          refine ⟨424858440898425570068099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283238960598950380045399 424858440898425570068099)
          ·
            refine ⟨637287661347638355102149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424858440898425570068099 637287661347638355102149)
            ·
              refine ⟨119491436502682191581653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 637287661347638355102149 119491436502682191581653)
              ·
                refine ⟨2800580543031613865195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119491436502682191581653 2800580543031613865195)
                ·
                  rfl

theorem cell23_147261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 7].length) (baseStart_147261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147261 prefixEnd_147261 := by exact prefixLift 147261
  have htrace : WordTrace (prefixWord ++ tailWord_147261) baseStart_147261 baseEnd_147261 := by
    simpa [prefixWord, tailWord_147261, baseEnd_147261] using wordTrace_append hprefix tailTrace_147261
  have hstable : (prefixWord ++ tailWord_147261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147261).length < 2 ^ (prefixWord ++ tailWord_147261).sum := by decide
  have hdescent : baseEnd_147261 < baseStart_147261 := by decide
  rcases family_descends (prefixWord ++ tailWord_147261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147271 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_147271 : Nat := 118140960795 + 147271 * 2 ^ 59
def prefixEnd_147271 : Nat := 4983230072969 + 3 ^ 40 * 147271 * 2
def baseEnd_147271 : Nat := 75620809468398535235219

theorem tailTrace_147271 : CollatzResearch.WordTrace tailWord_147271 prefixEnd_147271 75620809468398535235219 := by
  unfold tailWord_147271
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371414649469793729465667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3580943099646529152977111 5371414649469793729465667)
  ·
    refine ⟨8057121974204690594198501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5371414649469793729465667 8057121974204690594198501)
    ·
      refine ⟨1510710370163379486412219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8057121974204690594198501 1510710370163379486412219)
      ·
        refine ⟨2266065555245069229618329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510710370163379486412219 2266065555245069229618329)
        ·
          refine ⟨1699549166433801922213747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2266065555245069229618329 1699549166433801922213747)
          ·
            refine ⟨2549323749650702883320621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699549166433801922213747 2549323749650702883320621)
            ·
              refine ⟨955996406119013581245233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2549323749650702883320621 955996406119013581245233)
              ·
                refine ⟨716997304589260185933925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955996406119013581245233 716997304589260185933925)
                ·
                  refine ⟨134436994610486284862611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 716997304589260185933925 134436994610486284862611)
                  ·
                    refine ⟨201655491915729427293917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134436994610486284862611 201655491915729427293917)
                    ·
                      refine ⟨75620809468398535235219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 201655491915729427293917 75620809468398535235219)
                      ·
                        rfl

theorem cell23_147271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_147271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147271 prefixEnd_147271 := by exact prefixLift 147271
  have htrace : WordTrace (prefixWord ++ tailWord_147271) baseStart_147271 baseEnd_147271 := by
    simpa [prefixWord, tailWord_147271, baseEnd_147271] using wordTrace_append hprefix tailTrace_147271
  have hstable : (prefixWord ++ tailWord_147271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147271).length < 2 ^ (prefixWord ++ tailWord_147271).sum := by decide
  have hdescent : baseEnd_147271 < baseStart_147271 := by decide
  rcases family_descends (prefixWord ++ tailWord_147271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147272 : List Nat := [2, 1, 3, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_147272 : Nat := 118140960795 + 147272 * 2 ^ 59
def prefixEnd_147272 : Nat := 4983230072969 + 3 ^ 40 * 147272 * 2
def baseEnd_147272 : Nat := 75621322949053031322715

theorem tailTrace_147272 : CollatzResearch.WordTrace tailWord_147272 prefixEnd_147272 75621322949053031322715 := by
  unfold tailWord_147272
  simp only [CollatzResearch.WordTrace]
  refine ⟨2685725561233085450126035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3580967414977447266834713 2685725561233085450126035)
  ·
    refine ⟨4028588341849628175189053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2685725561233085450126035 4028588341849628175189053)
    ·
      refine ⟨1510720628193610565695895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4028588341849628175189053 1510720628193610565695895)
      ·
        refine ⟨2266080942290415848543843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510720628193610565695895 2266080942290415848543843)
        ·
          refine ⟨3399121413435623772815765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266080942290415848543843 3399121413435623772815765)
          ·
            refine ⟨159333816254794864350739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3399121413435623772815765 159333816254794864350739)
            ·
              refine ⟨239000724382192296526109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159333816254794864350739 239000724382192296526109)
              ·
                refine ⟨89625271643322111197291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239000724382192296526109 89625271643322111197291)
                ·
                  refine ⟨134437907464983166795937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89625271643322111197291 134437907464983166795937)
                  ·
                    refine ⟨100828430598737375096953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134437907464983166795937 100828430598737375096953)
                    ·
                      refine ⟨75621322949053031322715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100828430598737375096953 75621322949053031322715)
                      ·
                        rfl

theorem cell23_147272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_147272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147272 prefixEnd_147272 := by exact prefixLift 147272
  have htrace : WordTrace (prefixWord ++ tailWord_147272) baseStart_147272 baseEnd_147272 := by
    simpa [prefixWord, tailWord_147272, baseEnd_147272] using wordTrace_append hprefix tailTrace_147272
  have hstable : (prefixWord ++ tailWord_147272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147272).length < 2 ^ (prefixWord ++ tailWord_147272).sum := by decide
  have hdescent : baseEnd_147272 < baseStart_147272 := by decide
  rcases family_descends (prefixWord ++ tailWord_147272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147304 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 1, 8]
def baseStart_147304 : Nat := 118140960795 + 147304 * 2 ^ 59
def prefixEnd_147304 : Nat := 4983230072969 + 3 ^ 40 * 147304 * 2
def baseEnd_147304 : Nat := 25212584776665635374189

theorem tailTrace_147304 : CollatzResearch.WordTrace tailWord_147304 prefixEnd_147304 25212584776665635374189 := by
  unfold tailWord_147304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686309129175120182708483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3581745505566826910277977 2686309129175120182708483)
  ·
    refine ⟨4029463693762680274062725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2686309129175120182708483 4029463693762680274062725)
    ·
      refine ⟨755524442580502551386761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4029463693762680274062725 755524442580502551386761)
      ·
        refine ⟨566643331935376913540071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 755524442580502551386761 566643331935376913540071)
        ·
          refine ⟨849964997903065370310107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566643331935376913540071 849964997903065370310107)
          ·
            refine ⟨1274947496854598055465161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849964997903065370310107 1274947496854598055465161)
            ·
              refine ⟨956210622640948541598871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274947496854598055465161 956210622640948541598871)
              ·
                refine ⟨1434315933961422812398307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956210622640948541598871 1434315933961422812398307)
                ·
                  refine ⟨2151473900942134218597461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434315933961422812398307 2151473900942134218597461)
                  ·
                    refine ⟨25212584776665635374189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2151473900942134218597461 25212584776665635374189)
                    ·
                      rfl

theorem cell23_147304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_147304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147304 prefixEnd_147304 := by exact prefixLift 147304
  have htrace : WordTrace (prefixWord ++ tailWord_147304) baseStart_147304 baseEnd_147304 := by
    simpa [prefixWord, tailWord_147304, baseEnd_147304] using wordTrace_append hprefix tailTrace_147304
  have hstable : (prefixWord ++ tailWord_147304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147304).length < 2 ^ (prefixWord ++ tailWord_147304).sum := by decide
  have hdescent : baseEnd_147304 < baseStart_147304 := by decide
  rcases family_descends (prefixWord ++ tailWord_147304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147324 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_147324 : Nat := 118140960795 + 147324 * 2 ^ 59
def prefixEnd_147324 : Nat := 4983230072969 + 3 ^ 40 * 147324 * 2
def baseEnd_147324 : Nat := 75648023943086827872475

theorem tailTrace_147324 : CollatzResearch.WordTrace tailWord_147324 prefixEnd_147324 75648023943086827872475 := by
  unfold tailWord_147324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686673859138891890572513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3582231812185189187430017 2686673859138891890572513)
  ·
    refine ⟨2015005394354168917929385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2686673859138891890572513 2015005394354168917929385)
    ·
      refine ⟨1511254045765626688447039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2015005394354168917929385 1511254045765626688447039)
      ·
        refine ⟨2266881068648440032670559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511254045765626688447039 2266881068648440032670559)
        ·
          refine ⟨3400321602972660049005839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266881068648440032670559 3400321602972660049005839)
          ·
            refine ⟨5100482404458990073508759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400321602972660049005839 5100482404458990073508759)
            ·
              refine ⟨7650723606688485110263139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100482404458990073508759 7650723606688485110263139)
              ·
                refine ⟨11476085410032727665394709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7650723606688485110263139 11476085410032727665394709)
                ·
                  refine ⟨537941503595284109315377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11476085410032727665394709 537941503595284109315377)
                  ·
                    refine ⟨403456127696463081986533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537941503595284109315377 403456127696463081986533)
                    ·
                      refine ⟨75648023943086827872475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 403456127696463081986533 75648023943086827872475)
                      ·
                        rfl

theorem cell23_147324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_147324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147324 prefixEnd_147324 := by exact prefixLift 147324
  have htrace : WordTrace (prefixWord ++ tailWord_147324) baseStart_147324 baseEnd_147324 := by
    simpa [prefixWord, tailWord_147324, baseEnd_147324] using wordTrace_append hprefix tailTrace_147324
  have hstable : (prefixWord ++ tailWord_147324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147324).length < 2 ^ (prefixWord ++ tailWord_147324).sum := by decide
  have hdescent : baseEnd_147324 < baseStart_147324 := by decide
  rcases family_descends (prefixWord ++ tailWord_147324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147381 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_147381 : Nat := 118140960795 + 147381 * 2 ^ 59
def prefixEnd_147381 : Nat := 4983230072969 + 3 ^ 40 * 147381 * 2
def baseEnd_147381 : Nat := 25225764113464368286571

theorem tailTrace_147381 : CollatzResearch.WordTrace tailWord_147381 prefixEnd_147381 25225764113464368286571 := by
  unfold tailWord_147381
  simp only [CollatzResearch.WordTrace]
  refine ⟨5375426679071282515969997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3583617786047521677313331 5375426679071282515969997)
  ·
    refine ⟨2015785004651730943488749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5375426679071282515969997 2015785004651730943488749)
    ·
      refine ⟨755919376744399103808281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2015785004651730943488749 755919376744399103808281)
      ·
        refine ⟨566939532558299327856211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 755919376744399103808281 566939532558299327856211)
        ·
          refine ⟨850409298837448991784317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566939532558299327856211 850409298837448991784317)
          ·
            refine ⟨318903487064043371919119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 850409298837448991784317 318903487064043371919119)
            ·
              refine ⟨478355230596065057878679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318903487064043371919119 478355230596065057878679)
              ·
                refine ⟨717532845894097586818019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478355230596065057878679 717532845894097586818019)
                ·
                  refine ⟨1076299268841146380227029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717532845894097586818019 1076299268841146380227029)
                  ·
                    refine ⟨25225764113464368286571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1076299268841146380227029 25225764113464368286571)
                    ·
                      rfl

theorem cell23_147381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_147381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147381 prefixEnd_147381 := by exact prefixLift 147381
  have htrace : WordTrace (prefixWord ++ tailWord_147381) baseStart_147381 baseEnd_147381 := by
    simpa [prefixWord, tailWord_147381, baseEnd_147381] using wordTrace_append hprefix tailTrace_147381
  have hstable : (prefixWord ++ tailWord_147381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147381).length < 2 ^ (prefixWord ++ tailWord_147381).sum := by decide
  have hdescent : baseEnd_147381 < baseStart_147381 := by decide
  rcases family_descends (prefixWord ++ tailWord_147381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147401 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 3, 6, 2]
def baseStart_147401 : Nat := 118140960795 + 147401 * 2 ^ 59
def prefixEnd_147401 : Nat := 4983230072969 + 3 ^ 40 * 147401 * 2
def baseEnd_147401 : Nat := 75687561953483026609621

theorem tailTrace_147401 : CollatzResearch.WordTrace tailWord_147401 prefixEnd_147401 75687561953483026609621 := by
  unfold tailWord_147401
  simp only [CollatzResearch.WordTrace]
  refine ⟨5376156138998825931698057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3584104092665883954465371 5376156138998825931698057)
  ·
    refine ⟨4032117104249119448773543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5376156138998825931698057 4032117104249119448773543)
    ·
      refine ⟨6048175656373679173160315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4032117104249119448773543 6048175656373679173160315)
      ·
        refine ⟨9072263484560518759740473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6048175656373679173160315 9072263484560518759740473)
        ·
          refine ⟨6804197613420389069805355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9072263484560518759740473 6804197613420389069805355)
          ·
            refine ⟨10206296420130583604708033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804197613420389069805355 10206296420130583604708033)
            ·
              refine ⟨7654722315097937703531025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10206296420130583604708033 7654722315097937703531025)
              ·
                refine ⟨5741041736323453277648269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7654722315097937703531025 5741041736323453277648269)
                ·
                  refine ⟨2152890651121294979118101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5741041736323453277648269 2152890651121294979118101)
                  ·
                    refine ⟨100916749271310702146161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2152890651121294979118101 100916749271310702146161)
                    ·
                      refine ⟨75687561953483026609621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 100916749271310702146161 75687561953483026609621)
                      ·
                        rfl

theorem cell23_147401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 6, 2].length) (baseStart_147401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147401 prefixEnd_147401 := by exact prefixLift 147401
  have htrace : WordTrace (prefixWord ++ tailWord_147401) baseStart_147401 baseEnd_147401 := by
    simpa [prefixWord, tailWord_147401, baseEnd_147401] using wordTrace_append hprefix tailTrace_147401
  have hstable : (prefixWord ++ tailWord_147401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147401).length < 2 ^ (prefixWord ++ tailWord_147401).sum := by decide
  have hdescent : baseEnd_147401 < baseStart_147401 := by decide
  rcases family_descends (prefixWord ++ tailWord_147401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147438 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_147438 : Nat := 118140960795 + 147438 * 2 ^ 59
def prefixEnd_147438 : Nat := 4983230072969 + 3 ^ 40 * 147438 * 2
def baseEnd_147438 : Nat := 75706560737699381846951

theorem tailTrace_147438 : CollatzResearch.WordTrace tailWord_147438 prefixEnd_147438 75706560737699381846951 := by
  unfold tailWord_147438
  simp only [CollatzResearch.WordTrace]
  refine ⟨672188204983097656349371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3585003759909854167196645 672188204983097656349371)
  ·
    refine ⟨1008282307474646484524057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 672188204983097656349371 1008282307474646484524057)
    ·
      refine ⟨756211730605984863393043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1008282307474646484524057 756211730605984863393043)
      ·
        refine ⟨1134317595908977295089565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756211730605984863393043 1134317595908977295089565)
        ·
          refine ⟨425369098465866485658587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1134317595908977295089565 425369098465866485658587)
          ·
            refine ⟨638053647698799728487881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425369098465866485658587 638053647698799728487881)
            ·
              refine ⟨478540235774099796365911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638053647698799728487881 478540235774099796365911)
              ·
                refine ⟨717810353661149694548867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478540235774099796365911 717810353661149694548867)
                ·
                  refine ⟨1076715530491724541823301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717810353661149694548867 1076715530491724541823301)
                  ·
                    refine ⟨201884161967198351591869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076715530491724541823301 201884161967198351591869)
                    ·
                      refine ⟨75706560737699381846951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 201884161967198351591869 75706560737699381846951)
                      ·
                        rfl

theorem cell23_147438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_147438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147438 prefixEnd_147438 := by exact prefixLift 147438
  have htrace : WordTrace (prefixWord ++ tailWord_147438) baseStart_147438 baseEnd_147438 := by
    simpa [prefixWord, tailWord_147438, baseEnd_147438] using wordTrace_append hprefix tailTrace_147438
  have hstable : (prefixWord ++ tailWord_147438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147438).length < 2 ^ (prefixWord ++ tailWord_147438).sum := by decide
  have hdescent : baseEnd_147438 < baseStart_147438 := by decide
  rcases family_descends (prefixWord ++ tailWord_147438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147505 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 1, 5]
def baseStart_147505 : Nat := 118140960795 + 147505 * 2 ^ 59
def prefixEnd_147505 : Nat := 4983230072969 + 3 ^ 40 * 147505 * 2
def baseEnd_147505 : Nat := 25246987980516873236381

theorem tailTrace_147505 : CollatzResearch.WordTrace tailWord_147505 prefixEnd_147505 25246987980516873236381 := by
  unfold tailWord_147505
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379949330622051693483969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3586632887081367795655979 5379949330622051693483969)
  ·
    refine ⟨4034961997966538770112977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5379949330622051693483969 4034961997966538770112977)
    ·
      refine ⟨3026221498474904077584733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4034961997966538770112977 3026221498474904077584733)
      ·
        refine ⟨1134833061928089029094275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3026221498474904077584733 1134833061928089029094275)
        ·
          refine ⟨1702249592892133543641413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134833061928089029094275 1702249592892133543641413)
          ·
            refine ⟨319171798667275039432765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1702249592892133543641413 319171798667275039432765)
            ·
              refine ⟨119689424500228139787287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319171798667275039432765 119689424500228139787287)
              ·
                refine ⟨179534136750342209680931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119689424500228139787287 179534136750342209680931)
                ·
                  refine ⟨269301205125513314521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179534136750342209680931 269301205125513314521397)
                  ·
                    refine ⟨25246987980516873236381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 269301205125513314521397 25246987980516873236381)
                    ·
                      rfl

theorem cell23_147505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_147505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147505 prefixEnd_147505 := by exact prefixLift 147505
  have htrace : WordTrace (prefixWord ++ tailWord_147505) baseStart_147505 baseEnd_147505 := by
    simpa [prefixWord, tailWord_147505, baseEnd_147505] using wordTrace_append hprefix tailTrace_147505
  have hstable : (prefixWord ++ tailWord_147505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147505).length < 2 ^ (prefixWord ++ tailWord_147505).sum := by decide
  have hdescent : baseEnd_147505 < baseStart_147505 := by decide
  rcases family_descends (prefixWord ++ tailWord_147505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
